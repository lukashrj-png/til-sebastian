import os
import re
import time
import threading
import requests
import tempfile
import tkinter as tk
from tkinter import filedialog, scrolledtext
from urllib.parse import urljoin, urlparse, unquote
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from webdriver_manager.chrome import ChromeDriverManager
from PIL import Image

# -------------------------------------------------
# Konstanter
# -------------------------------------------------
FILE_EXTENSIONS = [
    ".pdf", ".jpg", ".jpeg", ".png", ".svg",
    ".docx", ".xlsx", ".gif", ".webp", ".xls",
    ".mp4"
]

IMAGE_EXTENSIONS = [".jpg", ".jpeg", ".png", ".svg", ".gif", ".webp"]

BLACKLISTED_FILES = ["logo_dark_en.svg", "1.gif", "logo_light_en.svg"]

BLACKLISTED_URL_PATHS = ["/page", "/filer", "/file"]

ROOT_FOLDER = ""
downloaded_files = set()
downloaded_lock = threading.Lock()
image_sizes = {}  # Dict til at tracke billedstørrelser: {filename: {'path': path, 'pixel_area': area, 'dimensions': (w, h)}}
image_lock = threading.Lock()  # Lock til thread-safe image tracking
crawl_thread = None
pause_flag = threading.Event()
stop_flag = threading.Event()
SPECIAL_FOLDER = "CD kalender eller nyheder"

# Nye indstillinger for hastighed
MAX_DOWNLOAD_WORKERS = 10  # Antal samtidige downloads
MAX_CRAWL_WORKERS = 3      # Antal samtidige sider at crawle
SESSION = requests.Session()  # Genbruger connections

# -------------------------------------------------
# GUI
# -------------------------------------------------
root = tk.Tk()
root.title("Webcrawler 2.0.7 lavet af Lukas :D")

tk.Label(root, text="Indsæt URL:").pack(pady=(10, 0))
url_entry = tk.Entry(root, width=60)
url_entry.pack(pady=5)

mappe_var = tk.StringVar()
tk.Button(root, text="Vælg mappe", command=lambda: vælg_mappe()).pack(pady=5)
tk.Label(root, textvariable=mappe_var).pack()

# Hastigheds indstillinger
speed_frame = tk.Frame(root)
speed_frame.pack(pady=5)
tk.Label(speed_frame, text="Hvor mange tråde?:").pack(side=tk.LEFT)
download_workers_var = tk.IntVar(value=10)
tk.Spinbox(speed_frame, from_=1, to=20, textvariable=download_workers_var, width=5).pack(side=tk.LEFT, padx=5)

tk.Button(root, text="Start download", command=lambda: start_download()).pack(pady=10)
tk.Button(root, text="     ⏸ Pause    ", command=lambda: pause_download()).pack(pady=5)
tk.Button(root, text=" ▶ Genoptag ", command=lambda: resume_download()).pack(pady=5)
tk.Button(root, text="      ⏹ Stop     ", command=lambda: stop_download()).pack(pady=5)

tk.Label(root, text="Terminal-output:").pack()
terminal = scrolledtext.ScrolledText(root, width=80, height=20)
terminal.pack(pady=5)

# Stats
stats_var = tk.StringVar(value="Filer downloadet: 0 | Hastighed: 0 filer/s")
tk.Label(root, textvariable=stats_var, font=("Arial", 10)).pack(pady=5)

# Loading animation
loading_var = tk.StringVar()
loading_label = tk.Label(root, textvariable=loading_var, font=("Arial", 12))
loading_label.pack(pady=5)
spinner_running = False

download_stats = {"count": 0, "start_time": None}

# -------------------------------------------------
# Logging
# -------------------------------------------------
def log(message: str):
    terminal.insert(tk.END, message + "\n")
    terminal.see(tk.END)
    terminal.update()

def log_to_file(folder: str, message: str):
    log_path = os.path.join(folder, "fejl_log.txt")
    with open(log_path, "a", encoding="utf-8") as f:
        f.write(message + "\n")

def update_stats():
    if download_stats["start_time"]:
        elapsed = time.time() - download_stats["start_time"]
        rate = download_stats["count"] / elapsed if elapsed > 0 else 0
        stats_var.set(f"Filer downloadet: {download_stats['count']} | Hastighed: {rate:.1f} filer/s")

# -------------------------------------------------
# Fil- og stihåndtering
# -------------------------------------------------
def clean_url_for_folder(url: str) -> str:
    parsed = urlparse(url)
    folder_name = parsed.netloc + parsed.path.strip("/").replace("/", "_")
    return folder_name or parsed.netloc

def safe_filename(name: str) -> str:
    name = name.replace(' ', '_')
    name = re.sub(r'[<>:"/\\|?*\x00-\x1F]', '_', name)
    return name

def sanitize_path(path: str, root_folder: str) -> str:
    parts = path.strip("/").split("/")
    sanitized_parts = [safe_filename(p)[:50] for p in parts if p]
    return os.path.join(root_folder, *sanitized_parts)

def strip_query_fragment(url: str) -> str:
    parsed = urlparse(url)
    return parsed._replace(query="", fragment="").geturl()

def get_top_level_folder(path: str, root: str) -> str:
    rel_path = os.path.relpath(path, root)
    first_part = rel_path.split(os.sep)[0]
    return os.path.join(root, first_part) if first_part != "." else root

# -------------------------------------------------
# Funktion til at finde baggrundsbilleder i CSS
# -------------------------------------------------
def extract_background_images(driver):
    """Finder alle baggrundsbilleder fra CSS styles"""
    bg_images = set()
    
    try:
        script = """
        let images = [];
        let elements = document.querySelectorAll('*');
        elements.forEach(el => {
            let style = window.getComputedStyle(el);
            let bgImage = style.backgroundImage;
            if (bgImage && bgImage !== 'none') {
                let match = bgImage.match(/url\\(['"]?([^'"\\)]+)['"]?\\)/);
                if (match) {
                    images.push(match[1]);
                }
            }
        });
        return images;
        """
        images = driver.execute_script(script)
        bg_images.update(images)
        
    except Exception as e:
        log(f" Fejl ved udtrækning af baggrundsbilleder: {e}")
    
    return bg_images

# -------------------------------------------------
# Funktion til at finde lazy-loaded billeder
# -------------------------------------------------
def extract_lazy_images(driver):
    """Finder lazy-loaded billeder (data-src, data-lazy-src, etc.)"""
    lazy_images = set()
    
    try:
        attrs = ['data-src', 'data-lazy-src', 'data-original', 'data-srcset']
        for attr in attrs:
            elements = driver.find_elements(By.XPATH, f"//*[@{attr}]")
            for el in elements:
                src = el.get_attribute(attr)
                if src:
                    lazy_images.add(src)
    except Exception as e:
        log(f" Fejl ved udtrækning af lazy-loaded billeder: {e}")
    
    return lazy_images

# -------------------------------------------------
# OPTIMERET Downloadfunktion
# -------------------------------------------------
def download_file(file_url: str, folder: str, max_retries: int = 2, timeout: int = 10):
    global downloaded_files

    file_url = strip_query_fragment(file_url)
    parsed_path = urlparse(file_url).path
    raw_name = os.path.basename(parsed_path)
    file_name = safe_filename(unquote(raw_name))

    if not file_name or file_name == "":
        file_name = f"image_{abs(hash(file_url))}"

    # Check om filen er blacklisted
    if file_name.lower() in [f.lower() for f in BLACKLISTED_FILES]:
        log(f"⏭ Springer over blacklisted fil: {file_name}")
        return

    # Check hvis allerede downloadet (thread-safe)
    with downloaded_lock:
        if file_name in downloaded_files:
            return
        downloaded_files.add(file_name)

    for attempt in range(1, max_retries + 1):
        try:
            # Brug HEAD request for at få metadata hurtigere
            head = SESSION.head(file_url, allow_redirects=True, timeout=timeout)
            ctype = head.headers.get("Content-Type", "").lower()
            disp = head.headers.get("Content-Disposition", "")

            cd_match = re.search(r'filename="?([^"]+)"?', disp)
            if cd_match:
                file_name = safe_filename(unquote(cd_match.group(1)))

            if not any(file_name.lower().endswith(ext) for ext in FILE_EXTENSIONS):
                if "pdf" in ctype:
                    file_name += ".pdf"
                elif "msword" in ctype or "wordprocessingml" in ctype:
                    file_name += ".docx"
                elif "excel" in ctype or "spreadsheetml" in ctype:
                    file_name += ".xlsx"
                elif "jpeg" in ctype or "jpg" in ctype:
                    file_name += ".jpg"
                elif "png" in ctype:
                    file_name += ".png"
                elif "webp" in ctype:
                    file_name += ".webp"
                elif "svg" in ctype:
                    file_name += ".svg"
                elif "gif" in ctype:
                    file_name += ".gif"

            doc_extensions = [".pdf", ".docx", ".xlsx", ".xls"]
            target_folder = get_top_level_folder(folder, ROOT_FOLDER)
            
            if any(file_name.lower().endswith(ext) for ext in doc_extensions):
                target_folder = os.path.join(target_folder, "dokumenter")

            os.makedirs(target_folder, exist_ok=True)
            file_path = os.path.join(target_folder, file_name)

            # Stream download for bedre performance
            response = SESSION.get(file_url, timeout=timeout, stream=True)
            response.raise_for_status()

            with open(file_path, "wb") as f:
                for chunk in response.iter_content(chunk_size=8192):
                    f.write(chunk)

            download_stats["count"] += 1
            update_stats()
            log(f" Hentet: {file_name}")
            return

        except Exception as e:
            if attempt < max_retries:
                time.sleep(1)
            else:
                log(f" Fejl: {file_name}")
                log_to_file(ROOT_FOLDER, f"Fejl ved {file_url}: {e}")

# -------------------------------------------------
# Download billeder via Selenium for fuld opløsning
# -------------------------------------------------
def download_image_via_selenium(driver, image_url: str, folder: str):
    """
    Downloader billeder via Selenium for at få fuld browser-opløsning.
    Sammenligner med eksisterende billeder og beholder kun det største.
    """
    global image_sizes

    try:
        # Strip query/fragment fra URL
        image_url = strip_query_fragment(image_url)
        parsed_path = urlparse(image_url).path
        raw_name = os.path.basename(parsed_path)
        file_name = safe_filename(unquote(raw_name))

        if not file_name or file_name == "":
            file_name = f"image_{abs(hash(image_url))}"

        # Tilføj extension hvis mangler
        if not any(file_name.lower().endswith(ext) for ext in IMAGE_EXTENSIONS):
            file_name += ".jpg"

        # Check om filen er blacklisted
        if file_name.lower() in [f.lower() for f in BLACKLISTED_FILES]:
            log(f"Springer over blacklisted fil: {file_name}")
            return

        # Skip SVG filer - PIL kan ikke håndtere dem
        if file_name.lower().endswith('.svg'):
            log(f"Springer over SVG (downloader via requests): {file_name}")
            download_file(image_url, folder)
            return

        # Check om vi allerede har et større billede
        with image_lock:
            if file_name in image_sizes:
                existing_info = image_sizes[file_name]
                existing_area = existing_info['pixel_area']
                existing_dims = existing_info['dimensions']
            else:
                existing_info = None
                existing_area = 0
                existing_dims = None

        # Download med Selenium's cookies og headers (som om det var browseren)
        target_folder = get_top_level_folder(folder, ROOT_FOLDER)
        os.makedirs(target_folder, exist_ok=True)

        temp_path = os.path.join(target_folder, f"_temp_{file_name}")
        file_path = os.path.join(target_folder, file_name)

        # Hent cookies fra Selenium driver
        cookies = driver.get_cookies()
        session_cookies = {cookie['name']: cookie['value'] for cookie in cookies}

        # Download med browser headers
        headers = {
            'User-Agent': driver.execute_script("return navigator.userAgent;"),
            'Accept': 'image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8',
            'Accept-Language': 'da-DK,da;q=0.9',
            'Referer': driver.current_url,
            'Accept-Encoding': 'gzip, deflate, br',
        }

        response = SESSION.get(image_url, headers=headers, cookies=session_cookies, timeout=10, stream=True)
        response.raise_for_status()

        # Skriv til temp fil
        with open(temp_path, 'wb') as f:
            for chunk in response.iter_content(chunk_size=8192):
                f.write(chunk)

        # Åbn med PIL for at få dimensioner
        try:
            img = Image.open(temp_path)
            width, height = img.size
            pixel_area = width * height

            # Detekter faktisk format
            actual_format = img.format.lower() if img.format else None

            # Map PIL format til filendelse
            format_to_ext = {
                'jpeg': '.jpg',
                'jpg': '.jpg',
                'png': '.png',
                'webp': '.webp',
                'gif': '.gif',
                'bmp': '.bmp',
                'tiff': '.tif'
            }

            # Tjek om filendelse matcher faktisk format
            if actual_format and actual_format in format_to_ext:
                correct_ext = format_to_ext[actual_format]
                current_ext = os.path.splitext(file_name)[1].lower()

                # Hvis forkert endelse: ret det
                if current_ext != correct_ext:
                    old_file_name = file_name
                    file_name = os.path.splitext(file_name)[0] + correct_ext

                    # Opdater også temp_path og file_path med nye filnavn
                    old_temp_path = temp_path
                    temp_path = os.path.join(target_folder, f"_temp_{file_name}")
                    file_path = os.path.join(target_folder, file_name)

                    # Omdøb temp filen
                    os.rename(old_temp_path, temp_path)

                    log(f" Retter filtype: {old_file_name} → {file_name} (faktisk format: {actual_format.upper()})")

            img.close()
        except Exception as e:
            log(f" Kunne ikke åbne billede med PIL: {file_name} - {e}")
            if os.path.exists(temp_path):
                os.remove(temp_path)
            return

        # Sammenlign med eksisterende
        if pixel_area > existing_area:
            # Dette billede er større - slet det gamle og gem det nye
            with image_lock:
                if existing_info and os.path.exists(existing_info['path']):
                    try:
                        os.remove(existing_info['path'])
                        log(f" Slettet mindre version af {file_name}")
                    except Exception as e:
                        log(f" Kunne ikke slette gammel fil: {e}")

                # Flyt temp til final destination
                if os.path.exists(file_path):
                    os.remove(file_path)
                os.rename(temp_path, file_path)

                # Opdater image_sizes
                image_sizes[file_name] = {
                    'path': file_path,
                    'pixel_area': pixel_area,
                    'dimensions': (width, height)
                }

            download_stats["count"] += 1
            update_stats()
            log(f"Hentet via Selenium: {file_name} ({width}×{height} px)")
        else:
            # Det eksisterende billede er større
            if os.path.exists(temp_path):
                os.remove(temp_path)
            log(f"Springer over mindre billede: {file_name} ({width}×{height} px < {existing_dims[0]}×{existing_dims[1]} px)")

    except Exception as e:
        log(f"Selenium download fejl for {file_name}: {e}")
        # Fjern temp fil hvis den findes
        try:
            if 'temp_path' in locals() and os.path.exists(temp_path):
                os.remove(temp_path)
        except:
            pass

# -------------------------------------------------
# Selenium-driver med optimering
# -------------------------------------------------
def init_driver(headless=True):
    options = Options()
    if headless:
        options.add_argument("--headless=new")
    options.add_argument("--disable-gpu")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--log-level=3")
    # Performance optimeringer
    options.add_argument("--disable-extensions")
    options.add_argument("--disable-images")  # Load ikke billeder i browser (vi downloader dem separat)
    options.add_experimental_option("prefs", {
        "profile.managed_default_content_settings.images": 2  # Bloker billeder
    })
    service = Service(ChromeDriverManager().install())
    driver = webdriver.Chrome(service=service, options=options)
    return driver

# -------------------------------------------------
# OPTIMERET crawler med parallel downloads
# -------------------------------------------------
def crawl_and_download(base_url: str, save_folder: str, scroll_pause=0.5, max_scrolls=15):
    global ROOT_FOLDER, download_stats
    ROOT_FOLDER = os.path.join(save_folder, clean_url_for_folder(base_url))
    os.makedirs(ROOT_FOLDER, exist_ok=True)
    
    download_stats["start_time"] = time.time()
    download_stats["count"] = 0

    domain = urlparse(base_url).netloc
    visited = set()
    queue = deque([base_url])
    driver = init_driver(headless=True)

    found_calendars = []
    download_queue = []

    try:
        # Download executor
        max_workers = download_workers_var.get()
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            while queue:
                while pause_flag.is_set():
                    time.sleep(0.5)
                if stop_flag.is_set():
                    log("⏹ Stop aktiveret. Afslutter crawler.")
                    return found_calendars

                current_url = queue.popleft()
                if current_url in visited:
                    continue
                visited.add(current_url)

                try:
                    driver.get(current_url)
                    time.sleep(0.5)  # Reduceret ventetid
                except Exception as e:
                    log(f"Fejl ved åbning af {current_url}: {e}")
                    continue

                # Hurtigere scroll
                last_height = driver.execute_script("return document.body.scrollHeight")
                scroll_count = 0
                while scroll_count < max_scrolls:
                    driver.execute_script("window.scrollTo(0, document.body.scrollHeight);")
                    time.sleep(scroll_pause)
                    new_height = driver.execute_script("return document.body.scrollHeight")
                    if new_height == last_height:
                        break
                    last_height = new_height
                    scroll_count += 1

                folder_path = sanitize_path(unquote(urlparse(current_url).path), ROOT_FOLDER)
                os.makedirs(folder_path, exist_ok=True)

                # Saml URLs i to separate lister: billeder og andre filer
                image_urls = []
                other_urls = []

                # Background billeder
                bg_images = extract_background_images(driver)
                for bg_url in bg_images:
                    full_bg_url = urljoin(current_url, bg_url)
                    # Check om URL indeholder blacklisted path
                    url_path = urlparse(full_bg_url).path.lower()
                    if any(blacklisted in url_path for blacklisted in BLACKLISTED_URL_PATHS):
                        continue
                    if any(full_bg_url.lower().endswith(ext) for ext in IMAGE_EXTENSIONS):
                        image_urls.append(full_bg_url)

                # Lazy-loaded billeder
                lazy_images = extract_lazy_images(driver)
                for lazy_url in lazy_images:
                    full_lazy_url = urljoin(current_url, lazy_url)
                    # Check om URL indeholder blacklisted path
                    url_path = urlparse(full_lazy_url).path.lower()
                    if any(blacklisted in url_path for blacklisted in BLACKLISTED_URL_PATHS):
                        continue
                    if any(full_lazy_url.lower().endswith(ext) for ext in IMAGE_EXTENSIONS):
                        image_urls.append(full_lazy_url)

                # Almindelige tags
                tags = driver.find_elements(By.XPATH, "//a | //img | //source | //iframe | //picture//source")
                for tag in tags:
                    tag_name = tag.tag_name

                    attrs_to_check = []
                    if tag_name == "a":
                        attrs_to_check = ["href"]
                    elif tag_name in ("img", "source", "iframe"):
                        attrs_to_check = ["src", "srcset", "data-src"]

                    for attr in attrs_to_check:
                        href = tag.get_attribute(attr)
                        if not href:
                            continue

                        if attr == "srcset":
                            urls = [u.strip().split()[0] for u in href.split(",")]
                        else:
                            urls = [href]

                        for url in urls:
                            full_url = urljoin(current_url, url)
                            path = unquote(urlparse(full_url).path).lower()

                            # Check om URL indeholder blacklisted path
                            if any(blacklisted in path for blacklisted in BLACKLISTED_URL_PATHS):
                                continue

                            if "calendar" in full_url or "churchdesk" in full_url or "/b/" in full_url:
                                if full_url not in found_calendars:
                                    found_calendars.append(full_url)
                                    log(f"Fundet kalender: {full_url}")

                            if any(path.endswith(ext) for ext in FILE_EXTENSIONS) or "api2.churchdesk.com/files" in full_url:
                                # Check om det er et billede eller andet
                                if any(path.endswith(ext) for ext in IMAGE_EXTENSIONS):
                                    image_urls.append(full_url)
                                else:
                                    other_urls.append(full_url)
                            elif urlparse(full_url).netloc == domain and full_url not in visited:
                                queue.append(full_url)

                # Download billeder serielt via Selenium for fuld opløsning
                for img_url in image_urls:
                    if stop_flag.is_set():
                        break
                    try:
                        download_image_via_selenium(driver, img_url, folder_path)
                    except Exception as e:
                        log(f"Selenium download fejl: {e}")

                # Download dokumenter parallelt
                futures = [executor.submit(download_file, url, folder_path) for url in other_urls]

                # Vent ikke på at alle er færdige, fortsæt bare med næste side

        return found_calendars

    finally:
        driver.quit()

# -------------------------------------------------
# Widget crawler (let optimeret)
# -------------------------------------------------
def widget_crawler(base_url: str, save_folder: str):
    driver = init_driver(headless=True)

    special_folder_path = os.path.join(ROOT_FOLDER, SPECIAL_FOLDER)
    os.makedirs(special_folder_path, exist_ok=True)

    try:
        log(f"Åbner widget: {base_url}")
        driver.get(base_url)
        time.sleep(2)

        try:
            iframe = WebDriverWait(driver, 10).until(
                EC.presence_of_element_located((By.TAG_NAME, "iframe"))
            )
            iframe_src = iframe.get_attribute("src")
            log(f"Fundet iframe: {iframe_src}")
            driver.get(iframe_src)
            time.sleep(1)
        except Exception:
            log("Ingen iframe fundet, fortsætter på siden.")

        all_event_links = set()
        while True:
            links = [a.get_attribute("href") for a in driver.find_elements(By.TAG_NAME, "a")]
            # Filtrer blacklisted paths
            links = [l for l in links if l and "/b/" in l and not any(blacklisted in urlparse(l).path.lower() for blacklisted in BLACKLISTED_URL_PATHS)]
            all_event_links.update(links)
            log(f"🔎 Fundet {len(all_event_links)} begivenheder indtil nu...")

            try:
                next_button = driver.find_element(By.CSS_SELECTOR, "button[aria-label='Næste side']")
                if next_button.get_attribute("disabled"):
                    break
                driver.execute_script("arguments[0].click();", next_button)
                time.sleep(1)
            except Exception:
                break

        # Download event filer (billeder via Selenium, andre parallelt)
        max_workers = download_workers_var.get()
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            for idx, event in enumerate(all_event_links, start=1):
                try:
                    driver.get(event)
                    WebDriverWait(driver, 5).until(
                        EC.presence_of_all_elements_located((By.TAG_NAME, "a"))
                    )
                    log(f" [{idx}/{len(all_event_links)}] Åbner begivenhed: {event}")

                    links = [a.get_attribute("href") for a in driver.find_elements(By.TAG_NAME, "a")]
                    images = [img.get_attribute("src") for img in driver.find_elements(By.TAG_NAME, "img")]
                    bg_images = extract_background_images(driver)
                    lazy_images = extract_lazy_images(driver)

                    all_links = [l for l in links + images + list(bg_images) + list(lazy_images) if l]

                    # Split i billeder og andre filer
                    image_urls = []
                    other_urls = []

                    for link in all_links:
                        clean_link = link.split("?")[0]
                        if any(clean_link.lower().endswith(ext) for ext in FILE_EXTENSIONS):
                            # Check om det er et billede
                            if any(clean_link.lower().endswith(ext) for ext in IMAGE_EXTENSIONS):
                                image_urls.append(link)
                            else:
                                other_urls.append(link)

                    # Download billeder serielt via Selenium
                    for img_url in image_urls:
                        if stop_flag.is_set():
                            break
                        try:
                            download_image_via_selenium(driver, img_url, special_folder_path)
                        except Exception as e:
                            log(f"Selenium download fejl: {e}")

                    # Download dokumenter parallelt
                    futures = []
                    for url in other_urls:
                        futures.append(executor.submit(download_file, url, special_folder_path))

                except Exception as e:
                    log(f" Fejl ved begivenhed {event}: {e}")

    finally:
        driver.quit()
        log(f"kalender download færdig. Filerne ligger i: {special_folder_path}")

# -------------------------------------------------
# Spinner-animation
# -------------------------------------------------
def animate_spinner():
    global spinner_running
    frames = [
        "   /)/)      (\\(\\\n  (^ ^)      (• •)\n  /づ📂      ⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ 📂     ⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ  📂    ⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ   📂   ⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ    📂  ⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ     📂 ⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (^ ^)\n  /づ      📂⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (^ ^)\n  /づ      📂⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ     📂 ⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ    📂  ⊂  \\",
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ   📂   ⊂  \\", 
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ  📂    ⊂  \\",   
        "   /)/)      (\\(\\\n  (• •)      (• •)\n  /づ 📂     ⊂  \\",  
        "   /)/)      (\\(\\\n  (^ ^)      (• •)\n  /づ📂      ⊂  \\",                  
    ]
    idx = 0
    while spinner_running:
        loading_var.set(f"Henter filer...\n{frames[idx % len(frames)]}")
        idx += 1
        time.sleep(0.15)

# -------------------------------------------------
# GUI funktioner
# -------------------------------------------------
def vælg_mappe():
    folder = filedialog.askdirectory()
    if folder:
        mappe_var.set(folder)
        log(f"📁 Valgt mappe: {folder}")

def start_download():
    url = url_entry.get()
    folder = mappe_var.get()
    if not url:
        log("⚠️ Du skal indsætte en URL.")
        return
    if not folder:
        log("⚠️ Du skal vælge en mappe.")
        return

    log(f" Starter crawler på: {url}")
    log(f" Bruger antal tråde: {download_workers_var.get()}  ")
    pause_flag.clear()
    stop_flag.clear()

    def run_crawler():
        global ROOT_FOLDER, spinner_running
        spinner_running = True
        spinner_thread = threading.Thread(target=animate_spinner, daemon=True)
        spinner_thread.start()
        
        try:
            ROOT_FOLDER = os.path.join(folder, clean_url_for_folder(url))
            os.makedirs(ROOT_FOLDER, exist_ok=True)

            found_calendars = crawl_and_download(url, folder)
            log("Almindelig crawling færdig.")

            if found_calendars:
                log(f"Fundet {len(found_calendars)} kalendere på undersider.")
                for idx, cal in enumerate(found_calendars, 1):
                    log(f"➡️ [{idx}/{len(found_calendars)}] Starter widget-crawler på: {cal}")
                    widget_crawler(cal, folder)
            else:
                log("ℹ Ingen ekstra kalendere fundet på undersider.")

            log("Alle downloads færdige.")
        except Exception as e:
            log(f"Fejl: {e}")
            log_to_file(ROOT_FOLDER, f"Generel fejl: {e}")
        finally:
            spinner_running = False
            loading_var.set("")

    global crawl_thread
    crawl_thread = threading.Thread(target=run_crawler, daemon=True)
    crawl_thread.start()

def pause_download():
    if crawl_thread and crawl_thread.is_alive():
        pause_flag.set()
        log("⏸ Download er sat på pause.")

def resume_download():
    if crawl_thread and crawl_thread.is_alive():
        pause_flag.clear()
        log("▶ Download genoptaget.")

def stop_download():
    if crawl_thread and crawl_thread.is_alive():
        stop_flag.set()
        pause_flag.clear()
        log("⏹ Download stoppet")
    log("Stopper hele programmet...")
    root.destroy()
    os._exit(0)

# -------------------------------------------------
# Start GUI
# -------------------------------------------------
root.mainloop()