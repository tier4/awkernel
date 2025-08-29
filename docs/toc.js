// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded "><a href="index.html"><strong aria-hidden="true">1.</strong> Introduction</a></li><li class="chapter-item expanded "><a href="internal/index.html"><strong aria-hidden="true">2.</strong> Internal</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="internal/synchronization.html"><strong aria-hidden="true">2.1.</strong> Synchronization</a></li><li class="chapter-item expanded "><a href="internal/console.html"><strong aria-hidden="true">2.2.</strong> Console</a></li><li class="chapter-item expanded "><a href="internal/logger.html"><strong aria-hidden="true">2.3.</strong> Logger</a></li><li class="chapter-item expanded "><a href="internal/boot.html"><strong aria-hidden="true">2.4.</strong> Boot</a></li><li class="chapter-item expanded "><a href="internal/arch/index.html"><strong aria-hidden="true">2.5.</strong> Architecture Abstraction</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="internal/arch/delay.html"><strong aria-hidden="true">2.5.1.</strong> Delay</a></li><li class="chapter-item expanded "><a href="internal/arch/cpu.html"><strong aria-hidden="true">2.5.2.</strong> CPU</a></li><li class="chapter-item expanded "><a href="internal/arch/interrupt.html"><strong aria-hidden="true">2.5.3.</strong> Interrupt</a></li><li class="chapter-item expanded "><a href="internal/arch/mapper.html"><strong aria-hidden="true">2.5.4.</strong> Mapper (Virtual Memory Management)</a></li></ol></li><li class="chapter-item expanded "><a href="internal/page_table.html"><strong aria-hidden="true">2.6.</strong> Page Table</a></li><li class="chapter-item expanded "><a href="internal/context_switch.html"><strong aria-hidden="true">2.7.</strong> Context Switch</a></li><li class="chapter-item expanded "><a href="internal/interrupt_controller.html"><strong aria-hidden="true">2.8.</strong> Interrupt Controller</a></li><li class="chapter-item expanded "><a href="internal/memory_allocator.html"><strong aria-hidden="true">2.9.</strong> Memory Allocator</a></li><li class="chapter-item expanded "><a href="internal/scheduler.html"><strong aria-hidden="true">2.10.</strong> Scheduler</a></li><li class="chapter-item expanded "><a href="internal/PCIe.html"><strong aria-hidden="true">2.11.</strong> PCIe</a></li></ol></li><li class="chapter-item expanded "><a href="LICENSE.html"><strong aria-hidden="true">3.</strong> License</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="license/awkernel.html"><strong aria-hidden="true">3.1.</strong> Awkernel</a></li><li class="chapter-item expanded "><a href="license/openbsd.html"><strong aria-hidden="true">3.2.</strong> OpenBSD</a></li><li class="chapter-item expanded "><a href="license/smoltcp.html"><strong aria-hidden="true">3.3.</strong> smoltcp</a></li><li class="chapter-item expanded "><a href="license/futures.html"><strong aria-hidden="true">3.4.</strong> Futures</a></li><li class="chapter-item expanded "><a href="license/ixgbe.html"><strong aria-hidden="true">3.5.</strong> Ixgbe device driver</a></li><li class="chapter-item expanded "><a href="license/igb.html"><strong aria-hidden="true">3.6.</strong> Igb device driver</a></li><li class="chapter-item expanded "><a href="license/genet.html"><strong aria-hidden="true">3.7.</strong> Genet device driver</a></li></ol></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split("#")[0].split("?")[0];
        if (current_page.endsWith("/")) {
            current_page += "index.html";
        }
        var links = Array.prototype.slice.call(this.querySelectorAll("a"));
        var l = links.length;
        for (var i = 0; i < l; ++i) {
            var link = links[i];
            var href = link.getAttribute("href");
            if (href && !href.startsWith("#") && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The "index" page is supposed to alias the first chapter in the book.
            if (link.href === current_page || (i === 0 && path_to_root === "" && current_page.endsWith("/index.html"))) {
                link.classList.add("active");
                var parent = link.parentElement;
                if (parent && parent.classList.contains("chapter-item")) {
                    parent.classList.add("expanded");
                }
                while (parent) {
                    if (parent.tagName === "LI" && parent.previousElementSibling) {
                        if (parent.previousElementSibling.classList.contains("chapter-item")) {
                            parent.previousElementSibling.classList.add("expanded");
                        }
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', function(e) {
            if (e.target.tagName === 'A') {
                sessionStorage.setItem('sidebar-scroll', this.scrollTop);
            }
        }, { passive: true });
        var sidebarScrollTop = sessionStorage.getItem('sidebar-scroll');
        sessionStorage.removeItem('sidebar-scroll');
        if (sidebarScrollTop) {
            // preserve sidebar scroll position when navigating via links within sidebar
            this.scrollTop = sidebarScrollTop;
        } else {
            // scroll sidebar to current active section when navigating via "next/previous chapter" buttons
            var activeSection = document.querySelector('#sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        var sidebarAnchorToggles = document.querySelectorAll('#sidebar a.toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(function (el) {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define("mdbook-sidebar-scrollbox", MDBookSidebarScrollbox);
