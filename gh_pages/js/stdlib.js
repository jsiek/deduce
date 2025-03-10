colorSchemes = {
    "deduce-dark" : {
        'background': '#202022',
        'foreground': '#fa7188',
        'hover-bg': '#4e3c63',
        'keyword' : '#e9cc60',
        'operator' : '#cfd6e3',
        'type': '#b689fe',
        'prim': '#f18bea',
        'comment': '#999999',
        'import': '#b689fe',
        'union': '#b689fe',
        'function': '#67bef9',
        'theorem': '#67bef9',
        'constructor': '#67bef9',
    },
    "deduce" : {
        'background': '#fefef8',
        'foreground': '#2e2d31',
        'hover-bg': 'pink',
        'keyword' : '#d85311',
        'operator' : '#2e2d31',
        'type': '#0f95af',
        'prim': '#9329ab',
        'comment': '#666666',
        'import': '#0f95af',
        'union': '#0f95af',
        'function': '#c553e9',
        'theorem': '#c553e9',
        'constructor': '#c553e9',
    },
    "vs-dark"  : {
        'background': '#1e1e1e',
        'foreground': '#d4d4d4',
        'hover-bg': '#4e3c63',
        'keyword' : '#c586c0',
        'operator' : '#d4d4d4',
        'type': '#569cd6',
        'prim': '#b5ce9f',
        'comment': '#da9955',
        'import': '#569cd6',
        'union': '#569cd6',
        'function': '#9cdcf3',
        'theorem': '#9cdcf3',
        'constructor': '#9cdcf3',
    },
    "vs" : {
        'background': '#fff',
        'foreground': '#000',
        'hover-bg': 'pink',
        'keyword' : '#0000ff',
        'operator' : '#000',
        'type': '#0000ff',
        'prim': '#098658',
        'comment': '#008000',
        'import': '#0000ff',
        'union': '#0000ff',
        'function': '#0000ff',
        'theorem': '#0000ff',
        'constructor': '#0000ff',
    },
    "hc-black" : {
        'background': '#000',
        'foreground': '#fff',
        'hover-bg': 'black',
        'keyword' : '#c586c0',
        'operator' : '#d4d4d4',
        'type': '#569cd6',
        'prim': '#b5ce9f',
        'comment': '#da9955',
        'import': '#569cd6',
        'union': '#569cd6',
        'function': '#9cdcf3',
        'theorem': '#9cdcf3',
        'constructor': '#9cdcf3',
    },
}

function setTheme(theme) {
    themeSelect.value = theme
    setCookie('theme', theme, 1)
    for (const color in colorSchemes[theme]) {
        document.documentElement.style.setProperty(`--${color}`, colorSchemes[theme][color]);
    }
}

function setDetailsCookie(details) {
    id = details.target.id;
    setCookie(id, document.getElementById(id).open)
}

function setDetailsState(details) {
    state = getCookie(details.id) == '' ? true : getCookie(details.id) === 'true'
    details.open = state
}

function setCookie(cname, cvalue, exdays) {
    const d = new Date();
    d.setTime(d.getTime() + (exdays * 24 * 60 * 60 * 1000));
    let expires = "expires=" + d.toUTCString();
    document.cookie = cname + "=" + cvalue + ";" + expires + ";path=/";
}
function getCookie(cname) {
    let name = cname + "=";
    let decodedCookie = decodeURIComponent(document.cookie);
    let ca = decodedCookie.split(';');
    for (let i = 0; i < ca.length; i++) {
        let c = ca[i];
        while (c.charAt(0) == ' ') {
            c = c.substring(1);
        }
        if (c.indexOf(name) == 0) {
            return c.substring(name.length, c.length);
        }
    }
    return "";
}

const thmDetails = document.getElementById('thm-details')
const pfDetails = document.getElementById('pf-details')
const themeSelect = document.getElementById('theme')

window.onload = () => {
    setTheme(getCookie('theme') == '' ? themeSelect.value : getCookie('theme'))
    setDetailsState(thmDetails)
    setDetailsState(pfDetails)
    themeSelect.oninput = () => setTheme(themeSelect.value)
    pfDetails.ontoggle = thmDetails.ontoggle = (e) => setDetailsCookie(e)
}

window.onresize = () => {
    document.documentElement.style.setProperty('--sidebar-w',
        window.innerWidth > 991.98 ? '225px' : window.innerWidth > 767.98 ? '180px' : '45px')
    document.querySelector('.sidebar-content').classList.add('hidden')
}

document.getElementById('nav-toggle').onclick = () => {
    const sbContent = document.querySelector('.sidebar-content')
    sbContent.classList.toggle('hidden')
    if (sbContent.classList.contains('hidden')) {
        document.documentElement.style.setProperty('--sidebar-w', '45px')
    } else {
        document.documentElement.style.setProperty('--sidebar-w', '180px')
    }
}