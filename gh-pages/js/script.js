const burgerToggle = document.getElementById("nav-toggle");
const linkList = document.getElementById("link-list");

burgerToggle.onclick = () => linkList.classList.toggle("hide");