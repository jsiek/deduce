# How to maintain the site 😀

Here you can find anything and everything you need to know about how to keep the site up-to-date and flexible to the ever changing needs of your users.

For your convenience, we've split up this doc into different sections to make it easier to find exactly what you're looking for

- [Updating site content](#updating-site-content)
- [Updating code blocks](#updating-code-blocks)
- [Changing colors](#changing-colors)

## Updating site content

Most of the pages on the site are generated into html from the markdown files found in the `/doc` directory. If you want to update the content for those pages, just update the markdown file and `convert.py` will do the rest for you.

The only three pages that are not automatically generated from the markdown files are

- `index.html` : The home page for the site
- `404.html` : The page that GitHub pages serves on a 404 error
- `pages/sandbox.html` : The live code page

If you want to edit the content for one of these pages, you will have to go in and directly change the html yourself.

## Updating code blocks

Currently, the site displays two kinds of code blocks which we will denote as `deduce` and `non-deduce` code blocks. 
- `deduce` codeblocks are the ones that actually get colored on the site. `convert.py` also generates deduce files for these codeblocks for testing purposes.
- `non-deduce` code blocks are not colored on the site. They are the ones that show up with black text on a light gray background. These code blocks are primarily used for non-deduce code, code output, or intermediary deduce code. 

Code blocks that are found in markdown files can be edited directly in the markdown (again `convert.py` has got your back).

## Changing colors