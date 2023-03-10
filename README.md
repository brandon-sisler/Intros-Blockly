# intros-blockly

Powered by [`create-svelte`](https://github.com/sveltejs/kit/tree/master/packages/create-svelte).

<!-- ## Creating a project

If you're seeing this, you've probably already done this step. Congrats!

```bash
# create a new project in the current directory
npm create svelte@latest

# create a new project in my-app
npm create svelte@latest my-app
``` -->

## Developing

Once you've created a project and installed/dupated dependencies with 

```bash
npm install
```

start a development server:

```bash
npm run dev -- --host

# or start the server and open the app in a new browser tab
npm run dev -- --host --open
```

## Building

To create a production version of your app:

```bash
npm install # to ensure dependencies are updated
npm run build
```

You can preview the production build with `npm run preview`.

> To deploy your app, you may need to install an [adapter](https://kit.svelte.dev/docs/adapters) for your target environment.

## Deploying

The app is deployed as a client-side "single page app" hosted by GitHub pages, by committing
files to the `/docs` directory. To update `/docs` with the latest build:

```
npm run build # if necessary
rm -rf docs/*
touch docs/.nojekyll # so GitHub Pages knows the site is static, not https://jekyllrb.com/
cp -r build/* docs/
```

Then add/commit/push your repository to update the public app. (You can update your Git
repo without updating the public app as long as you don't change the contents of `/docs`.)
