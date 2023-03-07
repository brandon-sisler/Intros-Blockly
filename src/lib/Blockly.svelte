<script lang="ts">
    import Blockly from './blockly';
    import { createWorkspace } from './blockly';
	import { onMount } from 'svelte';
    export let toolbox : Blockly.utils.toolbox.ToolboxDefinition;
    export let width : number = 800;
    export let height : number = 600;
    export let workspace : Blockly.WorkspaceSvg;
    let blocklyContainer : HTMLElement;
    let mounted = false;
	onMount(async () => {
        blocklyContainer.style.height = `${height}px`
        blocklyContainer.style.width = `${width}px`
        workspace = createWorkspace(blocklyContainer,{toolbox:toolbox});
        mounted = true;
	});
    $: if (mounted) {
        blocklyContainer.style.height = `${height}px`
        blocklyContainer.style.width = `${width}px`
        Blockly.svgResize(workspace);
    }
</script>

<div class="blocklyContainer" bind:this={blocklyContainer}/>

<style scoped>
    .blocklyContainer {
        border: 1px solid #aaa;
    }
</style>