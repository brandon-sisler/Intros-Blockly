<script lang="ts">
    import Blockly from './blockly';
    import { createWorkspace } from './blockly';
	import { onMount } from 'svelte';
    export let toolbox : Blockly.utils.toolbox.ToolboxDefinition;
    export let width : string = "800px";
    export let height : string = "600px";
    export let workspace : Blockly.WorkspaceSvg;
    let blocklyContainer : HTMLElement;
    let mounted = false;
	onMount(async () => {
        blocklyContainer.style.height = height
        blocklyContainer.style.width = width
        workspace = createWorkspace(blocklyContainer,{toolbox:toolbox});
        mounted = true;
	});
    $: if (mounted) {
        blocklyContainer.style.height = height
        blocklyContainer.style.width = width
        Blockly.svgResize(workspace);
    }
</script>

<div class="blocklyContainer" bind:this={blocklyContainer}/>

<style scoped>
    .blocklyContainer {
        border: 1px solid #aaa;
    }
</style>