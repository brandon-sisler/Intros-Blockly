<script lang="ts">
	import { onMount } from 'svelte';
    import SpaTeXt from 'spatext';
    import CodeMirror from "svelte-codemirror-editor"
    import { xml } from "@codemirror/lang-xml";
    import type Blockly from '../lib/blockly';
    import BlocklyComponent from '../lib/Blockly.svelte';
    import toolbox from '../lib/blockly/toolbox';
    import SpatextGenerator from '../lib/blockly/generators/Spatext'
    import CoqGenerator from '../lib/blockly/generators/Coq'
    let workspace : Blockly.WorkspaceSvg;
	onMount(async () => {
        workspace.addChangeListener(()=>workspace=workspace);
	});
    let stx = "<spatext/>"
    $: if (workspace) {
        stx = `<spatext>\n${SpatextGenerator.workspaceToCode(workspace)}\n</spatext>`
    }
</script>

<BlocklyComponent height="30em" width="100%" {toolbox} bind:workspace/>

{#if workspace}
<div class="flex-container">
    <div class="column"><CodeMirror value={stx} lang={xml()} readonly styles={{"&":{border:"1px solid #aaa"}}}/></div>
    <div class="column"><SpaTeXt {stx}/></div>
</div>
<CodeMirror value={CoqGenerator.workspaceToCode(workspace)} lang={xml()} readonly styles={{"&":{border:"1px solid #aaa"}}}/>
{/if}

<style>
    .flex-container{
        width: 100%;
        min-height: 300px;
        margin: 0 auto;
        display: -webkit-flex; /* Safari */		
        display: flex; /* Standard syntax */
    }
    .flex-container .column{
        width: 50%;
        padding: 10px;
        -webkit-flex: 1; /* Safari */
        -ms-flex: 1; /* IE 10 */
        flex: 1; /* Standard syntax */
    }
</style>