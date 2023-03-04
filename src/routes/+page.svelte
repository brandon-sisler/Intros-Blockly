<script lang="ts">
    import type Blockly from 'blockly';
    import BlocklyComponent from '../lib/Blockly.svelte';
	import { onMount } from 'svelte';
    import { toolbox } from '../lib/toolbox'
    import { nlOutput, coqOutput } from '../lib/custom.js';
    let workspace : Blockly.WorkspaceSvg;
	onMount(async () => {
        workspace.addChangeListener(()=>workspace=workspace);
	});
</script>

<BlocklyComponent height={320} width={1200} {toolbox} bind:workspace/>

{#if workspace}
<textarea id="blocklyProof" style="height: 320px; width: 600px;" readonly>{nlOutput(workspace)}</textarea>
<textarea id="blocklyCoq" style="height: 320px; width: 600px;" readonly>{coqOutput(workspace)}</textarea>
{/if}