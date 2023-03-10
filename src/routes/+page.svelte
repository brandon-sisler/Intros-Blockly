<script lang="ts">
    import type Blockly from '../lib/blockly';
    import BlocklyComponent from '../lib/Blockly.svelte';
	import { onMount } from 'svelte';
    import { toolbox } from '../lib/blockly/toolbox';
    import SpatextGenerator from '../lib/blockly/generators/Spatext'
    import CoqGenerator from '../lib/blockly/generators/Coq'
    let workspace : Blockly.WorkspaceSvg;
	onMount(async () => {
        workspace.addChangeListener(()=>workspace=workspace);
	});
</script>

<BlocklyComponent height={320} width={1200} {toolbox} bind:workspace/>

{#if workspace}
<textarea id="blocklyProof" style="height: 320px; width: 600px;" readonly>{SpatextGenerator.workspaceToCode(workspace)}</textarea>
<textarea id="blocklyCoq" style="height: 320px; width: 600px;" readonly>{CoqGenerator.workspaceToCode(workspace)}</textarea>
{/if}