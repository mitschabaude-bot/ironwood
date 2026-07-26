import Clean.Halo2.TopLevel
import Zcash.Circuits.Action.RealBases
import Zcash.Circuits.Action.TopLevelSynthesisLaws

/-!
# The deployed Orchard Action as a closed top-level circuit
-/

namespace Zcash.Circuits.Action

open Halo2
open Specs.Sinsemilla (Generators)
open Circuit

set_option maxHeartbeats 20000

theorem initialGeneratorTableIdx_mem
    (G : Generators) (B : Bases) (cfg : Config) (i : RegionIndex) :
    Operation.loadTable cfg.sinsemilla1.generatorTable.tableIdx
        ((List.range (2 ^ Specs.K)).map (Nat.cast : ℕ → Fp)) ∈
      (mainPost G B cfg ()).operations i := by
  simp only [mainPost, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil]
  apply List.mem_append_left
  rw [FormalCircuit.call_operations]
  simp only [baseCircuit, main, CircuitPreIronwood.synthesize, synthesizeBase,
    Circuit.operations_bind, Circuit.operations_pure, List.append_nil]
  apply List.mem_append_left
  simp only [synthWitness, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil]
  apply List.mem_append_left
  rw [Sinsemilla.load_operations]
  simp

private theorem constraints_initialGeneratorLoad
    (G : Generators) (B : Bases) (cfg : Config)
    (i : RegionIndex) (env : Placed Environment Fp)
    (h : Constraints env.place env.env
      ((mainPost G B cfg ()).operations i) i) :
    Constraints env.place env.env
      ((Sinsemilla.load G cfg.sinsemilla1.generatorTable).operations i) i := by
  simp only [mainPost, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil] at h
  rw [constraints_append] at h
  have hbase := h.1
  rw [FormalCircuit.call_operations] at hbase
  simp only [baseCircuit, main, CircuitPreIronwood.synthesize, synthesizeBase,
    Circuit.operations_bind, Circuit.operations_pure] at hbase
  rw [constraints_append] at hbase
  have hwitness := hbase.1
  simp only [synthWitness, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil] at hwitness
  rw [constraints_append] at hwitness
  exact hwitness.1

private theorem extendsWitnesses_initialGeneratorLoad
    (G : Generators) (B : Bases) (cfg : Config)
    (i : RegionIndex) (env : Placed ProverEnvironment Fp)
    (h : ExtendsWitnesses env.place env.env
      ((mainPost G B cfg ()).operations i) i) :
    ExtendsWitnesses env.place env.env
      ((Sinsemilla.load G cfg.sinsemilla1.generatorTable).operations i) i := by
  simp only [mainPost, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil] at h
  rw [extendsWitnesses_append] at h
  have hbase := h.1
  rw [FormalCircuit.call_operations] at hbase
  simp only [baseCircuit, main, CircuitPreIronwood.synthesize, synthesizeBase,
    Circuit.operations_bind, Circuit.operations_pure] at hbase
  rw [extendsWitnesses_append] at hbase
  have hwitness := hbase.1
  simp only [synthWitness, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil] at hwitness
  rw [extendsWitnesses_append] at hwitness
  exact hwitness.1

private theorem constraints_generatorLoad_of_extendsWitnesses
    (G : Generators) (cfg : Sinsemilla.GeneratorTableConfig)
    (i : RegionIndex) (env : Placed ProverEnvironment Fp)
    (h : ExtendsWitnesses env.place env.env
      ((Sinsemilla.load G cfg).operations i) i) :
    Constraints env.place env.toEnvironment.env
      ((Sinsemilla.load G cfg).operations i) i := by
  simp only [Sinsemilla.load, circuit_norm] at h ⊢
  exact h

private theorem generatorTableExact_of_constraints
    (G : Generators) (cfg : Sinsemilla.GeneratorTableConfig)
    (i : RegionIndex) (env : Placed Environment Fp)
    (h : Constraints env.place env.env
      ((Sinsemilla.load G cfg).operations i) i) :
    GeneratorTableExact G cfg env.env := by
  simp only [GeneratorTableExact, Sinsemilla.load, circuit_norm] at h ⊢
  exact h

private theorem rangeLoad_constraints_of_generatorLoad
    (G : Generators) (gcfg : Sinsemilla.GeneratorTableConfig)
    (lcfg : LookupRangeCheck.Config 10)
    (htable : lcfg.tableIdx = gcfg.tableIdx)
    (i : RegionIndex) (env : Placed Environment Fp)
    (h : Constraints env.place env.env
      ((Sinsemilla.load G gcfg).operations i) i) :
    Constraints env.place env.env
      ((LookupRangeCheck.load 10 lcfg).operations i) i := by
  simp only [Sinsemilla.load, LookupRangeCheck.load, circuit_norm] at h ⊢
  rw [htable]
  exact ⟨h.1, h.2.1⟩

private theorem configuredTableSharing (G : Generators) :
    let cfg := (configure G {}).1
    cfg.sinsemilla2.generatorTable = cfg.sinsemilla1.generatorTable ∧
    cfg.merkle1.sinsemilla.generatorTable = cfg.sinsemilla1.generatorTable ∧
    cfg.merkle2.sinsemilla.generatorTable = cfg.sinsemilla1.generatorTable ∧
    cfg.lookupConfig.tableIdx = cfg.sinsemilla1.generatorTable.tableIdx := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem configuredLookupSelectorIndices (G : Generators) :
    let cfg := (configure G {}).1
    cfg.lookupConfig.qLookup.index = 2 ∧
      cfg.lookupConfig.qRunning.index = 3 := by
  exact ⟨rfl, rfl⟩

private theorem configured_pureEnvironmentAssumptions
    (G : Generators) (env : Placed Environment Fp) :
    let cfg := (configure G {}).1
    Ecc.MulFixed.FullWidth.EnvAssumptions cfg.eccConfig.mulFixedFull env ∧
    Ecc.MulFixed.Short.EnvAssumptions cfg.eccConfig.mulFixedShort env ∧
    Ecc.MulFixed.BaseFieldElem.InnerEnvAssumptions
      cfg.eccConfig.mulFixedBaseField env ∧
    cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index := by
  simp only [Ecc.MulFixed.FullWidth.EnvAssumptions,
    Ecc.MulFixed.Short.EnvAssumptions,
    Ecc.MulFixed.Short.InnerEnvAssumptions,
    Ecc.MulFixed.BaseFieldElem.InnerEnvAssumptions, circuit_norm]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  obtain ⟨hLookup, hRunning⟩ := configuredLookupSelectorIndices G
  omega

private theorem configured_environmentAssumptions
    (G : Generators) (i : RegionIndex) (env : Placed Environment Fp)
    (hUsable : 2 ^ Specs.K ≤ env.env.usableRows)
    (hload : let cfg := (configure G {}).1
      Constraints env.place env.env
        ((Sinsemilla.load G cfg.sinsemilla1.generatorTable).operations i) i) :
    EnvAssumptions G (configure G {}).1 env := by
  let cfg := (configure G {}).1
  change EnvAssumptions G cfg env
  have hload' : Constraints env.place env.env
      ((Sinsemilla.load G cfg.sinsemilla1.generatorTable).operations i) i := hload
  have hexact :=
    generatorTableExact_of_constraints G cfg.sinsemilla1.generatorTable i env hload'
  have hgenerator := Sinsemilla.load_generatorTableLoaded G
    cfg.sinsemilla1.generatorTable env.place env.env i hUsable hload'
  obtain ⟨hs2, hm1, hm2, hlookup⟩ := configuredTableSharing G
  have hrangeConstraints := rangeLoad_constraints_of_generatorLoad G
    cfg.sinsemilla1.generatorTable cfg.lookupConfig hlookup i env hload'
  have hrange := LookupRangeCheck.load_tableLoaded 10 cfg.lookupConfig
    env.place env.env i (by norm_num) hUsable hrangeConstraints
  obtain ⟨hfull, hshort, hbaseField, hdistinct⟩ :=
    configured_pureEnvironmentAssumptions G env
  simp only [EnvAssumptions]
  refine ⟨hexact, hgenerator, ?_, ?_, ?_, hfull, hshort, ?_, ?_, hrange,
    hdistinct⟩
  · simpa only [hs2] using hgenerator
  · simpa only [hm1] using hgenerator
  · simpa only [hm2] using hgenerator
  · exact ⟨hbaseField, hrange, hdistinct⟩
  · exact ⟨hrange, hdistinct⟩

/-- The real Action synthesis closes its environment contract on the verifier side. -/
private theorem closesEnvironmentSoundness
    (G : Generators) (B : Bases)
    (i : RegionIndex) (env : Placed Environment Fp)
    (hwellFormed : SynthesisWellFormed env.env
      ((mainPost G B (configure G {}).1 ()).operations i))
    (hconstraints : Constraints env.place env.env
      ((mainPost G B (configure G {}).1 ()).operations i) i) :
    EnvAssumptions G (configure G {}).1 env := by
  have hUsable : 2 ^ Specs.K ≤ env.env.usableRows := by
    have hfit := hwellFormed.tablesFit
      (configure G {}).1.sinsemilla1.generatorTable.tableIdx
      ((List.range (2 ^ Specs.K)).map (Nat.cast : ℕ → Fp))
      (initialGeneratorTableIdx_mem G B (configure G {}).1 i)
    simpa only [List.length_map, List.length_range] using hfit
  exact configured_environmentAssumptions G i env hUsable
    (constraints_initialGeneratorLoad G B (configure G {}).1 i env hconstraints)

/-- The same closure, using the honest prover's fixed-table witness extension. -/
private theorem closesEnvironmentCompleteness
    (G : Generators) (B : Bases)
    (i : RegionIndex) (env : Placed ProverEnvironment Fp)
    (hwellFormed : SynthesisWellFormed env.toEnvironment.env
      ((mainPost G B (configure G {}).1 ()).operations i))
    (hwitnesses : ExtendsWitnesses env.place env.env
      ((mainPost G B (configure G {}).1 ()).operations i) i) :
    EnvAssumptions G (configure G {}).1 env.toEnvironment := by
  have hUsable : 2 ^ Specs.K ≤ env.env.usableRows := by
    have hfit := hwellFormed.tablesFit
      (configure G {}).1.sinsemilla1.generatorTable.tableIdx
      ((List.range (2 ^ Specs.K)).map (Nat.cast : ℕ → Fp))
      (initialGeneratorTableIdx_mem G B (configure G {}).1 i)
    simpa only [List.length_map, List.length_range] using hfit
  have hloadWitnesses :=
    extendsWitnesses_initialGeneratorLoad G B (configure G {}).1 i env hwitnesses
  have hload := constraints_generatorLoad_of_extendsWitnesses G
    (configure G {}).1.sinsemilla1.generatorTable i env hloadWitnesses
  exact configured_environmentAssumptions G i env.toEnvironment hUsable hload

private theorem circuit_configure_eq (G : Generators) (B : Bases) :
    (circuit G B).configure = fun _ => configure G :=
  rfl

private theorem circuit_synthesize_eq (G : Generators) (B : Bases) (cfg : Config) :
    (circuit G B).synthesize cfg = mainPost G B cfg :=
  rfl

private theorem circuit_envAssumptions_eq (G : Generators) (B : Bases) (cfg : Config) :
    (circuit G B).EnvAssumptions cfg = EnvAssumptions G cfg :=
  rfl

/--
The proof-carrying Orchard Action circuit at arbitrary certified constants, closed as
a deployable `TopLevelCircuit`: unit public synthesis input, `True` verifier
assumptions, and no unfulfilled environment contract at its boundary.
-/
def topLevelCircuit (G : Generators) (B : Bases) :
    TopLevelCircuit Fp Unit Config unit where
  formalCircuit := circuit G B
  configInput := ()
  assumptions_eq := rfl
  lookupRelevantSelectorActivationsExact :=
    actionCircuit_lookupRelevantSelectorActivationsExact G B
  lookupInputsNoSimpleSelectors :=
    actionCircuit_lookupInputsNoSimpleSelectors G B
  closesEnvironmentSoundness := by
    simp only [circuit_configure_eq, circuit_synthesize_eq,
      circuit_envAssumptions_eq]
    intro i env hwellFormed hconstraints
    exact closesEnvironmentSoundness G B i env hwellFormed hconstraints
  closesEnvironmentCompleteness := by
    simp only [circuit_configure_eq, circuit_synthesize_eq,
      circuit_envAssumptions_eq]
    intro i env hwellFormed hwitnesses
    exact closesEnvironmentCompleteness G B i env hwellFormed hwitnesses

/-- The deployed Orchard Action circuit, instantiated at its real proven constants. -/
def orchardActionTopLevelCircuit :
    TopLevelCircuit Fp Unit Config unit :=
  topLevelCircuit Specs.Sinsemilla.orchardGenerators orchardBases

end Zcash.Circuits.Action
