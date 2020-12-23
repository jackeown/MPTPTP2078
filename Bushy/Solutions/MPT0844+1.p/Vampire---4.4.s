%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t55_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:12 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  271 ( 580 expanded)
%              Number of leaves         :   77 ( 248 expanded)
%              Depth                    :    8
%              Number of atoms          :  614 (1275 expanded)
%              Number of equality atoms :   54 ( 127 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f623,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f95,f102,f109,f117,f125,f135,f150,f166,f176,f191,f200,f218,f224,f237,f242,f249,f265,f279,f293,f308,f314,f322,f355,f367,f377,f387,f395,f408,f411,f424,f429,f436,f449,f463,f477,f494,f500,f512,f532,f540,f556,f564,f575,f583,f597,f612,f619,f622])).

fof(f622,plain,
    ( ~ spl5_6
    | spl5_9
    | ~ spl5_58 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f620,f407])).

fof(f407,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl5_58
  <=> k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f620,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(superposition,[],[f116,f399])).

fof(f399,plain,
    ( ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl5_6 ),
    inference(resolution,[],[f79,f108])).

fof(f108,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',redefinition_k5_relset_1)).

fof(f116,plain,
    ( k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_9
  <=> k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f619,plain,
    ( spl5_96
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f544,f538,f617])).

fof(f617,plain,
    ( spl5_96
  <=> k1_relset_1(sK2,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f538,plain,
    ( spl5_82
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f544,plain,
    ( k1_relset_1(sK2,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ spl5_82 ),
    inference(resolution,[],[f539,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',redefinition_k1_relset_1)).

fof(f539,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f538])).

fof(f612,plain,
    ( ~ spl5_95
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f604,f581,f610])).

fof(f610,plain,
    ( spl5_95
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f581,plain,
    ( spl5_90
  <=> r2_hidden(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f604,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_relat_1(k1_xboole_0))
    | ~ spl5_90 ),
    inference(resolution,[],[f582,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',antisymmetry_r2_hidden)).

fof(f582,plain,
    ( r2_hidden(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f581])).

fof(f597,plain,
    ( spl5_92
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f588,f422,f174,f164,f595])).

fof(f595,plain,
    ( spl5_92
  <=> k1_zfmisc_1(sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f164,plain,
    ( spl5_16
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f174,plain,
    ( spl5_18
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f422,plain,
    ( spl5_62
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f588,plain,
    ( k1_zfmisc_1(sK2) = k1_xboole_0
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f584,f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f584,plain,
    ( k1_zfmisc_1(sK2) = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_16
    | ~ spl5_62 ),
    inference(resolution,[],[f423,f168])).

fof(f168,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK4(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl5_16 ),
    inference(resolution,[],[f165,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t8_boole)).

fof(f165,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f423,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f422])).

fof(f583,plain,
    ( spl5_90
    | spl5_63
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f568,f562,f419,f581])).

fof(f419,plain,
    ( spl5_63
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f562,plain,
    ( spl5_86
  <=> m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f568,plain,
    ( r2_hidden(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl5_63
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f567,f420])).

fof(f420,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f419])).

fof(f567,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | r2_hidden(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl5_86 ),
    inference(resolution,[],[f563,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t2_subset)).

fof(f563,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f562])).

fof(f575,plain,
    ( spl5_88
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f566,f562,f573])).

fof(f573,plain,
    ( spl5_88
  <=> r1_tarski(k1_relat_1(k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f566,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ spl5_86 ),
    inference(resolution,[],[f563,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t3_subset)).

fof(f564,plain,
    ( spl5_86
    | ~ spl5_82
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f557,f554,f538,f562])).

fof(f554,plain,
    ( spl5_84
  <=> m1_subset_1(k1_relset_1(sK2,sK0,k1_xboole_0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f557,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl5_82
    | ~ spl5_84 ),
    inference(forward_demodulation,[],[f555,f544])).

fof(f555,plain,
    ( m1_subset_1(k1_relset_1(sK2,sK0,k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f554])).

fof(f556,plain,
    ( spl5_84
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f543,f538,f554])).

fof(f543,plain,
    ( m1_subset_1(k1_relset_1(sK2,sK0,k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl5_82 ),
    inference(resolution,[],[f539,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',dt_k1_relset_1)).

fof(f540,plain,
    ( spl5_82
    | ~ spl5_6
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f521,f406,f107,f538])).

fof(f521,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_6
    | ~ spl5_58 ),
    inference(superposition,[],[f504,f407])).

fof(f504,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f501,f399])).

fof(f501,plain,
    ( ! [X0] : m1_subset_1(k5_relset_1(sK2,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_6 ),
    inference(resolution,[],[f80,f108])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',dt_k5_relset_1)).

fof(f532,plain,
    ( spl5_80
    | ~ spl5_6
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f525,f406,f107,f530])).

fof(f530,plain,
    ( spl5_80
  <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f525,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK0))
    | ~ spl5_6
    | ~ spl5_58 ),
    inference(superposition,[],[f519,f407])).

fof(f519,plain,
    ( ! [X8] : r1_tarski(k7_relat_1(sK3,X8),k2_zfmisc_1(sK2,sK0))
    | ~ spl5_6 ),
    inference(resolution,[],[f504,f70])).

fof(f512,plain,
    ( ~ spl5_79
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f498,f469,f510])).

fof(f510,plain,
    ( spl5_79
  <=> ~ r2_hidden(sK2,sK4(k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f469,plain,
    ( spl5_72
  <=> r2_hidden(sK4(k1_relat_1(sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f498,plain,
    ( ~ r2_hidden(sK2,sK4(k1_relat_1(sK3)))
    | ~ spl5_72 ),
    inference(resolution,[],[f470,f66])).

fof(f470,plain,
    ( r2_hidden(sK4(k1_relat_1(sK3)),sK2)
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f469])).

fof(f500,plain,
    ( ~ spl5_75
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f499,f469,f472])).

fof(f472,plain,
    ( spl5_75
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f499,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_72 ),
    inference(resolution,[],[f470,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t7_boole)).

fof(f494,plain,
    ( spl5_76
    | ~ spl5_52
    | ~ spl5_70 ),
    inference(avatar_split_clause,[],[f481,f461,f375,f492])).

fof(f492,plain,
    ( spl5_76
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f375,plain,
    ( spl5_52
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f461,plain,
    ( spl5_70
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f481,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_52
    | ~ spl5_70 ),
    inference(superposition,[],[f376,f462])).

fof(f462,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f461])).

fof(f376,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f375])).

fof(f477,plain,
    ( spl5_72
    | spl5_74
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f464,f447,f475,f469])).

fof(f475,plain,
    ( spl5_74
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f447,plain,
    ( spl5_68
  <=> m1_subset_1(sK4(k1_relat_1(sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f464,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(sK4(k1_relat_1(sK3)),sK2)
    | ~ spl5_68 ),
    inference(resolution,[],[f448,f69])).

fof(f448,plain,
    ( m1_subset_1(sK4(k1_relat_1(sK3)),sK2)
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f447])).

fof(f463,plain,
    ( spl5_70
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f454,f441,f174,f164,f461])).

fof(f441,plain,
    ( spl5_66
  <=> v1_xboole_0(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f454,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_66 ),
    inference(forward_demodulation,[],[f450,f175])).

fof(f450,plain,
    ( k1_relat_1(sK3) = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_16
    | ~ spl5_66 ),
    inference(resolution,[],[f442,f168])).

fof(f442,plain,
    ( v1_xboole_0(k1_relat_1(sK3))
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f441])).

fof(f449,plain,
    ( spl5_66
    | spl5_68
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f368,f365,f447,f441])).

fof(f365,plain,
    ( spl5_50
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f368,plain,
    ( m1_subset_1(sK4(k1_relat_1(sK3)),sK2)
    | v1_xboole_0(k1_relat_1(sK3))
    | ~ spl5_50 ),
    inference(resolution,[],[f366,f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f77,f137])).

fof(f137,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',existence_m1_subset_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t4_subset)).

fof(f366,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f365])).

fof(f436,plain,
    ( ~ spl5_65
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f427,f416,f434])).

fof(f434,plain,
    ( spl5_65
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f416,plain,
    ( spl5_60
  <=> r2_hidden(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f427,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_relat_1(sK3))
    | ~ spl5_60 ),
    inference(resolution,[],[f417,f66])).

fof(f417,plain,
    ( r2_hidden(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f416])).

fof(f429,plain,
    ( ~ spl5_63
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f428,f416,f419])).

fof(f428,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl5_60 ),
    inference(resolution,[],[f417,f72])).

fof(f424,plain,
    ( spl5_60
    | spl5_62
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f370,f365,f422,f416])).

fof(f370,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | r2_hidden(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl5_50 ),
    inference(resolution,[],[f366,f69])).

fof(f411,plain,
    ( spl5_44
    | ~ spl5_14
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f410,f406,f148,f306])).

fof(f306,plain,
    ( spl5_44
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f148,plain,
    ( spl5_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f410,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_14
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f409,f149])).

fof(f149,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f409,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_58 ),
    inference(superposition,[],[f65,f407])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',dt_k7_relat_1)).

fof(f408,plain,
    ( spl5_58
    | ~ spl5_14
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f398,f393,f148,f406])).

fof(f393,plain,
    ( spl5_56
  <=> r1_xboole_0(sK1,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f398,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl5_14
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f396,f149])).

fof(f396,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl5_56 ),
    inference(resolution,[],[f394,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t187_relat_1)).

fof(f394,plain,
    ( r1_xboole_0(sK1,k1_relat_1(sK3))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f393])).

fof(f395,plain,
    ( spl5_56
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f388,f385,f393])).

fof(f385,plain,
    ( spl5_54
  <=> r1_xboole_0(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f388,plain,
    ( r1_xboole_0(sK1,k1_relat_1(sK3))
    | ~ spl5_54 ),
    inference(resolution,[],[f386,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',symmetry_r1_xboole_0)).

fof(f386,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK1)
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f385])).

fof(f387,plain,
    ( spl5_54
    | ~ spl5_10
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f379,f375,f123,f385])).

fof(f123,plain,
    ( spl5_10
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f379,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK1)
    | ~ spl5_10
    | ~ spl5_52 ),
    inference(resolution,[],[f378,f124])).

fof(f124,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f378,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | r1_xboole_0(k1_relat_1(sK3),X0) )
    | ~ spl5_52 ),
    inference(resolution,[],[f376,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t63_xboole_1)).

fof(f377,plain,
    ( spl5_52
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f369,f365,f375])).

fof(f369,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl5_50 ),
    inference(resolution,[],[f366,f70])).

fof(f367,plain,
    ( spl5_50
    | ~ spl5_6
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f360,f353,f107,f365])).

fof(f353,plain,
    ( spl5_48
  <=> k1_relset_1(sK2,sK0,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f360,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl5_6
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f358,f354])).

fof(f354,plain,
    ( k1_relset_1(sK2,sK0,sK3) = k1_relat_1(sK3)
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f353])).

fof(f358,plain,
    ( m1_subset_1(k1_relset_1(sK2,sK0,sK3),k1_zfmisc_1(sK2))
    | ~ spl5_6 ),
    inference(resolution,[],[f75,f108])).

fof(f355,plain,
    ( spl5_48
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f348,f107,f353])).

fof(f348,plain,
    ( k1_relset_1(sK2,sK0,sK3) = k1_relat_1(sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f74,f108])).

fof(f322,plain,
    ( ~ spl5_47
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f312,f285,f320])).

fof(f320,plain,
    ( spl5_47
  <=> ~ r2_hidden(k2_zfmisc_1(sK2,sK0),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f285,plain,
    ( spl5_40
  <=> r2_hidden(sK4(sK3),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f312,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK2,sK0),sK4(sK3))
    | ~ spl5_40 ),
    inference(resolution,[],[f286,f66])).

fof(f286,plain,
    ( r2_hidden(sK4(sK3),k2_zfmisc_1(sK2,sK0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f285])).

fof(f314,plain,
    ( ~ spl5_43
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f313,f285,f288])).

fof(f288,plain,
    ( spl5_43
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f313,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK0))
    | ~ spl5_40 ),
    inference(resolution,[],[f286,f72])).

fof(f308,plain,
    ( spl5_44
    | ~ spl5_14
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f299,f277,f148,f306])).

fof(f277,plain,
    ( spl5_38
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f299,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_14
    | ~ spl5_38 ),
    inference(superposition,[],[f149,f278])).

fof(f278,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f277])).

fof(f293,plain,
    ( spl5_40
    | spl5_42
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f280,f263,f291,f285])).

fof(f291,plain,
    ( spl5_42
  <=> v1_xboole_0(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f263,plain,
    ( spl5_36
  <=> m1_subset_1(sK4(sK3),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f280,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK2,sK0))
    | r2_hidden(sK4(sK3),k2_zfmisc_1(sK2,sK0))
    | ~ spl5_36 ),
    inference(resolution,[],[f264,f69])).

fof(f264,plain,
    ( m1_subset_1(sK4(sK3),k2_zfmisc_1(sK2,sK0))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f263])).

fof(f279,plain,
    ( spl5_38
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f270,f257,f174,f164,f277])).

fof(f257,plain,
    ( spl5_34
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f270,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f266,f175])).

fof(f266,plain,
    ( sK3 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_16
    | ~ spl5_34 ),
    inference(resolution,[],[f258,f168])).

fof(f258,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f257])).

fof(f265,plain,
    ( spl5_34
    | spl5_36
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f251,f107,f263,f257])).

fof(f251,plain,
    ( m1_subset_1(sK4(sK3),k2_zfmisc_1(sK2,sK0))
    | v1_xboole_0(sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f222,f108])).

fof(f249,plain,
    ( ~ spl5_33
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f240,f229,f247])).

fof(f247,plain,
    ( spl5_33
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f229,plain,
    ( spl5_28
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f240,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)),sK3)
    | ~ spl5_28 ),
    inference(resolution,[],[f230,f66])).

fof(f230,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f229])).

fof(f242,plain,
    ( ~ spl5_31
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f241,f229,f232])).

fof(f232,plain,
    ( spl5_31
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f241,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_28 ),
    inference(resolution,[],[f230,f72])).

fof(f237,plain,
    ( spl5_28
    | spl5_30
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f138,f107,f235,f229])).

fof(f235,plain,
    ( spl5_30
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f138,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_6 ),
    inference(resolution,[],[f69,f108])).

fof(f224,plain,
    ( ~ spl5_25
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f221,f216,f207])).

fof(f207,plain,
    ( spl5_25
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f216,plain,
    ( spl5_26
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f221,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_26 ),
    inference(resolution,[],[f217,f72])).

fof(f217,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f216])).

fof(f218,plain,
    ( spl5_24
    | spl5_26
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f183,f174,f216,f210])).

fof(f210,plain,
    ( spl5_24
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f183,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18 ),
    inference(superposition,[],[f137,f175])).

fof(f200,plain,
    ( spl5_22
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f184,f174,f198])).

fof(f198,plain,
    ( spl5_22
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f184,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18 ),
    inference(superposition,[],[f64,f175])).

fof(f191,plain,
    ( spl5_20
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f181,f174,f189])).

fof(f189,plain,
    ( spl5_20
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f181,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_18 ),
    inference(superposition,[],[f127,f175])).

fof(f127,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f70,f64])).

fof(f176,plain,
    ( spl5_18
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f169,f164,f174])).

fof(f169,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_16 ),
    inference(resolution,[],[f165,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t6_boole)).

fof(f166,plain,
    ( spl5_16
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f159,f86,f164])).

fof(f86,plain,
    ( spl5_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f159,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_0 ),
    inference(resolution,[],[f158,f137])).

fof(f158,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_0 ),
    inference(resolution,[],[f157,f64])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f78,f87])).

fof(f87,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f86])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t5_subset)).

fof(f150,plain,
    ( spl5_14
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f143,f107,f148])).

fof(f143,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f73,f108])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',cc1_relset_1)).

fof(f135,plain,
    ( spl5_12
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f128,f107,f133])).

fof(f133,plain,
    ( spl5_12
  <=> r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f128,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
    | ~ spl5_6 ),
    inference(resolution,[],[f70,f108])).

fof(f125,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f118,f93,f123])).

fof(f93,plain,
    ( spl5_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f118,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f68,f94])).

fof(f94,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f117,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f59,f115])).

fof(f59,plain,(
    k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f53])).

fof(f53,plain,
    ( ? [X0,X1,X2,X3] :
        ( k5_relset_1(X2,X0,X3,X1) != k1_xboole_0
        & r1_xboole_0(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( k5_relset_1(X2,X0,X3,X1) != k1_xboole_0
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( k5_relset_1(X2,X0,X3,X1) != k1_xboole_0
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k5_relset_1(X2,X0,X3,X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k5_relset_1(X2,X0,X3,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',t55_relset_1)).

fof(f109,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f57,f107])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f102,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f61,f100])).

fof(f100,plain,
    ( spl5_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f61,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',d2_xboole_0)).

fof(f95,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f58,f93])).

fof(f58,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f81,f86])).

fof(f81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f60,f61])).

fof(f60,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t55_relset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
