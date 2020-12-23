%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:19 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 278 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  254 ( 599 expanded)
%              Number of equality atoms :   70 ( 195 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f561,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f99,f114,f157,f161,f167,f207,f490,f499,f549,f560])).

fof(f560,plain,
    ( ~ spl3_2
    | spl3_26 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | ~ spl3_2
    | spl3_26 ),
    inference(unit_resulting_resolution,[],[f116,f548,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f548,plain,
    ( k1_xboole_0 != k6_subset_1(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl3_26
  <=> k1_xboole_0 = k6_subset_1(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f116,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f79,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f79,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f62,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f549,plain,
    ( ~ spl3_26
    | spl3_8
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f544,f496,f203,f159,f110,f546])).

fof(f110,plain,
    ( spl3_8
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f159,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f203,plain,
    ( spl3_15
  <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f496,plain,
    ( spl3_24
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f544,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | k1_xboole_0 != k6_subset_1(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f541,f498])).

fof(f498,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f496])).

fof(f541,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k6_subset_1(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(superposition,[],[f193,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f203])).

fof(f193,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
        | k1_xboole_0 != k6_subset_1(X0,k2_relat_1(sK2)) )
    | ~ spl3_12 ),
    inference(resolution,[],[f160,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f499,plain,
    ( spl3_24
    | ~ spl3_11
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f492,f484,f154,f496])).

fof(f154,plain,
    ( spl3_11
  <=> k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f484,plain,
    ( spl3_23
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f492,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f156,f486])).

fof(f486,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f484])).

fof(f156,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f490,plain,
    ( spl3_23
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f489,f165,f484])).

fof(f165,plain,
    ( spl3_13
  <=> ! [X1,X0] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f489,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f475,f265])).

fof(f265,plain,(
    ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f259,f133])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) ),
    inference(superposition,[],[f50,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f39,f46,f36,f36])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f259,plain,(
    ! [X1] : k6_subset_1(X1,X1) = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) ),
    inference(superposition,[],[f130,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f35,f46,f46])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f130,plain,(
    ! [X1] : k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)) = k6_subset_1(X1,X1) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f475,plain,
    ( ! [X4] : k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X4,X4))
    | ~ spl3_13 ),
    inference(superposition,[],[f166,f265])).

fof(f166,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f207,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f199,f165,f90,f203])).

fof(f90,plain,
    ( spl3_6
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f199,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(superposition,[],[f92,f166])).

fof(f92,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f167,plain,
    ( ~ spl3_5
    | spl3_13
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f163,f70,f165,f75])).

fof(f75,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_4 ),
    inference(resolution,[],[f45,f72])).

fof(f72,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f161,plain,
    ( ~ spl3_5
    | spl3_12
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f147,f70,f159,f75])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl3_4 ),
    inference(resolution,[],[f40,f72])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f157,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f144,f75,f70,f154])).

fof(f144,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f77,f72,f32,f40])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f77,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f114,plain,
    ( ~ spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f107,f55,f110])).

fof(f55,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f107,plain,
    ( k1_xboole_0 != k6_subset_1(sK0,sK1)
    | spl3_1 ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f99,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f87,f65,f90])).

fof(f65,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f87,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f51,f67])).

fof(f67,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f78,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f75])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f73,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (819134465)
% 0.14/0.37  ipcrm: permission denied for id (819167234)
% 0.14/0.37  ipcrm: permission denied for id (819200005)
% 0.14/0.37  ipcrm: permission denied for id (819232774)
% 0.14/0.37  ipcrm: permission denied for id (820805639)
% 0.14/0.38  ipcrm: permission denied for id (820871177)
% 0.14/0.38  ipcrm: permission denied for id (820903946)
% 0.14/0.38  ipcrm: permission denied for id (820936715)
% 0.14/0.38  ipcrm: permission denied for id (821002253)
% 0.14/0.39  ipcrm: permission denied for id (819331091)
% 0.14/0.39  ipcrm: permission denied for id (819363861)
% 0.14/0.39  ipcrm: permission denied for id (819396630)
% 0.14/0.39  ipcrm: permission denied for id (819429399)
% 0.14/0.40  ipcrm: permission denied for id (821297178)
% 0.14/0.40  ipcrm: permission denied for id (821329947)
% 0.14/0.40  ipcrm: permission denied for id (819462172)
% 0.14/0.40  ipcrm: permission denied for id (821362717)
% 0.14/0.40  ipcrm: permission denied for id (821395486)
% 0.21/0.40  ipcrm: permission denied for id (821461024)
% 0.21/0.41  ipcrm: permission denied for id (821526562)
% 0.21/0.41  ipcrm: permission denied for id (819593251)
% 0.21/0.41  ipcrm: permission denied for id (821592100)
% 0.21/0.41  ipcrm: permission denied for id (819658791)
% 0.21/0.41  ipcrm: permission denied for id (821690408)
% 0.21/0.42  ipcrm: permission denied for id (821723177)
% 0.21/0.42  ipcrm: permission denied for id (821755946)
% 0.21/0.42  ipcrm: permission denied for id (821788715)
% 0.21/0.42  ipcrm: permission denied for id (821821484)
% 0.21/0.42  ipcrm: permission denied for id (821887022)
% 0.21/0.42  ipcrm: permission denied for id (821919791)
% 0.21/0.42  ipcrm: permission denied for id (821952560)
% 0.21/0.43  ipcrm: permission denied for id (822050867)
% 0.21/0.43  ipcrm: permission denied for id (819789877)
% 0.21/0.43  ipcrm: permission denied for id (822116406)
% 0.21/0.43  ipcrm: permission denied for id (822149175)
% 0.21/0.43  ipcrm: permission denied for id (822181944)
% 0.21/0.44  ipcrm: permission denied for id (822214713)
% 0.21/0.44  ipcrm: permission denied for id (819855419)
% 0.21/0.44  ipcrm: permission denied for id (819888189)
% 0.21/0.44  ipcrm: permission denied for id (819953726)
% 0.21/0.44  ipcrm: permission denied for id (819986495)
% 0.21/0.45  ipcrm: permission denied for id (822411330)
% 0.21/0.45  ipcrm: permission denied for id (822444099)
% 0.21/0.45  ipcrm: permission denied for id (820117575)
% 0.21/0.46  ipcrm: permission denied for id (820150346)
% 0.21/0.46  ipcrm: permission denied for id (822706252)
% 0.21/0.46  ipcrm: permission denied for id (822739021)
% 0.21/0.46  ipcrm: permission denied for id (820183118)
% 0.21/0.46  ipcrm: permission denied for id (822804560)
% 0.21/0.47  ipcrm: permission denied for id (820248657)
% 0.21/0.47  ipcrm: permission denied for id (822870099)
% 0.21/0.47  ipcrm: permission denied for id (822902868)
% 0.21/0.47  ipcrm: permission denied for id (823001175)
% 0.21/0.47  ipcrm: permission denied for id (820281432)
% 0.21/0.48  ipcrm: permission denied for id (820346970)
% 0.21/0.48  ipcrm: permission denied for id (823066715)
% 0.21/0.48  ipcrm: permission denied for id (823099484)
% 0.21/0.48  ipcrm: permission denied for id (823197791)
% 0.21/0.49  ipcrm: permission denied for id (823296098)
% 0.21/0.49  ipcrm: permission denied for id (820379749)
% 0.21/0.49  ipcrm: permission denied for id (823394406)
% 0.21/0.49  ipcrm: permission denied for id (823459944)
% 0.21/0.50  ipcrm: permission denied for id (823525482)
% 0.21/0.50  ipcrm: permission denied for id (823623789)
% 0.21/0.50  ipcrm: permission denied for id (820412527)
% 0.21/0.50  ipcrm: permission denied for id (820445296)
% 0.21/0.50  ipcrm: permission denied for id (823689329)
% 0.21/0.51  ipcrm: permission denied for id (823787636)
% 0.21/0.51  ipcrm: permission denied for id (820543605)
% 0.21/0.51  ipcrm: permission denied for id (823820406)
% 0.21/0.51  ipcrm: permission denied for id (820576375)
% 0.21/0.51  ipcrm: permission denied for id (820609145)
% 0.21/0.52  ipcrm: permission denied for id (823918714)
% 0.21/0.52  ipcrm: permission denied for id (824082559)
% 0.21/0.60  % (1875)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.73/0.61  % (1880)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.73/0.61  % (1872)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.96/0.63  % (1877)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.16/0.65  % (1870)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.16/0.65  % (1884)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.16/0.66  % (1873)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.16/0.66  % (1876)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.16/0.66  % (1878)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.16/0.66  % (1883)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.16/0.66  % (1879)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.16/0.66  % (1881)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.16/0.66  % (1882)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.16/0.66  % (1876)Refutation found. Thanks to Tanya!
% 1.16/0.66  % SZS status Theorem for theBenchmark
% 1.16/0.66  % SZS output start Proof for theBenchmark
% 1.16/0.66  fof(f561,plain,(
% 1.16/0.66    $false),
% 1.16/0.66    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f99,f114,f157,f161,f167,f207,f490,f499,f549,f560])).
% 1.16/0.66  fof(f560,plain,(
% 1.16/0.66    ~spl3_2 | spl3_26),
% 1.16/0.66    inference(avatar_contradiction_clause,[],[f554])).
% 1.16/0.66  fof(f554,plain,(
% 1.16/0.66    $false | (~spl3_2 | spl3_26)),
% 1.16/0.66    inference(unit_resulting_resolution,[],[f116,f548,f51])).
% 1.16/0.66  fof(f51,plain,(
% 1.16/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.16/0.66    inference(definition_unfolding,[],[f42,f36])).
% 1.16/0.66  fof(f36,plain,(
% 1.16/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f10])).
% 1.16/0.66  fof(f10,axiom,(
% 1.16/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.16/0.66  fof(f42,plain,(
% 1.16/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f26])).
% 1.16/0.66  fof(f26,plain,(
% 1.16/0.66    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.16/0.66    inference(nnf_transformation,[],[f2])).
% 1.16/0.66  fof(f2,axiom,(
% 1.16/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.16/0.66  fof(f548,plain,(
% 1.16/0.66    k1_xboole_0 != k6_subset_1(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | spl3_26),
% 1.16/0.66    inference(avatar_component_clause,[],[f546])).
% 1.16/0.66  fof(f546,plain,(
% 1.16/0.66    spl3_26 <=> k1_xboole_0 = k6_subset_1(k6_subset_1(sK0,sK1),k2_relat_1(sK2))),
% 1.16/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.16/0.66  fof(f116,plain,(
% 1.16/0.66    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))) ) | ~spl3_2),
% 1.16/0.66    inference(unit_resulting_resolution,[],[f79,f53])).
% 1.16/0.66  fof(f53,plain,(
% 1.16/0.66    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.16/0.66    inference(definition_unfolding,[],[f44,f36])).
% 1.16/0.66  fof(f44,plain,(
% 1.16/0.66    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.16/0.66    inference(cnf_transformation,[],[f21])).
% 1.16/0.66  fof(f21,plain,(
% 1.16/0.66    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.16/0.66    inference(ennf_transformation,[],[f6])).
% 1.16/0.66  fof(f6,axiom,(
% 1.16/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.16/0.67  fof(f79,plain,(
% 1.16/0.67    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2)))) ) | ~spl3_2),
% 1.16/0.67    inference(unit_resulting_resolution,[],[f62,f43])).
% 1.16/0.67  fof(f43,plain,(
% 1.16/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.16/0.67    inference(cnf_transformation,[],[f20])).
% 1.16/0.67  fof(f20,plain,(
% 1.16/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.16/0.67    inference(ennf_transformation,[],[f3])).
% 1.16/0.67  fof(f3,axiom,(
% 1.16/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.16/0.67  fof(f62,plain,(
% 1.16/0.67    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 1.16/0.67    inference(avatar_component_clause,[],[f60])).
% 1.16/0.67  fof(f60,plain,(
% 1.16/0.67    spl3_2 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.16/0.67  fof(f549,plain,(
% 1.16/0.67    ~spl3_26 | spl3_8 | ~spl3_12 | ~spl3_15 | ~spl3_24),
% 1.16/0.67    inference(avatar_split_clause,[],[f544,f496,f203,f159,f110,f546])).
% 1.16/0.67  fof(f110,plain,(
% 1.16/0.67    spl3_8 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.16/0.67  fof(f159,plain,(
% 1.16/0.67    spl3_12 <=> ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0)),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.16/0.67  fof(f203,plain,(
% 1.16/0.67    spl3_15 <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.16/0.67  fof(f496,plain,(
% 1.16/0.67    spl3_24 <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.16/0.67  fof(f544,plain,(
% 1.16/0.67    k1_xboole_0 = k6_subset_1(sK0,sK1) | k1_xboole_0 != k6_subset_1(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | (~spl3_12 | ~spl3_15 | ~spl3_24)),
% 1.16/0.67    inference(forward_demodulation,[],[f541,f498])).
% 1.16/0.67  fof(f498,plain,(
% 1.16/0.67    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl3_24),
% 1.16/0.67    inference(avatar_component_clause,[],[f496])).
% 1.16/0.67  fof(f541,plain,(
% 1.16/0.67    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k6_subset_1(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | (~spl3_12 | ~spl3_15)),
% 1.16/0.67    inference(superposition,[],[f193,f205])).
% 1.16/0.67  fof(f205,plain,(
% 1.16/0.67    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~spl3_15),
% 1.16/0.67    inference(avatar_component_clause,[],[f203])).
% 1.16/0.67  fof(f193,plain,(
% 1.16/0.67    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | k1_xboole_0 != k6_subset_1(X0,k2_relat_1(sK2))) ) | ~spl3_12),
% 1.16/0.67    inference(resolution,[],[f160,f52])).
% 1.16/0.67  fof(f52,plain,(
% 1.16/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 1.16/0.67    inference(definition_unfolding,[],[f41,f36])).
% 1.16/0.67  fof(f41,plain,(
% 1.16/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.16/0.67    inference(cnf_transformation,[],[f26])).
% 1.16/0.67  fof(f160,plain,(
% 1.16/0.67    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl3_12),
% 1.16/0.67    inference(avatar_component_clause,[],[f159])).
% 1.16/0.67  fof(f499,plain,(
% 1.16/0.67    spl3_24 | ~spl3_11 | ~spl3_23),
% 1.16/0.67    inference(avatar_split_clause,[],[f492,f484,f154,f496])).
% 1.16/0.67  fof(f154,plain,(
% 1.16/0.67    spl3_11 <=> k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.16/0.67  fof(f484,plain,(
% 1.16/0.67    spl3_23 <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.16/0.67  fof(f492,plain,(
% 1.16/0.67    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | (~spl3_11 | ~spl3_23)),
% 1.16/0.67    inference(backward_demodulation,[],[f156,f486])).
% 1.16/0.67  fof(f486,plain,(
% 1.16/0.67    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~spl3_23),
% 1.16/0.67    inference(avatar_component_clause,[],[f484])).
% 1.16/0.67  fof(f156,plain,(
% 1.16/0.67    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) | ~spl3_11),
% 1.16/0.67    inference(avatar_component_clause,[],[f154])).
% 1.16/0.67  fof(f490,plain,(
% 1.16/0.67    spl3_23 | ~spl3_13),
% 1.16/0.67    inference(avatar_split_clause,[],[f489,f165,f484])).
% 1.16/0.67  fof(f165,plain,(
% 1.16/0.67    spl3_13 <=> ! [X1,X0] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.16/0.67  fof(f489,plain,(
% 1.16/0.67    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~spl3_13),
% 1.16/0.67    inference(forward_demodulation,[],[f475,f265])).
% 1.16/0.67  fof(f265,plain,(
% 1.16/0.67    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) )),
% 1.16/0.67    inference(forward_demodulation,[],[f259,f133])).
% 1.16/0.67  fof(f133,plain,(
% 1.16/0.67    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) )),
% 1.16/0.67    inference(superposition,[],[f50,f47])).
% 1.16/0.67  fof(f47,plain,(
% 1.16/0.67    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 1.16/0.67    inference(definition_unfolding,[],[f33,f36])).
% 1.16/0.67  fof(f33,plain,(
% 1.16/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.16/0.67    inference(cnf_transformation,[],[f8])).
% 1.16/0.67  fof(f8,axiom,(
% 1.16/0.67    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.16/0.67  fof(f50,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.16/0.67    inference(definition_unfolding,[],[f39,f46,f36,f36])).
% 1.16/0.67  fof(f46,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.16/0.67    inference(definition_unfolding,[],[f37,f38])).
% 1.16/0.67  fof(f38,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.16/0.67    inference(cnf_transformation,[],[f9])).
% 1.16/0.67  fof(f9,axiom,(
% 1.16/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.16/0.67  fof(f37,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.16/0.67    inference(cnf_transformation,[],[f11])).
% 1.16/0.67  fof(f11,axiom,(
% 1.16/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.16/0.67  fof(f39,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.16/0.67    inference(cnf_transformation,[],[f7])).
% 1.16/0.67  fof(f7,axiom,(
% 1.16/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.16/0.67  fof(f259,plain,(
% 1.16/0.67    ( ! [X1] : (k6_subset_1(X1,X1) = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))) )),
% 1.16/0.67    inference(superposition,[],[f130,f49])).
% 1.16/0.67  fof(f49,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 1.16/0.67    inference(definition_unfolding,[],[f35,f46,f46])).
% 1.16/0.67  fof(f35,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.16/0.67    inference(cnf_transformation,[],[f1])).
% 1.16/0.67  fof(f1,axiom,(
% 1.16/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.16/0.67  fof(f130,plain,(
% 1.16/0.67    ( ! [X1] : (k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)) = k6_subset_1(X1,X1)) )),
% 1.16/0.67    inference(superposition,[],[f50,f48])).
% 1.16/0.67  fof(f48,plain,(
% 1.16/0.67    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 1.16/0.67    inference(definition_unfolding,[],[f34,f36])).
% 1.16/0.67  fof(f34,plain,(
% 1.16/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.16/0.67    inference(cnf_transformation,[],[f5])).
% 1.16/0.67  fof(f5,axiom,(
% 1.16/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.16/0.67  fof(f475,plain,(
% 1.16/0.67    ( ! [X4] : (k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X4,X4))) ) | ~spl3_13),
% 1.16/0.67    inference(superposition,[],[f166,f265])).
% 1.16/0.67  fof(f166,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_13),
% 1.16/0.67    inference(avatar_component_clause,[],[f165])).
% 1.16/0.67  fof(f207,plain,(
% 1.16/0.67    spl3_15 | ~spl3_6 | ~spl3_13),
% 1.16/0.67    inference(avatar_split_clause,[],[f199,f165,f90,f203])).
% 1.16/0.67  fof(f90,plain,(
% 1.16/0.67    spl3_6 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.16/0.67  fof(f199,plain,(
% 1.16/0.67    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | (~spl3_6 | ~spl3_13)),
% 1.16/0.67    inference(superposition,[],[f92,f166])).
% 1.16/0.67  fof(f92,plain,(
% 1.16/0.67    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_6),
% 1.16/0.67    inference(avatar_component_clause,[],[f90])).
% 1.16/0.67  fof(f167,plain,(
% 1.16/0.67    ~spl3_5 | spl3_13 | ~spl3_4),
% 1.16/0.67    inference(avatar_split_clause,[],[f163,f70,f165,f75])).
% 1.16/0.67  fof(f75,plain,(
% 1.16/0.67    spl3_5 <=> v1_relat_1(sK2)),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.16/0.67  fof(f70,plain,(
% 1.16/0.67    spl3_4 <=> v1_funct_1(sK2)),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.16/0.67  fof(f163,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) ) | ~spl3_4),
% 1.16/0.67    inference(resolution,[],[f45,f72])).
% 1.16/0.67  fof(f72,plain,(
% 1.16/0.67    v1_funct_1(sK2) | ~spl3_4),
% 1.16/0.67    inference(avatar_component_clause,[],[f70])).
% 1.16/0.67  fof(f45,plain,(
% 1.16/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.16/0.67    inference(cnf_transformation,[],[f23])).
% 1.16/0.67  fof(f23,plain,(
% 1.16/0.67    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.16/0.67    inference(flattening,[],[f22])).
% 1.16/0.67  fof(f22,plain,(
% 1.16/0.67    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.16/0.67    inference(ennf_transformation,[],[f12])).
% 1.16/0.67  fof(f12,axiom,(
% 1.16/0.67    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.16/0.67  fof(f161,plain,(
% 1.16/0.67    ~spl3_5 | spl3_12 | ~spl3_4),
% 1.16/0.67    inference(avatar_split_clause,[],[f147,f70,f159,f75])).
% 1.16/0.67  fof(f147,plain,(
% 1.16/0.67    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) ) | ~spl3_4),
% 1.16/0.67    inference(resolution,[],[f40,f72])).
% 1.16/0.67  fof(f40,plain,(
% 1.16/0.67    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.16/0.67    inference(cnf_transformation,[],[f19])).
% 1.16/0.67  fof(f19,plain,(
% 1.16/0.67    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.16/0.67    inference(flattening,[],[f18])).
% 1.16/0.67  fof(f18,plain,(
% 1.16/0.67    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.16/0.67    inference(ennf_transformation,[],[f13])).
% 1.16/0.67  fof(f13,axiom,(
% 1.16/0.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.16/0.67  fof(f157,plain,(
% 1.16/0.67    spl3_11 | ~spl3_4 | ~spl3_5),
% 1.16/0.67    inference(avatar_split_clause,[],[f144,f75,f70,f154])).
% 1.16/0.67  fof(f144,plain,(
% 1.16/0.67    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) | (~spl3_4 | ~spl3_5)),
% 1.16/0.67    inference(unit_resulting_resolution,[],[f77,f72,f32,f40])).
% 1.16/0.67  fof(f32,plain,(
% 1.16/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.16/0.67    inference(cnf_transformation,[],[f4])).
% 1.16/0.67  fof(f4,axiom,(
% 1.16/0.67    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.16/0.67  fof(f77,plain,(
% 1.16/0.67    v1_relat_1(sK2) | ~spl3_5),
% 1.16/0.67    inference(avatar_component_clause,[],[f75])).
% 1.16/0.67  fof(f114,plain,(
% 1.16/0.67    ~spl3_8 | spl3_1),
% 1.16/0.67    inference(avatar_split_clause,[],[f107,f55,f110])).
% 1.16/0.67  fof(f55,plain,(
% 1.16/0.67    spl3_1 <=> r1_tarski(sK0,sK1)),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.16/0.67  fof(f107,plain,(
% 1.16/0.67    k1_xboole_0 != k6_subset_1(sK0,sK1) | spl3_1),
% 1.16/0.67    inference(resolution,[],[f52,f57])).
% 1.16/0.67  fof(f57,plain,(
% 1.16/0.67    ~r1_tarski(sK0,sK1) | spl3_1),
% 1.16/0.67    inference(avatar_component_clause,[],[f55])).
% 1.16/0.67  fof(f99,plain,(
% 1.16/0.67    spl3_6 | ~spl3_3),
% 1.16/0.67    inference(avatar_split_clause,[],[f87,f65,f90])).
% 1.16/0.67  fof(f65,plain,(
% 1.16/0.67    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.16/0.67  fof(f87,plain,(
% 1.16/0.67    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 1.16/0.67    inference(resolution,[],[f51,f67])).
% 1.16/0.67  fof(f67,plain,(
% 1.16/0.67    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 1.16/0.67    inference(avatar_component_clause,[],[f65])).
% 1.16/0.67  fof(f78,plain,(
% 1.16/0.67    spl3_5),
% 1.16/0.67    inference(avatar_split_clause,[],[f27,f75])).
% 1.16/0.67  fof(f27,plain,(
% 1.16/0.67    v1_relat_1(sK2)),
% 1.16/0.67    inference(cnf_transformation,[],[f25])).
% 1.16/0.67  fof(f25,plain,(
% 1.16/0.67    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.16/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f24])).
% 1.16/0.67  fof(f24,plain,(
% 1.16/0.67    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.16/0.67    introduced(choice_axiom,[])).
% 1.16/0.67  fof(f17,plain,(
% 1.16/0.67    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.16/0.67    inference(flattening,[],[f16])).
% 1.16/0.67  fof(f16,plain,(
% 1.16/0.67    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.16/0.67    inference(ennf_transformation,[],[f15])).
% 1.16/0.67  fof(f15,negated_conjecture,(
% 1.16/0.67    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.16/0.67    inference(negated_conjecture,[],[f14])).
% 1.16/0.67  fof(f14,conjecture,(
% 1.16/0.67    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 1.16/0.67  fof(f73,plain,(
% 1.16/0.67    spl3_4),
% 1.16/0.67    inference(avatar_split_clause,[],[f28,f70])).
% 1.16/0.67  fof(f28,plain,(
% 1.16/0.67    v1_funct_1(sK2)),
% 1.16/0.67    inference(cnf_transformation,[],[f25])).
% 1.16/0.67  fof(f68,plain,(
% 1.16/0.67    spl3_3),
% 1.16/0.67    inference(avatar_split_clause,[],[f29,f65])).
% 1.16/0.67  fof(f29,plain,(
% 1.16/0.67    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.16/0.67    inference(cnf_transformation,[],[f25])).
% 1.16/0.67  fof(f63,plain,(
% 1.16/0.67    spl3_2),
% 1.16/0.67    inference(avatar_split_clause,[],[f30,f60])).
% 1.16/0.67  fof(f30,plain,(
% 1.16/0.67    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.16/0.67    inference(cnf_transformation,[],[f25])).
% 1.16/0.67  fof(f58,plain,(
% 1.16/0.67    ~spl3_1),
% 1.16/0.67    inference(avatar_split_clause,[],[f31,f55])).
% 1.16/0.67  fof(f31,plain,(
% 1.16/0.67    ~r1_tarski(sK0,sK1)),
% 1.16/0.67    inference(cnf_transformation,[],[f25])).
% 1.16/0.67  % SZS output end Proof for theBenchmark
% 1.16/0.67  % (1876)------------------------------
% 1.16/0.67  % (1876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.67  % (1876)Termination reason: Refutation
% 1.16/0.67  
% 1.16/0.67  % (1876)Memory used [KB]: 6396
% 1.16/0.67  % (1876)Time elapsed: 0.073 s
% 1.16/0.67  % (1876)------------------------------
% 1.16/0.67  % (1876)------------------------------
% 1.16/0.67  % (1725)Success in time 0.302 s
%------------------------------------------------------------------------------
