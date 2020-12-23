%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:02 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 541 expanded)
%              Number of leaves         :   37 ( 192 expanded)
%              Depth                    :   13
%              Number of atoms          :  487 (1304 expanded)
%              Number of equality atoms :  102 ( 378 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1892,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f120,f125,f136,f162,f281,f453,f660,f672,f685,f744,f761,f773,f796,f852,f866,f1843,f1891])).

fof(f1891,plain,
    ( ~ spl2_3
    | ~ spl2_16
    | ~ spl2_22
    | spl2_23
    | ~ spl2_29 ),
    inference(avatar_contradiction_clause,[],[f1890])).

fof(f1890,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_22
    | spl2_23
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f670,f996])).

fof(f996,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f984,f850])).

fof(f850,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(backward_demodulation,[],[f812,f848])).

fof(f848,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(backward_demodulation,[],[f826,f846])).

fof(f846,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_29 ),
    inference(superposition,[],[f795,f273])).

fof(f273,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f244,f246])).

fof(f246,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f110,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f91,f97])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f83,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f110,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f69,f66])).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f244,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f124,f106])).

fof(f124,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f795,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f793])).

fof(f793,plain,
    ( spl2_29
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f826,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f659,f255])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f105,f246])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f87,f97])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f659,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f657])).

fof(f657,plain,
    ( spl2_22
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f812,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f659,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f984,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl2_16 ),
    inference(resolution,[],[f169,f452])).

fof(f452,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f450])).

fof(f450,plain,
    ( spl2_16
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(k3_subset_1(X1,X0),X1) ) ),
    inference(resolution,[],[f86,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f670,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_23 ),
    inference(avatar_component_clause,[],[f669])).

fof(f669,plain,
    ( spl2_23
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f1843,plain,
    ( ~ spl2_3
    | spl2_9
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_26
    | ~ spl2_31 ),
    inference(avatar_contradiction_clause,[],[f1842])).

fof(f1842,plain,
    ( $false
    | ~ spl2_3
    | spl2_9
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_26
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f1841,f391])).

fof(f391,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl2_9
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f1841,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_26
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f1840,f763])).

fof(f763,plain,
    ( sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f671,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f85,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f671,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f669])).

fof(f1840,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_3
    | ~ spl2_22
    | ~ spl2_26
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f1803,f1831])).

fof(f1831,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_22
    | ~ spl2_26
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f845,f1830])).

fof(f1830,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f1817,f865])).

fof(f865,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f863])).

fof(f863,plain,
    ( spl2_31
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f1817,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f743,f124,f356])).

fof(f356,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k3_tarski(k2_tarski(X3,X4)) = k4_subset_1(X2,X3,X4)
      | ~ r1_tarski(X4,X2) ) ),
    inference(resolution,[],[f109,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f96,f81])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f743,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f741])).

fof(f741,plain,
    ( spl2_26
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f845,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f814,f101])).

fof(f101,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f79,f81,f81])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f814,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f110,f659,f109])).

fof(f1803,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f128,f659,f356])).

fof(f128,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f110,f89])).

fof(f866,plain,
    ( spl2_31
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f371,f122,f117,f863])).

fof(f117,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f371,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f119,f124,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f119,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f852,plain,
    ( ~ spl2_3
    | ~ spl2_22
    | spl2_27
    | ~ spl2_29 ),
    inference(avatar_contradiction_clause,[],[f851])).

fof(f851,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_22
    | spl2_27
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f850,f760])).

fof(f760,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f758])).

fof(f758,plain,
    ( spl2_27
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f796,plain,
    ( spl2_29
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f375,f122,f117,f793])).

fof(f375,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f119,f124,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f773,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f667,f389,f122,f117,f112,f155])).

fof(f155,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f112,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f667,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f119,f114,f124,f390,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f390,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f389])).

fof(f114,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f761,plain,
    ( ~ spl2_5
    | ~ spl2_27
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f747,f450,f122,f758,f155])).

fof(f747,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f746,f545])).

fof(f545,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f452,f255])).

fof(f746,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f65,f273])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f56,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f744,plain,
    ( spl2_26
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f675,f669,f133,f741])).

fof(f133,plain,
    ( spl2_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f675,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f135,f671,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f135,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f685,plain,
    ( spl2_22
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | spl2_22
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f681,f658])).

fof(f658,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_22 ),
    inference(avatar_component_clause,[],[f657])).

fof(f681,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f671,f90])).

fof(f672,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f664,f155,f122,f117,f669])).

fof(f664,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f119,f124,f157,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f157,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f660,plain,
    ( spl2_22
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f649,f450,f159,f122,f657])).

fof(f159,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f649,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(backward_demodulation,[],[f536,f648])).

fof(f648,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(backward_demodulation,[],[f545,f646])).

fof(f646,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f273,f161])).

fof(f161,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f536,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f452,f86])).

fof(f453,plain,
    ( spl2_16
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f340,f278,f450])).

fof(f278,plain,
    ( spl2_7
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f340,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f280,f90])).

fof(f280,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f278])).

fof(f281,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f192,f122,f117,f278])).

fof(f192,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f119,f124,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f162,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f64,f159,f155])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f136,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f126,f122,f133])).

fof(f126,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f124,f89])).

fof(f125,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f63,f122])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f120,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f62,f117])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f115,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f61,f112])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (10101)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (10089)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (10090)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (10095)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (10093)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (10104)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (10103)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (10092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (10091)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (10100)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (10106)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (10094)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (10102)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (10105)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (10098)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (10099)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (10096)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.38/0.53  % (10097)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.61/0.56  % (10104)Refutation found. Thanks to Tanya!
% 1.61/0.56  % SZS status Theorem for theBenchmark
% 1.61/0.56  % SZS output start Proof for theBenchmark
% 1.61/0.56  fof(f1892,plain,(
% 1.61/0.56    $false),
% 1.61/0.56    inference(avatar_sat_refutation,[],[f115,f120,f125,f136,f162,f281,f453,f660,f672,f685,f744,f761,f773,f796,f852,f866,f1843,f1891])).
% 1.61/0.56  fof(f1891,plain,(
% 1.61/0.56    ~spl2_3 | ~spl2_16 | ~spl2_22 | spl2_23 | ~spl2_29),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f1890])).
% 1.61/0.56  fof(f1890,plain,(
% 1.61/0.56    $false | (~spl2_3 | ~spl2_16 | ~spl2_22 | spl2_23 | ~spl2_29)),
% 1.61/0.56    inference(subsumption_resolution,[],[f670,f996])).
% 1.61/0.56  fof(f996,plain,(
% 1.61/0.56    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_16 | ~spl2_22 | ~spl2_29)),
% 1.61/0.56    inference(forward_demodulation,[],[f984,f850])).
% 1.61/0.56  fof(f850,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_22 | ~spl2_29)),
% 1.61/0.56    inference(backward_demodulation,[],[f812,f848])).
% 1.61/0.56  fof(f848,plain,(
% 1.61/0.56    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_22 | ~spl2_29)),
% 1.61/0.56    inference(backward_demodulation,[],[f826,f846])).
% 1.61/0.56  fof(f846,plain,(
% 1.61/0.56    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_29)),
% 1.61/0.56    inference(superposition,[],[f795,f273])).
% 1.61/0.56  fof(f273,plain,(
% 1.61/0.56    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) ) | ~spl2_3),
% 1.61/0.56    inference(forward_demodulation,[],[f244,f246])).
% 1.61/0.56  fof(f246,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f110,f106])).
% 1.61/0.56  fof(f106,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 1.61/0.56    inference(definition_unfolding,[],[f91,f97])).
% 1.61/0.56  fof(f97,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.61/0.56    inference(definition_unfolding,[],[f83,f80])).
% 1.61/0.56  fof(f80,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f21])).
% 1.61/0.56  fof(f21,axiom,(
% 1.61/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.61/0.56  fof(f83,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f3])).
% 1.61/0.56  fof(f3,axiom,(
% 1.61/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.61/0.56  fof(f91,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f46])).
% 1.61/0.56  fof(f46,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f19])).
% 1.61/0.56  fof(f19,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.61/0.56  fof(f110,plain,(
% 1.61/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(forward_demodulation,[],[f69,f66])).
% 1.61/0.56  fof(f66,plain,(
% 1.61/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.61/0.56    inference(cnf_transformation,[],[f13])).
% 1.61/0.56  fof(f13,axiom,(
% 1.61/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.61/0.56  fof(f69,plain,(
% 1.61/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f15])).
% 1.61/0.56  fof(f15,axiom,(
% 1.61/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.61/0.56  fof(f244,plain,(
% 1.61/0.56    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f124,f106])).
% 1.61/0.56  fof(f124,plain,(
% 1.61/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.61/0.56    inference(avatar_component_clause,[],[f122])).
% 1.61/0.56  fof(f122,plain,(
% 1.61/0.56    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.61/0.56  fof(f795,plain,(
% 1.61/0.56    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_29),
% 1.61/0.56    inference(avatar_component_clause,[],[f793])).
% 1.61/0.56  fof(f793,plain,(
% 1.61/0.56    spl2_29 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 1.61/0.56  fof(f826,plain,(
% 1.61/0.56    k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_22),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f659,f255])).
% 1.61/0.56  fof(f255,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 1.61/0.56    inference(backward_demodulation,[],[f105,f246])).
% 1.61/0.56  fof(f105,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.61/0.56    inference(definition_unfolding,[],[f87,f97])).
% 1.61/0.56  fof(f87,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f44])).
% 1.61/0.56  fof(f44,plain,(
% 1.61/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f14])).
% 1.61/0.56  fof(f14,axiom,(
% 1.61/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.61/0.56  fof(f659,plain,(
% 1.61/0.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_22),
% 1.61/0.56    inference(avatar_component_clause,[],[f657])).
% 1.61/0.56  fof(f657,plain,(
% 1.61/0.56    spl2_22 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.61/0.56  fof(f812,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_22),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f659,f88])).
% 1.61/0.56  fof(f88,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.61/0.56    inference(cnf_transformation,[],[f45])).
% 1.61/0.56  fof(f45,plain,(
% 1.61/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f17])).
% 1.61/0.56  fof(f17,axiom,(
% 1.61/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.61/0.56  fof(f984,plain,(
% 1.61/0.56    r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) | ~spl2_16),
% 1.61/0.56    inference(resolution,[],[f169,f452])).
% 1.61/0.56  fof(f452,plain,(
% 1.61/0.56    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_16),
% 1.61/0.56    inference(avatar_component_clause,[],[f450])).
% 1.61/0.56  fof(f450,plain,(
% 1.61/0.56    spl2_16 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.61/0.56  fof(f169,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k3_subset_1(X1,X0),X1)) )),
% 1.61/0.56    inference(resolution,[],[f86,f89])).
% 1.61/0.56  fof(f89,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f60])).
% 1.61/0.56  fof(f60,plain,(
% 1.61/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.61/0.56    inference(nnf_transformation,[],[f22])).
% 1.61/0.56  fof(f22,axiom,(
% 1.61/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.61/0.56  fof(f86,plain,(
% 1.61/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f43])).
% 1.61/0.56  fof(f43,plain,(
% 1.61/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f16])).
% 1.61/0.56  fof(f16,axiom,(
% 1.61/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.61/0.56  fof(f670,plain,(
% 1.61/0.56    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_23),
% 1.61/0.56    inference(avatar_component_clause,[],[f669])).
% 1.61/0.56  fof(f669,plain,(
% 1.61/0.56    spl2_23 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.61/0.56  fof(f1843,plain,(
% 1.61/0.56    ~spl2_3 | spl2_9 | ~spl2_22 | ~spl2_23 | ~spl2_26 | ~spl2_31),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f1842])).
% 1.61/0.56  fof(f1842,plain,(
% 1.61/0.56    $false | (~spl2_3 | spl2_9 | ~spl2_22 | ~spl2_23 | ~spl2_26 | ~spl2_31)),
% 1.61/0.56    inference(subsumption_resolution,[],[f1841,f391])).
% 1.61/0.56  fof(f391,plain,(
% 1.61/0.56    sK1 != k2_pre_topc(sK0,sK1) | spl2_9),
% 1.61/0.56    inference(avatar_component_clause,[],[f389])).
% 1.61/0.56  fof(f389,plain,(
% 1.61/0.56    spl2_9 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.61/0.56  fof(f1841,plain,(
% 1.61/0.56    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_22 | ~spl2_23 | ~spl2_26 | ~spl2_31)),
% 1.61/0.56    inference(forward_demodulation,[],[f1840,f763])).
% 1.61/0.56  fof(f763,plain,(
% 1.61/0.56    sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl2_23),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f671,f104])).
% 1.61/0.56  fof(f104,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 1.61/0.56    inference(definition_unfolding,[],[f85,f81])).
% 1.61/0.56  fof(f81,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f12])).
% 1.61/0.56  fof(f12,axiom,(
% 1.61/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.61/0.56  fof(f85,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f42])).
% 1.61/0.56  fof(f42,plain,(
% 1.61/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.61/0.56    inference(ennf_transformation,[],[f4])).
% 1.61/0.56  fof(f4,axiom,(
% 1.61/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.61/0.56  fof(f671,plain,(
% 1.61/0.56    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_23),
% 1.61/0.56    inference(avatar_component_clause,[],[f669])).
% 1.61/0.56  fof(f1840,plain,(
% 1.61/0.56    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | (~spl2_3 | ~spl2_22 | ~spl2_26 | ~spl2_31)),
% 1.61/0.56    inference(forward_demodulation,[],[f1803,f1831])).
% 1.61/0.56  fof(f1831,plain,(
% 1.61/0.56    k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_22 | ~spl2_26 | ~spl2_31)),
% 1.61/0.56    inference(backward_demodulation,[],[f845,f1830])).
% 1.61/0.56  fof(f1830,plain,(
% 1.61/0.56    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_26 | ~spl2_31)),
% 1.61/0.56    inference(forward_demodulation,[],[f1817,f865])).
% 1.61/0.56  fof(f865,plain,(
% 1.61/0.56    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_31),
% 1.61/0.56    inference(avatar_component_clause,[],[f863])).
% 1.61/0.56  fof(f863,plain,(
% 1.61/0.56    spl2_31 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.61/0.56  fof(f1817,plain,(
% 1.61/0.56    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_26)),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f743,f124,f356])).
% 1.61/0.56  fof(f356,plain,(
% 1.61/0.56    ( ! [X4,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k3_tarski(k2_tarski(X3,X4)) = k4_subset_1(X2,X3,X4) | ~r1_tarski(X4,X2)) )),
% 1.61/0.56    inference(resolution,[],[f109,f90])).
% 1.61/0.56  fof(f90,plain,(
% 1.61/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f60])).
% 1.61/0.56  fof(f109,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(definition_unfolding,[],[f96,f81])).
% 1.61/0.56  fof(f96,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f54])).
% 1.61/0.56  fof(f54,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(flattening,[],[f53])).
% 1.61/0.56  fof(f53,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.61/0.56    inference(ennf_transformation,[],[f18])).
% 1.61/0.56  fof(f18,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.61/0.56  fof(f743,plain,(
% 1.61/0.56    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_26),
% 1.61/0.56    inference(avatar_component_clause,[],[f741])).
% 1.61/0.56  fof(f741,plain,(
% 1.61/0.56    spl2_26 <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.61/0.56  fof(f845,plain,(
% 1.61/0.56    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) | ~spl2_22),
% 1.61/0.56    inference(forward_demodulation,[],[f814,f101])).
% 1.61/0.56  fof(f101,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.61/0.56    inference(definition_unfolding,[],[f79,f81,f81])).
% 1.61/0.56  fof(f79,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f1])).
% 1.61/0.56  fof(f1,axiom,(
% 1.61/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.61/0.56  fof(f814,plain,(
% 1.61/0.56    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) | ~spl2_22),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f110,f659,f109])).
% 1.61/0.56  fof(f1803,plain,(
% 1.61/0.56    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) | ~spl2_22),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f128,f659,f356])).
% 1.61/0.56  fof(f128,plain,(
% 1.61/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f110,f89])).
% 1.61/0.56  fof(f866,plain,(
% 1.61/0.56    spl2_31 | ~spl2_2 | ~spl2_3),
% 1.61/0.56    inference(avatar_split_clause,[],[f371,f122,f117,f863])).
% 1.61/0.56  fof(f117,plain,(
% 1.61/0.56    spl2_2 <=> l1_pre_topc(sK0)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.61/0.56  fof(f371,plain,(
% 1.61/0.56    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f119,f124,f72])).
% 1.61/0.56  fof(f72,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f36])).
% 1.61/0.56  fof(f36,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f27])).
% 1.61/0.56  fof(f27,axiom,(
% 1.61/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 1.61/0.56  fof(f119,plain,(
% 1.61/0.56    l1_pre_topc(sK0) | ~spl2_2),
% 1.61/0.56    inference(avatar_component_clause,[],[f117])).
% 1.61/0.56  fof(f852,plain,(
% 1.61/0.56    ~spl2_3 | ~spl2_22 | spl2_27 | ~spl2_29),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f851])).
% 1.61/0.56  fof(f851,plain,(
% 1.61/0.56    $false | (~spl2_3 | ~spl2_22 | spl2_27 | ~spl2_29)),
% 1.61/0.56    inference(subsumption_resolution,[],[f850,f760])).
% 1.61/0.56  fof(f760,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | spl2_27),
% 1.61/0.56    inference(avatar_component_clause,[],[f758])).
% 1.61/0.56  fof(f758,plain,(
% 1.61/0.56    spl2_27 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 1.61/0.56  fof(f796,plain,(
% 1.61/0.56    spl2_29 | ~spl2_2 | ~spl2_3),
% 1.61/0.56    inference(avatar_split_clause,[],[f375,f122,f117,f793])).
% 1.61/0.56  fof(f375,plain,(
% 1.61/0.56    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f119,f124,f73])).
% 1.61/0.56  fof(f73,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f37])).
% 1.61/0.56  fof(f37,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f29])).
% 1.61/0.56  fof(f29,axiom,(
% 1.61/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 1.61/0.56  fof(f773,plain,(
% 1.61/0.56    spl2_5 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_9),
% 1.61/0.56    inference(avatar_split_clause,[],[f667,f389,f122,f117,f112,f155])).
% 1.61/0.56  fof(f155,plain,(
% 1.61/0.56    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.61/0.56  fof(f112,plain,(
% 1.61/0.56    spl2_1 <=> v2_pre_topc(sK0)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.61/0.56  fof(f667,plain,(
% 1.61/0.56    v4_pre_topc(sK1,sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_9)),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f119,f114,f124,f390,f75])).
% 1.61/0.56  fof(f75,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f39])).
% 1.61/0.56  fof(f39,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.56    inference(flattening,[],[f38])).
% 1.61/0.56  fof(f38,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f24])).
% 1.61/0.56  fof(f24,axiom,(
% 1.61/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.61/0.56  fof(f390,plain,(
% 1.61/0.56    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_9),
% 1.61/0.56    inference(avatar_component_clause,[],[f389])).
% 1.61/0.56  fof(f114,plain,(
% 1.61/0.56    v2_pre_topc(sK0) | ~spl2_1),
% 1.61/0.56    inference(avatar_component_clause,[],[f112])).
% 1.61/0.56  fof(f761,plain,(
% 1.61/0.56    ~spl2_5 | ~spl2_27 | ~spl2_3 | ~spl2_16),
% 1.61/0.56    inference(avatar_split_clause,[],[f747,f450,f122,f758,f155])).
% 1.61/0.56  fof(f747,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_16)),
% 1.61/0.56    inference(forward_demodulation,[],[f746,f545])).
% 1.61/0.56  fof(f545,plain,(
% 1.61/0.56    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_16),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f452,f255])).
% 1.61/0.56  fof(f746,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_3),
% 1.61/0.56    inference(forward_demodulation,[],[f65,f273])).
% 1.61/0.56  fof(f65,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.61/0.56    inference(cnf_transformation,[],[f59])).
% 1.61/0.56  fof(f59,plain,(
% 1.61/0.56    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f56,f58,f57])).
% 1.61/0.56  fof(f57,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f58,plain,(
% 1.61/0.56    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f56,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.61/0.56    inference(flattening,[],[f55])).
% 1.61/0.56  fof(f55,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.61/0.56    inference(nnf_transformation,[],[f33])).
% 1.61/0.56  fof(f33,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.61/0.56    inference(flattening,[],[f32])).
% 1.61/0.56  fof(f32,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f31])).
% 1.61/0.56  fof(f31,negated_conjecture,(
% 1.61/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.61/0.56    inference(negated_conjecture,[],[f30])).
% 1.61/0.56  fof(f30,conjecture,(
% 1.61/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 1.61/0.56  fof(f744,plain,(
% 1.61/0.56    spl2_26 | ~spl2_4 | ~spl2_23),
% 1.61/0.56    inference(avatar_split_clause,[],[f675,f669,f133,f741])).
% 1.61/0.56  fof(f133,plain,(
% 1.61/0.56    spl2_4 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.61/0.56  fof(f675,plain,(
% 1.61/0.56    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_4 | ~spl2_23)),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f135,f671,f95])).
% 1.61/0.56  fof(f95,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f52])).
% 1.61/0.56  fof(f52,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.61/0.56    inference(flattening,[],[f51])).
% 1.61/0.56  fof(f51,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.61/0.56    inference(ennf_transformation,[],[f6])).
% 1.61/0.56  fof(f6,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.61/0.56  fof(f135,plain,(
% 1.61/0.56    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_4),
% 1.61/0.56    inference(avatar_component_clause,[],[f133])).
% 1.61/0.56  fof(f685,plain,(
% 1.61/0.56    spl2_22 | ~spl2_23),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f684])).
% 1.61/0.56  fof(f684,plain,(
% 1.61/0.56    $false | (spl2_22 | ~spl2_23)),
% 1.61/0.56    inference(subsumption_resolution,[],[f681,f658])).
% 1.61/0.56  fof(f658,plain,(
% 1.61/0.56    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_22),
% 1.61/0.56    inference(avatar_component_clause,[],[f657])).
% 1.61/0.56  fof(f681,plain,(
% 1.61/0.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_23),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f671,f90])).
% 1.61/0.56  fof(f672,plain,(
% 1.61/0.56    spl2_23 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 1.61/0.56    inference(avatar_split_clause,[],[f664,f155,f122,f117,f669])).
% 1.61/0.56  fof(f664,plain,(
% 1.61/0.56    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f119,f124,f157,f76])).
% 1.61/0.56  fof(f76,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f41])).
% 1.61/0.56  fof(f41,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.56    inference(flattening,[],[f40])).
% 1.61/0.56  fof(f40,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f28])).
% 1.61/0.56  fof(f28,axiom,(
% 1.61/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 1.61/0.56  fof(f157,plain,(
% 1.61/0.56    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 1.61/0.56    inference(avatar_component_clause,[],[f155])).
% 1.61/0.56  fof(f660,plain,(
% 1.61/0.56    spl2_22 | ~spl2_3 | ~spl2_6 | ~spl2_16),
% 1.61/0.56    inference(avatar_split_clause,[],[f649,f450,f159,f122,f657])).
% 1.61/0.56  fof(f159,plain,(
% 1.61/0.56    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.61/0.56  fof(f649,plain,(
% 1.61/0.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_3 | ~spl2_6 | ~spl2_16)),
% 1.61/0.56    inference(backward_demodulation,[],[f536,f648])).
% 1.61/0.56  fof(f648,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6 | ~spl2_16)),
% 1.61/0.56    inference(backward_demodulation,[],[f545,f646])).
% 1.61/0.56  fof(f646,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 1.61/0.56    inference(superposition,[],[f273,f161])).
% 1.61/0.56  fof(f161,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 1.61/0.56    inference(avatar_component_clause,[],[f159])).
% 1.61/0.56  fof(f536,plain,(
% 1.61/0.56    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl2_16),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f452,f86])).
% 1.61/0.56  fof(f453,plain,(
% 1.61/0.56    spl2_16 | ~spl2_7),
% 1.61/0.56    inference(avatar_split_clause,[],[f340,f278,f450])).
% 1.61/0.56  fof(f278,plain,(
% 1.61/0.56    spl2_7 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.61/0.56  fof(f340,plain,(
% 1.61/0.56    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_7),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f280,f90])).
% 1.61/0.56  fof(f280,plain,(
% 1.61/0.56    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_7),
% 1.61/0.56    inference(avatar_component_clause,[],[f278])).
% 1.61/0.56  fof(f281,plain,(
% 1.61/0.56    spl2_7 | ~spl2_2 | ~spl2_3),
% 1.61/0.56    inference(avatar_split_clause,[],[f192,f122,f117,f278])).
% 1.61/0.56  fof(f192,plain,(
% 1.61/0.56    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3)),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f119,f124,f70])).
% 1.61/0.56  fof(f70,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f34])).
% 1.61/0.56  fof(f34,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f25])).
% 1.61/0.56  fof(f25,axiom,(
% 1.61/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.61/0.56  fof(f162,plain,(
% 1.61/0.56    spl2_5 | spl2_6),
% 1.61/0.56    inference(avatar_split_clause,[],[f64,f159,f155])).
% 1.61/0.56  fof(f64,plain,(
% 1.61/0.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.61/0.56    inference(cnf_transformation,[],[f59])).
% 1.61/0.56  fof(f136,plain,(
% 1.61/0.56    spl2_4 | ~spl2_3),
% 1.61/0.56    inference(avatar_split_clause,[],[f126,f122,f133])).
% 1.61/0.56  fof(f126,plain,(
% 1.61/0.56    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f124,f89])).
% 1.61/0.56  fof(f125,plain,(
% 1.61/0.56    spl2_3),
% 1.61/0.56    inference(avatar_split_clause,[],[f63,f122])).
% 1.61/0.56  fof(f63,plain,(
% 1.61/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.56    inference(cnf_transformation,[],[f59])).
% 1.61/0.56  fof(f120,plain,(
% 1.61/0.56    spl2_2),
% 1.61/0.56    inference(avatar_split_clause,[],[f62,f117])).
% 1.61/0.56  fof(f62,plain,(
% 1.61/0.56    l1_pre_topc(sK0)),
% 1.61/0.56    inference(cnf_transformation,[],[f59])).
% 1.61/0.56  fof(f115,plain,(
% 1.61/0.56    spl2_1),
% 1.61/0.56    inference(avatar_split_clause,[],[f61,f112])).
% 1.61/0.56  fof(f61,plain,(
% 1.61/0.56    v2_pre_topc(sK0)),
% 1.61/0.56    inference(cnf_transformation,[],[f59])).
% 1.61/0.56  % SZS output end Proof for theBenchmark
% 1.61/0.56  % (10104)------------------------------
% 1.61/0.56  % (10104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.56  % (10104)Termination reason: Refutation
% 1.61/0.56  
% 1.61/0.56  % (10104)Memory used [KB]: 11897
% 1.61/0.56  % (10104)Time elapsed: 0.133 s
% 1.61/0.56  % (10104)------------------------------
% 1.61/0.56  % (10104)------------------------------
% 1.61/0.57  % (10088)Success in time 0.216 s
%------------------------------------------------------------------------------
