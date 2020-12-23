%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 774 expanded)
%              Number of leaves         :   30 ( 237 expanded)
%              Depth                    :   16
%              Number of atoms          :  299 (1405 expanded)
%              Number of equality atoms :  113 ( 765 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f989,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f99,f108,f137,f148,f187,f677,f687,f732,f982])).

fof(f982,plain,
    ( spl2_3
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(avatar_contradiction_clause,[],[f981])).

fof(f981,plain,
    ( $false
    | spl2_3
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f980,f97])).

fof(f97,plain,
    ( sK0 != sK1
    | spl2_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f980,plain,
    ( sK0 = sK1
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f979,f953])).

fof(f953,plain,
    ( sK0 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(backward_demodulation,[],[f686,f948])).

% (12502)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f948,plain,
    ( sK0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f947,f310])).

fof(f310,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f305,f111])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f81,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f305,plain,(
    ! [X3] : k5_xboole_0(X3,k4_xboole_0(X3,X3)) = X3 ),
    inference(superposition,[],[f71,f124])).

fof(f124,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f121,f111])).

fof(f121,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f81,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f947,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f929,f769])).

fof(f769,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f731,f64])).

fof(f731,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f729])).

fof(f729,plain,
    ( spl2_22
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f929,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl2_19 ),
    inference(superposition,[],[f469,f686])).

fof(f469,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k4_xboole_0(X7,X6)) = k5_xboole_0(X7,k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f188,f79])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f188,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(superposition,[],[f79,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f47,f68,f68])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f686,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f684])).

fof(f684,plain,
    ( spl2_19
  <=> k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f979,plain,
    ( sK1 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f978,f956])).

fof(f956,plain,
    ( sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(backward_demodulation,[],[f726,f948])).

fof(f726,plain,
    ( sK1 = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f725,f310])).

fof(f725,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f724,f721])).

fof(f721,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1)
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f709,f300])).

fof(f300,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f296,f124])).

fof(f296,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f71,f111])).

fof(f709,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl2_17 ),
    inference(superposition,[],[f173,f676])).

fof(f676,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f674])).

fof(f674,plain,
    ( spl2_17
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f173,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f71,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f48,f54,f54])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f724,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f714,f79])).

fof(f714,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl2_17 ),
    inference(superposition,[],[f188,f676])).

fof(f978,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f934,f948])).

fof(f934,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl2_17 ),
    inference(superposition,[],[f469,f676])).

fof(f732,plain,
    ( spl2_22
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f669,f87,f729])).

fof(f87,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f669,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f89,f317])).

fof(f317,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | r1_tarski(X3,X2) ) ),
    inference(subsumption_resolution,[],[f316,f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f75,f74])).

fof(f74,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f316,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f312,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f312,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1(X2,X3))
      | r1_tarski(X3,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f59,f131])).

fof(f131,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f126,f111])).

fof(f126,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f85,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f89,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f687,plain,
    ( spl2_19
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f376,f184,f684])).

fof(f184,plain,
    ( spl2_7
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f376,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f367,f124])).

fof(f367,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))
    | ~ spl2_7 ),
    inference(superposition,[],[f173,f186])).

fof(f186,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f184])).

fof(f677,plain,
    ( spl2_17
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f258,f184,f674])).

fof(f258,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f252,f124])).

fof(f252,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl2_7 ),
    inference(superposition,[],[f77,f186])).

fof(f187,plain,
    ( spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f150,f145,f184])).

fof(f145,plain,
    ( spl2_5
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f150,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f147,f64])).

fof(f147,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f148,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f143,f92,f87,f145])).

fof(f92,plain,
    ( spl2_2
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f143,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f94,f141])).

fof(f141,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f89,f56])).

fof(f94,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f137,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f133,f41])).

fof(f133,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_4 ),
    inference(backward_demodulation,[],[f107,f131])).

fof(f107,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_4
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f108,plain,
    ( ~ spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f102,f96,f105])).

fof(f102,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f101,f98])).

fof(f98,plain,
    ( sK0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f101,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | sK0 != sK1
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f84,f98])).

fof(f84,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f72,f74])).

fof(f72,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f40,f70])).

fof(f40,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f99,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f83,f96,f92])).

fof(f83,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f73,f74])).

fof(f73,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f39,f70])).

fof(f39,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:17:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (12513)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.48  % (12501)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (12496)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (12513)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f989,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f90,f99,f108,f137,f148,f187,f677,f687,f732,f982])).
% 0.22/0.53  fof(f982,plain,(
% 0.22/0.53    spl2_3 | ~spl2_17 | ~spl2_19 | ~spl2_22),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f981])).
% 0.22/0.53  fof(f981,plain,(
% 0.22/0.53    $false | (spl2_3 | ~spl2_17 | ~spl2_19 | ~spl2_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f980,f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    sK0 != sK1 | spl2_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl2_3 <=> sK0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.53  fof(f980,plain,(
% 0.22/0.53    sK0 = sK1 | (~spl2_17 | ~spl2_19 | ~spl2_22)),
% 0.22/0.53    inference(forward_demodulation,[],[f979,f953])).
% 0.22/0.53  fof(f953,plain,(
% 0.22/0.53    sK0 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | (~spl2_19 | ~spl2_22)),
% 0.22/0.53    inference(backward_demodulation,[],[f686,f948])).
% 0.22/0.53  % (12502)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  fof(f948,plain,(
% 0.22/0.53    sK0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | (~spl2_19 | ~spl2_22)),
% 0.22/0.53    inference(forward_demodulation,[],[f947,f310])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = X3) )),
% 0.22/0.53    inference(forward_demodulation,[],[f305,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f81,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(nnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    ( ! [X3] : (k5_xboole_0(X3,k4_xboole_0(X3,X3)) = X3) )),
% 0.22/0.53    inference(superposition,[],[f71,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(forward_demodulation,[],[f121,f111])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f81,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f55,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f53,f54])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.53  fof(f947,plain,(
% 0.22/0.53    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) | (~spl2_19 | ~spl2_22)),
% 0.22/0.53    inference(forward_demodulation,[],[f929,f769])).
% 0.22/0.53  fof(f769,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_22),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f731,f64])).
% 0.22/0.53  fof(f731,plain,(
% 0.22/0.53    r1_tarski(sK1,sK0) | ~spl2_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f729])).
% 0.22/0.53  fof(f729,plain,(
% 0.22/0.53    spl2_22 <=> r1_tarski(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.53  fof(f929,plain,(
% 0.22/0.53    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl2_19),
% 0.22/0.53    inference(superposition,[],[f469,f686])).
% 0.22/0.53  fof(f469,plain,(
% 0.22/0.53    ( ! [X6,X7] : (k5_xboole_0(X6,k4_xboole_0(X7,X6)) = k5_xboole_0(X7,k4_xboole_0(X6,X7))) )),
% 0.22/0.53    inference(superposition,[],[f188,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f52,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f50,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f51,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f65,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.22/0.53    inference(superposition,[],[f79,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f47,f68,f68])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.53  fof(f686,plain,(
% 0.22/0.53    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl2_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f684])).
% 0.22/0.53  fof(f684,plain,(
% 0.22/0.53    spl2_19 <=> k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.53  fof(f979,plain,(
% 0.22/0.53    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | (~spl2_17 | ~spl2_19 | ~spl2_22)),
% 0.22/0.53    inference(forward_demodulation,[],[f978,f956])).
% 0.22/0.53  fof(f956,plain,(
% 0.22/0.53    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_17 | ~spl2_19 | ~spl2_22)),
% 0.22/0.53    inference(backward_demodulation,[],[f726,f948])).
% 0.22/0.53  fof(f726,plain,(
% 0.22/0.53    sK1 = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl2_17),
% 0.22/0.53    inference(forward_demodulation,[],[f725,f310])).
% 0.22/0.53  fof(f725,plain,(
% 0.22/0.53    k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl2_17),
% 0.22/0.53    inference(forward_demodulation,[],[f724,f721])).
% 0.22/0.53  fof(f721,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1) | ~spl2_17),
% 0.22/0.53    inference(forward_demodulation,[],[f709,f300])).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f296,f124])).
% 0.22/0.53  fof(f296,plain,(
% 0.22/0.53    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) )),
% 0.22/0.53    inference(superposition,[],[f71,f111])).
% 0.22/0.53  fof(f709,plain,(
% 0.22/0.53    k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~spl2_17),
% 0.22/0.53    inference(superposition,[],[f173,f676])).
% 0.22/0.53  fof(f676,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~spl2_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f674])).
% 0.22/0.53  fof(f674,plain,(
% 0.22/0.53    spl2_17 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.22/0.53    inference(superposition,[],[f71,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f48,f54,f54])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.53  fof(f724,plain,(
% 0.22/0.53    k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl2_17),
% 0.22/0.53    inference(forward_demodulation,[],[f714,f79])).
% 0.22/0.53  fof(f714,plain,(
% 0.22/0.53    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl2_17),
% 0.22/0.53    inference(superposition,[],[f188,f676])).
% 0.22/0.53  fof(f978,plain,(
% 0.22/0.53    k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_17 | ~spl2_19 | ~spl2_22)),
% 0.22/0.53    inference(forward_demodulation,[],[f934,f948])).
% 0.22/0.53  fof(f934,plain,(
% 0.22/0.53    k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl2_17),
% 0.22/0.53    inference(superposition,[],[f469,f676])).
% 0.22/0.53  fof(f732,plain,(
% 0.22/0.53    spl2_22 | ~spl2_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f669,f87,f729])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.53  fof(f669,plain,(
% 0.22/0.53    r1_tarski(sK1,sK0) | ~spl2_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f89,f317])).
% 0.22/0.53  fof(f317,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | r1_tarski(X3,X2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f316,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f75,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f43,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f46,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,axiom,(
% 0.22/0.53    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,axiom,(
% 0.22/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f45,f70])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.53  fof(f316,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r1_tarski(X3,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f312,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f312,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~r1_tarski(k1_xboole_0,k3_subset_1(X2,X3)) | r1_tarski(X3,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 0.22/0.53    inference(superposition,[],[f59,f131])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f126,f111])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f85,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f687,plain,(
% 0.22/0.53    spl2_19 | ~spl2_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f376,f184,f684])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    spl2_7 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.53  fof(f376,plain,(
% 0.22/0.53    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl2_7),
% 0.22/0.53    inference(forward_demodulation,[],[f367,f124])).
% 0.22/0.53  fof(f367,plain,(
% 0.22/0.53    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) | ~spl2_7),
% 0.22/0.53    inference(superposition,[],[f173,f186])).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) | ~spl2_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f184])).
% 0.22/0.53  fof(f677,plain,(
% 0.22/0.53    spl2_17 | ~spl2_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f258,f184,f674])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~spl2_7),
% 0.22/0.53    inference(forward_demodulation,[],[f252,f124])).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl2_7),
% 0.22/0.53    inference(superposition,[],[f77,f186])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    spl2_7 | ~spl2_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f150,f145,f184])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    spl2_5 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) | ~spl2_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f147,f64])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | ~spl2_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f145])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl2_5 | ~spl2_1 | ~spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f143,f92,f87,f145])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl2_2 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | (~spl2_1 | ~spl2_2)),
% 0.22/0.53    inference(backward_demodulation,[],[f94,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f89,f56])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl2_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f92])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl2_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f136])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    $false | spl2_4),
% 0.22/0.53    inference(subsumption_resolution,[],[f133,f41])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,sK0) | spl2_4),
% 0.22/0.53    inference(backward_demodulation,[],[f107,f131])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl2_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl2_4 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ~spl2_4 | ~spl2_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f102,f96,f105])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl2_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f101,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    sK0 = sK1 | ~spl2_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f96])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | sK0 != sK1 | ~spl2_3),
% 0.22/0.53    inference(backward_demodulation,[],[f84,f98])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.53    inference(backward_demodulation,[],[f72,f74])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.53    inference(definition_unfolding,[],[f40,f70])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f23])).
% 0.22/0.53  fof(f23,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl2_2 | spl2_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f83,f96,f92])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.53    inference(backward_demodulation,[],[f73,f74])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.53    inference(definition_unfolding,[],[f39,f70])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    spl2_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f87])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (12513)------------------------------
% 0.22/0.53  % (12513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12513)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (12513)Memory used [KB]: 11257
% 0.22/0.53  % (12513)Time elapsed: 0.089 s
% 0.22/0.53  % (12513)------------------------------
% 0.22/0.53  % (12513)------------------------------
% 0.22/0.53  % (12492)Success in time 0.169 s
%------------------------------------------------------------------------------
