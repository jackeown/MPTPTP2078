%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:51 EST 2020

% Result     : Theorem 8.51s
% Output     : Refutation 8.51s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 439 expanded)
%              Number of leaves         :   35 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  297 ( 714 expanded)
%              Number of equality atoms :  109 ( 362 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6333,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f115,f120,f356,f619,f5002,f5476,f6153,f6332])).

fof(f6332,plain,
    ( ~ spl2_1
    | spl2_13
    | ~ spl2_26
    | ~ spl2_27 ),
    inference(avatar_contradiction_clause,[],[f6331])).

fof(f6331,plain,
    ( $false
    | ~ spl2_1
    | spl2_13
    | ~ spl2_26
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f6324,f251])).

fof(f251,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f239,f98])).

fof(f98,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f95])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f81,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f86,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f87,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f88,f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f239,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(unit_resulting_resolution,[],[f104,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f80,f96])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f69,f95])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f6324,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | ~ spl2_1
    | spl2_13
    | ~ spl2_26
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f618,f6321])).

fof(f6321,plain,
    ( sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_26
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f6320,f5475])).

fof(f5475,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f5473])).

fof(f5473,plain,
    ( spl2_26
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f6320,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_27 ),
    inference(superposition,[],[f148,f6152])).

fof(f6152,plain,
    ( k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f6150])).

fof(f6150,plain,
    ( spl2_27
  <=> k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f148,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f121,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f121,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f109,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f109,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f618,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl2_13
  <=> k1_xboole_0 = k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f6153,plain,
    ( spl2_27
    | ~ spl2_1
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f5697,f5473,f107,f6150])).

fof(f5697,plain,
    ( k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f5680,f210])).

fof(f210,plain,
    ( ! [X0] : k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f109,f104,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f5680,plain,
    ( k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_26 ),
    inference(superposition,[],[f156,f5475])).

fof(f156,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f121,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f5476,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f5276,f4999,f107,f5473])).

fof(f4999,plain,
    ( spl2_25
  <=> r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f5276,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f5275,f270])).

fof(f270,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f269,f251])).

fof(f269,plain,(
    ! [X0] : k2_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f257,f98])).

fof(f257,plain,(
    ! [X0] : k2_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(unit_resulting_resolution,[],[f104,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 ) ),
    inference(definition_unfolding,[],[f75,f96])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f5275,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f5236,f241])).

fof(f241,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),X0)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f127,f100])).

fof(f127,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f109,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f5236,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k2_xboole_0(sK0,k5_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),sK0))))
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f5001,f99])).

fof(f5001,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f4999])).

fof(f5002,plain,
    ( spl2_25
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f4860,f353,f107,f4999])).

fof(f353,plain,
    ( spl2_4
  <=> k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f4860,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f4822,f145])).

fof(f145,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f144,f59])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f144,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f140,f60])).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f140,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f57,f61])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f4822,plain,
    ( ! [X50] : r1_tarski(k10_relat_1(k6_relat_1(X50),sK0),k1_relat_1(k7_relat_1(sK1,X50)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f4798,f205])).

fof(f205,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f187,f170])).

fof(f170,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f109,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f187,plain,
    ( ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f57,f109,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f4798,plain,
    ( ! [X50] : r1_tarski(k10_relat_1(k6_relat_1(X50),sK0),k10_relat_1(k6_relat_1(X50),k1_relat_1(sK1)))
    | ~ spl2_4 ),
    inference(superposition,[],[f1038,f355])).

fof(f355,plain,
    ( k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f353])).

fof(f1038,plain,(
    ! [X4,X2,X3] : r1_tarski(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f66,f233])).

fof(f233,plain,(
    ! [X2,X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(unit_resulting_resolution,[],[f57,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f619,plain,
    ( ~ spl2_13
    | ~ spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f323,f117,f107,f616])).

fof(f117,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f323,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))
    | ~ spl2_1
    | spl2_3 ),
    inference(backward_demodulation,[],[f253,f313])).

fof(f313,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f109,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f82,f95])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f253,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f119,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f96])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f119,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f356,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f132,f112,f353])).

fof(f112,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f132,plain,
    ( k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f114,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f114,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f120,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f49])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f115,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f110,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (18236)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.48  % (18244)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (18232)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (18256)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (18231)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.55  % (18251)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (18243)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.62/0.56  % (18235)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.57  % (18255)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.62/0.57  % (18247)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.62/0.57  % (18248)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.62/0.57  % (18240)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.62/0.57  % (18252)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.62/0.58  % (18239)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.62/0.58  % (18239)Refutation not found, incomplete strategy% (18239)------------------------------
% 1.62/0.58  % (18239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (18239)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (18239)Memory used [KB]: 10746
% 1.62/0.58  % (18239)Time elapsed: 0.178 s
% 1.62/0.58  % (18239)------------------------------
% 1.62/0.58  % (18239)------------------------------
% 1.62/0.58  % (18229)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.62/0.59  % (18233)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.62/0.59  % (18241)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.84/0.59  % (18230)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.84/0.60  % (18237)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.84/0.60  % (18245)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.84/0.60  % (18257)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.84/0.60  % (18253)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.84/0.60  % (18245)Refutation not found, incomplete strategy% (18245)------------------------------
% 1.84/0.60  % (18245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (18245)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.60  
% 1.84/0.60  % (18245)Memory used [KB]: 10618
% 1.84/0.60  % (18245)Time elapsed: 0.176 s
% 1.84/0.60  % (18245)------------------------------
% 1.84/0.60  % (18245)------------------------------
% 1.84/0.60  % (18257)Refutation not found, incomplete strategy% (18257)------------------------------
% 1.84/0.60  % (18257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (18257)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.60  
% 1.84/0.60  % (18257)Memory used [KB]: 10746
% 1.84/0.60  % (18257)Time elapsed: 0.190 s
% 1.84/0.60  % (18257)------------------------------
% 1.84/0.60  % (18257)------------------------------
% 1.84/0.61  % (18254)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.84/0.61  % (18249)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.84/0.61  % (18234)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.84/0.62  % (18246)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.84/0.62  % (18258)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.84/0.63  % (18238)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.84/0.63  % (18250)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.84/0.64  % (18232)Refutation not found, incomplete strategy% (18232)------------------------------
% 1.84/0.64  % (18232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.64  % (18242)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.84/0.65  % (18232)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.65  
% 1.84/0.65  % (18232)Memory used [KB]: 6140
% 1.84/0.65  % (18232)Time elapsed: 0.219 s
% 1.84/0.65  % (18232)------------------------------
% 1.84/0.65  % (18232)------------------------------
% 2.90/0.78  % (18286)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.90/0.78  % (18284)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.90/0.79  % (18283)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.90/0.81  % (18231)Time limit reached!
% 2.90/0.81  % (18231)------------------------------
% 2.90/0.81  % (18231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.81  % (18231)Termination reason: Time limit
% 2.90/0.81  
% 2.90/0.81  % (18231)Memory used [KB]: 6652
% 2.90/0.81  % (18231)Time elapsed: 0.409 s
% 2.90/0.81  % (18231)------------------------------
% 2.90/0.81  % (18231)------------------------------
% 2.90/0.82  % (18253)Time limit reached!
% 2.90/0.82  % (18253)------------------------------
% 2.90/0.82  % (18253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.82  % (18253)Termination reason: Time limit
% 2.90/0.82  
% 2.90/0.82  % (18253)Memory used [KB]: 11897
% 2.90/0.82  % (18253)Time elapsed: 0.406 s
% 2.90/0.82  % (18253)------------------------------
% 2.90/0.82  % (18253)------------------------------
% 2.90/0.83  % (18285)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.55/0.86  % (18285)Refutation not found, incomplete strategy% (18285)------------------------------
% 3.55/0.86  % (18285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.86  % (18285)Termination reason: Refutation not found, incomplete strategy
% 3.55/0.86  
% 3.55/0.86  % (18285)Memory used [KB]: 6140
% 3.55/0.86  % (18285)Time elapsed: 0.180 s
% 3.55/0.86  % (18285)------------------------------
% 3.55/0.86  % (18285)------------------------------
% 3.94/0.95  % (18258)Time limit reached!
% 3.94/0.95  % (18258)------------------------------
% 3.94/0.95  % (18258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.94/0.95  % (18258)Termination reason: Time limit
% 3.94/0.95  
% 3.94/0.95  % (18258)Memory used [KB]: 3709
% 3.94/0.95  % (18258)Time elapsed: 0.529 s
% 3.94/0.95  % (18258)------------------------------
% 3.94/0.95  % (18258)------------------------------
% 4.29/0.95  % (18235)Time limit reached!
% 4.29/0.95  % (18235)------------------------------
% 4.29/0.95  % (18235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.29/0.95  % (18235)Termination reason: Time limit
% 4.29/0.95  % (18235)Termination phase: Saturation
% 4.29/0.95  
% 4.29/0.95  % (18235)Memory used [KB]: 14456
% 4.29/0.95  % (18235)Time elapsed: 0.523 s
% 4.29/0.95  % (18235)------------------------------
% 4.29/0.95  % (18235)------------------------------
% 4.38/0.96  % (18243)Time limit reached!
% 4.38/0.96  % (18243)------------------------------
% 4.38/0.96  % (18243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/0.96  % (18243)Termination reason: Time limit
% 4.38/0.96  
% 4.38/0.96  % (18243)Memory used [KB]: 4477
% 4.38/0.96  % (18243)Time elapsed: 0.520 s
% 4.38/0.96  % (18243)------------------------------
% 4.38/0.96  % (18243)------------------------------
% 4.38/0.97  % (18288)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.38/0.99  % (18287)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.60/1.04  % (18236)Time limit reached!
% 4.60/1.04  % (18236)------------------------------
% 4.60/1.04  % (18236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/1.04  % (18236)Termination reason: Time limit
% 4.60/1.04  
% 4.60/1.04  % (18236)Memory used [KB]: 6652
% 4.60/1.04  % (18236)Time elapsed: 0.629 s
% 4.60/1.04  % (18236)------------------------------
% 4.60/1.04  % (18236)------------------------------
% 5.50/1.07  % (18289)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.50/1.14  % (18291)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.25/1.16  % (18292)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 6.25/1.17  % (18290)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.65/1.24  % (18230)Time limit reached!
% 6.65/1.24  % (18230)------------------------------
% 6.65/1.24  % (18230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.65/1.24  % (18230)Termination reason: Time limit
% 6.65/1.24  % (18230)Termination phase: Saturation
% 6.65/1.24  
% 6.65/1.24  % (18230)Memory used [KB]: 5500
% 6.65/1.24  % (18230)Time elapsed: 0.816 s
% 6.65/1.24  % (18230)------------------------------
% 6.65/1.24  % (18230)------------------------------
% 7.00/1.26  % (18293)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 8.00/1.41  % (18294)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 8.00/1.44  % (18241)Time limit reached!
% 8.00/1.44  % (18241)------------------------------
% 8.00/1.44  % (18241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.00/1.44  % (18256)Time limit reached!
% 8.00/1.44  % (18256)------------------------------
% 8.00/1.44  % (18256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.00/1.44  % (18256)Termination reason: Time limit
% 8.00/1.44  % (18256)Termination phase: Saturation
% 8.00/1.44  
% 8.00/1.44  % (18256)Memory used [KB]: 15991
% 8.00/1.44  % (18256)Time elapsed: 1.0000 s
% 8.00/1.44  % (18256)------------------------------
% 8.00/1.44  % (18256)------------------------------
% 8.00/1.44  % (18241)Termination reason: Time limit
% 8.00/1.44  % (18241)Termination phase: Saturation
% 8.00/1.44  
% 8.00/1.44  % (18241)Memory used [KB]: 18421
% 8.00/1.44  % (18241)Time elapsed: 1.0000 s
% 8.00/1.44  % (18241)------------------------------
% 8.00/1.44  % (18241)------------------------------
% 8.51/1.50  % (18249)Refutation found. Thanks to Tanya!
% 8.51/1.50  % SZS status Theorem for theBenchmark
% 8.51/1.50  % SZS output start Proof for theBenchmark
% 8.51/1.50  fof(f6333,plain,(
% 8.51/1.50    $false),
% 8.51/1.50    inference(avatar_sat_refutation,[],[f110,f115,f120,f356,f619,f5002,f5476,f6153,f6332])).
% 8.51/1.50  fof(f6332,plain,(
% 8.51/1.50    ~spl2_1 | spl2_13 | ~spl2_26 | ~spl2_27),
% 8.51/1.50    inference(avatar_contradiction_clause,[],[f6331])).
% 8.51/1.50  fof(f6331,plain,(
% 8.51/1.50    $false | (~spl2_1 | spl2_13 | ~spl2_26 | ~spl2_27)),
% 8.51/1.50    inference(subsumption_resolution,[],[f6324,f251])).
% 8.51/1.50  fof(f251,plain,(
% 8.51/1.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 8.51/1.50    inference(forward_demodulation,[],[f239,f98])).
% 8.51/1.50  fof(f98,plain,(
% 8.51/1.50    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 8.51/1.50    inference(definition_unfolding,[],[f65,f95])).
% 8.51/1.50  fof(f95,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 8.51/1.50    inference(definition_unfolding,[],[f67,f94])).
% 8.51/1.50  fof(f94,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 8.51/1.50    inference(definition_unfolding,[],[f68,f93])).
% 8.51/1.50  fof(f93,plain,(
% 8.51/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 8.51/1.50    inference(definition_unfolding,[],[f81,f92])).
% 8.51/1.50  fof(f92,plain,(
% 8.51/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 8.51/1.50    inference(definition_unfolding,[],[f86,f91])).
% 8.51/1.50  fof(f91,plain,(
% 8.51/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 8.51/1.50    inference(definition_unfolding,[],[f87,f90])).
% 8.51/1.50  fof(f90,plain,(
% 8.51/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 8.51/1.50    inference(definition_unfolding,[],[f88,f89])).
% 8.51/1.50  fof(f89,plain,(
% 8.51/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f16])).
% 8.51/1.50  fof(f16,axiom,(
% 8.51/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 8.51/1.50  fof(f88,plain,(
% 8.51/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f15])).
% 8.51/1.50  fof(f15,axiom,(
% 8.51/1.50    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 8.51/1.50  fof(f87,plain,(
% 8.51/1.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f14])).
% 8.51/1.50  fof(f14,axiom,(
% 8.51/1.50    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 8.51/1.50  fof(f86,plain,(
% 8.51/1.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f13])).
% 8.51/1.50  fof(f13,axiom,(
% 8.51/1.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 8.51/1.50  fof(f81,plain,(
% 8.51/1.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f12])).
% 8.51/1.50  fof(f12,axiom,(
% 8.51/1.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 8.51/1.50  fof(f68,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f11])).
% 8.51/1.50  fof(f11,axiom,(
% 8.51/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 8.51/1.50  fof(f67,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 8.51/1.50    inference(cnf_transformation,[],[f17])).
% 8.51/1.50  fof(f17,axiom,(
% 8.51/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 8.51/1.50  fof(f65,plain,(
% 8.51/1.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 8.51/1.50    inference(cnf_transformation,[],[f32])).
% 8.51/1.50  fof(f32,plain,(
% 8.51/1.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 8.51/1.50    inference(rectify,[],[f1])).
% 8.51/1.50  fof(f1,axiom,(
% 8.51/1.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 8.51/1.50  fof(f239,plain,(
% 8.51/1.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f104,f100])).
% 8.51/1.50  fof(f100,plain,(
% 8.51/1.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 8.51/1.50    inference(definition_unfolding,[],[f80,f96])).
% 8.51/1.50  fof(f96,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 8.51/1.50    inference(definition_unfolding,[],[f69,f95])).
% 8.51/1.50  fof(f69,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.51/1.50    inference(cnf_transformation,[],[f4])).
% 8.51/1.50  fof(f4,axiom,(
% 8.51/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 8.51/1.50  fof(f80,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f53])).
% 8.51/1.50  fof(f53,plain,(
% 8.51/1.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 8.51/1.50    inference(nnf_transformation,[],[f3])).
% 8.51/1.50  fof(f3,axiom,(
% 8.51/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 8.51/1.50  fof(f104,plain,(
% 8.51/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.51/1.50    inference(equality_resolution,[],[f77])).
% 8.51/1.50  fof(f77,plain,(
% 8.51/1.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 8.51/1.50    inference(cnf_transformation,[],[f52])).
% 8.51/1.50  fof(f52,plain,(
% 8.51/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.51/1.50    inference(flattening,[],[f51])).
% 8.51/1.50  fof(f51,plain,(
% 8.51/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.51/1.50    inference(nnf_transformation,[],[f2])).
% 8.51/1.50  fof(f2,axiom,(
% 8.51/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 8.51/1.50  fof(f6324,plain,(
% 8.51/1.50    k1_xboole_0 != k5_xboole_0(sK0,sK0) | (~spl2_1 | spl2_13 | ~spl2_26 | ~spl2_27)),
% 8.51/1.50    inference(backward_demodulation,[],[f618,f6321])).
% 8.51/1.50  fof(f6321,plain,(
% 8.51/1.50    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_26 | ~spl2_27)),
% 8.51/1.50    inference(forward_demodulation,[],[f6320,f5475])).
% 8.51/1.50  fof(f5475,plain,(
% 8.51/1.50    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_26),
% 8.51/1.50    inference(avatar_component_clause,[],[f5473])).
% 8.51/1.50  fof(f5473,plain,(
% 8.51/1.50    spl2_26 <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 8.51/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 8.51/1.50  fof(f6320,plain,(
% 8.51/1.50    k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_27)),
% 8.51/1.50    inference(superposition,[],[f148,f6152])).
% 8.51/1.50  fof(f6152,plain,(
% 8.51/1.50    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_27),
% 8.51/1.50    inference(avatar_component_clause,[],[f6150])).
% 8.51/1.50  fof(f6150,plain,(
% 8.51/1.50    spl2_27 <=> k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 8.51/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 8.51/1.50  fof(f148,plain,(
% 8.51/1.50    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_1),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f121,f61])).
% 8.51/1.50  fof(f61,plain,(
% 8.51/1.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 8.51/1.50    inference(cnf_transformation,[],[f35])).
% 8.51/1.50  fof(f35,plain,(
% 8.51/1.50    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 8.51/1.50    inference(ennf_transformation,[],[f23])).
% 8.51/1.50  fof(f23,axiom,(
% 8.51/1.50    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 8.51/1.50  fof(f121,plain,(
% 8.51/1.50    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_1),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f109,f70])).
% 8.51/1.50  fof(f70,plain,(
% 8.51/1.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f39])).
% 8.51/1.50  fof(f39,plain,(
% 8.51/1.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 8.51/1.50    inference(ennf_transformation,[],[f19])).
% 8.51/1.50  fof(f19,axiom,(
% 8.51/1.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 8.51/1.50  fof(f109,plain,(
% 8.51/1.50    v1_relat_1(sK1) | ~spl2_1),
% 8.51/1.50    inference(avatar_component_clause,[],[f107])).
% 8.51/1.50  fof(f107,plain,(
% 8.51/1.50    spl2_1 <=> v1_relat_1(sK1)),
% 8.51/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 8.51/1.50  fof(f618,plain,(
% 8.51/1.50    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) | spl2_13),
% 8.51/1.50    inference(avatar_component_clause,[],[f616])).
% 8.51/1.50  fof(f616,plain,(
% 8.51/1.50    spl2_13 <=> k1_xboole_0 = k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))),
% 8.51/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 8.51/1.50  fof(f6153,plain,(
% 8.51/1.50    spl2_27 | ~spl2_1 | ~spl2_26),
% 8.51/1.50    inference(avatar_split_clause,[],[f5697,f5473,f107,f6150])).
% 8.51/1.50  fof(f5697,plain,(
% 8.51/1.50    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_26)),
% 8.51/1.50    inference(forward_demodulation,[],[f5680,f210])).
% 8.51/1.50  fof(f210,plain,(
% 8.51/1.50    ( ! [X0] : (k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0)) ) | ~spl2_1),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f109,f104,f64])).
% 8.51/1.50  fof(f64,plain,(
% 8.51/1.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f38])).
% 8.51/1.50  fof(f38,plain,(
% 8.51/1.50    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 8.51/1.50    inference(ennf_transformation,[],[f21])).
% 8.51/1.50  fof(f21,axiom,(
% 8.51/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 8.51/1.50  fof(f5680,plain,(
% 8.51/1.50    k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_26)),
% 8.51/1.50    inference(superposition,[],[f156,f5475])).
% 8.51/1.50  fof(f156,plain,(
% 8.51/1.50    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_1),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f121,f62])).
% 8.51/1.50  fof(f62,plain,(
% 8.51/1.50    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f36])).
% 8.51/1.50  fof(f36,plain,(
% 8.51/1.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 8.51/1.50    inference(ennf_transformation,[],[f20])).
% 8.51/1.50  fof(f20,axiom,(
% 8.51/1.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 8.51/1.50  fof(f5476,plain,(
% 8.51/1.50    spl2_26 | ~spl2_1 | ~spl2_25),
% 8.51/1.50    inference(avatar_split_clause,[],[f5276,f4999,f107,f5473])).
% 8.51/1.50  fof(f4999,plain,(
% 8.51/1.50    spl2_25 <=> r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 8.51/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 8.51/1.50  fof(f5276,plain,(
% 8.51/1.50    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_25)),
% 8.51/1.50    inference(forward_demodulation,[],[f5275,f270])).
% 8.51/1.50  fof(f270,plain,(
% 8.51/1.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.51/1.50    inference(forward_demodulation,[],[f269,f251])).
% 8.51/1.50  fof(f269,plain,(
% 8.51/1.50    ( ! [X0] : (k2_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 8.51/1.50    inference(forward_demodulation,[],[f257,f98])).
% 8.51/1.50  fof(f257,plain,(
% 8.51/1.50    ( ! [X0] : (k2_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0) )),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f104,f99])).
% 8.51/1.50  fof(f99,plain,(
% 8.51/1.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1) )),
% 8.51/1.50    inference(definition_unfolding,[],[f75,f96])).
% 8.51/1.50  fof(f75,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f44])).
% 8.51/1.50  fof(f44,plain,(
% 8.51/1.50    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 8.51/1.50    inference(ennf_transformation,[],[f8])).
% 8.51/1.50  fof(f8,axiom,(
% 8.51/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 8.51/1.50  fof(f5275,plain,(
% 8.51/1.50    k2_xboole_0(sK0,k1_xboole_0) = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_25)),
% 8.51/1.50    inference(forward_demodulation,[],[f5236,f241])).
% 8.51/1.50  fof(f241,plain,(
% 8.51/1.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),X0)))) ) | ~spl2_1),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f127,f100])).
% 8.51/1.50  fof(f127,plain,(
% 8.51/1.50    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) ) | ~spl2_1),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f109,f72])).
% 8.51/1.50  fof(f72,plain,(
% 8.51/1.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f41])).
% 8.51/1.50  fof(f41,plain,(
% 8.51/1.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 8.51/1.50    inference(ennf_transformation,[],[f27])).
% 8.51/1.50  fof(f27,axiom,(
% 8.51/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 8.51/1.50  fof(f5236,plain,(
% 8.51/1.50    k1_relat_1(k7_relat_1(sK1,sK0)) = k2_xboole_0(sK0,k5_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),sK0)))) | ~spl2_25),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f5001,f99])).
% 8.51/1.50  fof(f5001,plain,(
% 8.51/1.50    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~spl2_25),
% 8.51/1.50    inference(avatar_component_clause,[],[f4999])).
% 8.51/1.50  fof(f5002,plain,(
% 8.51/1.50    spl2_25 | ~spl2_1 | ~spl2_4),
% 8.51/1.50    inference(avatar_split_clause,[],[f4860,f353,f107,f4999])).
% 8.51/1.50  fof(f353,plain,(
% 8.51/1.50    spl2_4 <=> k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1))),
% 8.51/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 8.51/1.50  fof(f4860,plain,(
% 8.51/1.50    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | (~spl2_1 | ~spl2_4)),
% 8.51/1.50    inference(superposition,[],[f4822,f145])).
% 8.51/1.50  fof(f145,plain,(
% 8.51/1.50    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 8.51/1.50    inference(forward_demodulation,[],[f144,f59])).
% 8.51/1.50  fof(f59,plain,(
% 8.51/1.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 8.51/1.50    inference(cnf_transformation,[],[f26])).
% 8.51/1.50  fof(f26,axiom,(
% 8.51/1.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 8.51/1.50  fof(f144,plain,(
% 8.51/1.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 8.51/1.50    inference(forward_demodulation,[],[f140,f60])).
% 8.51/1.50  fof(f60,plain,(
% 8.51/1.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 8.51/1.50    inference(cnf_transformation,[],[f26])).
% 8.51/1.50  fof(f140,plain,(
% 8.51/1.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f57,f61])).
% 8.51/1.50  fof(f57,plain,(
% 8.51/1.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 8.51/1.50    inference(cnf_transformation,[],[f18])).
% 8.51/1.50  fof(f18,axiom,(
% 8.51/1.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 8.51/1.50  fof(f4822,plain,(
% 8.51/1.50    ( ! [X50] : (r1_tarski(k10_relat_1(k6_relat_1(X50),sK0),k1_relat_1(k7_relat_1(sK1,X50)))) ) | (~spl2_1 | ~spl2_4)),
% 8.51/1.50    inference(forward_demodulation,[],[f4798,f205])).
% 8.51/1.50  fof(f205,plain,(
% 8.51/1.50    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) ) | ~spl2_1),
% 8.51/1.50    inference(forward_demodulation,[],[f187,f170])).
% 8.51/1.50  fof(f170,plain,(
% 8.51/1.50    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_1),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f109,f73])).
% 8.51/1.50  fof(f73,plain,(
% 8.51/1.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f42])).
% 8.51/1.50  fof(f42,plain,(
% 8.51/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 8.51/1.50    inference(ennf_transformation,[],[f28])).
% 8.51/1.50  fof(f28,axiom,(
% 8.51/1.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 8.51/1.50  fof(f187,plain,(
% 8.51/1.50    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) ) | ~spl2_1),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f57,f109,f63])).
% 8.51/1.50  fof(f63,plain,(
% 8.51/1.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f37])).
% 8.51/1.50  fof(f37,plain,(
% 8.51/1.50    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 8.51/1.50    inference(ennf_transformation,[],[f25])).
% 8.51/1.50  fof(f25,axiom,(
% 8.51/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 8.51/1.50  fof(f4798,plain,(
% 8.51/1.50    ( ! [X50] : (r1_tarski(k10_relat_1(k6_relat_1(X50),sK0),k10_relat_1(k6_relat_1(X50),k1_relat_1(sK1)))) ) | ~spl2_4),
% 8.51/1.50    inference(superposition,[],[f1038,f355])).
% 8.51/1.50  fof(f355,plain,(
% 8.51/1.50    k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_4),
% 8.51/1.50    inference(avatar_component_clause,[],[f353])).
% 8.51/1.50  fof(f1038,plain,(
% 8.51/1.50    ( ! [X4,X2,X3] : (r1_tarski(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)))) )),
% 8.51/1.50    inference(superposition,[],[f66,f233])).
% 8.51/1.50  fof(f233,plain,(
% 8.51/1.50    ( ! [X2,X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),X2))) )),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f57,f83])).
% 8.51/1.50  fof(f83,plain,(
% 8.51/1.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 8.51/1.50    inference(cnf_transformation,[],[f46])).
% 8.51/1.50  fof(f46,plain,(
% 8.51/1.50    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 8.51/1.50    inference(ennf_transformation,[],[f24])).
% 8.51/1.50  fof(f24,axiom,(
% 8.51/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 8.51/1.50  fof(f66,plain,(
% 8.51/1.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.51/1.50    inference(cnf_transformation,[],[f9])).
% 8.51/1.50  fof(f9,axiom,(
% 8.51/1.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 8.51/1.50  fof(f619,plain,(
% 8.51/1.50    ~spl2_13 | ~spl2_1 | spl2_3),
% 8.51/1.50    inference(avatar_split_clause,[],[f323,f117,f107,f616])).
% 8.51/1.50  fof(f117,plain,(
% 8.51/1.50    spl2_3 <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 8.51/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 8.51/1.50  fof(f323,plain,(
% 8.51/1.50    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) | (~spl2_1 | spl2_3)),
% 8.51/1.50    inference(backward_demodulation,[],[f253,f313])).
% 8.51/1.50  fof(f313,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1)))) ) | ~spl2_1),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f109,f102])).
% 8.51/1.50  fof(f102,plain,(
% 8.51/1.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 8.51/1.50    inference(definition_unfolding,[],[f82,f95])).
% 8.51/1.50  fof(f82,plain,(
% 8.51/1.50    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 8.51/1.50    inference(cnf_transformation,[],[f45])).
% 8.51/1.50  fof(f45,plain,(
% 8.51/1.50    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 8.51/1.50    inference(ennf_transformation,[],[f29])).
% 8.51/1.50  fof(f29,axiom,(
% 8.51/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 8.51/1.50  fof(f253,plain,(
% 8.51/1.50    k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) | spl2_3),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f119,f101])).
% 8.51/1.50  fof(f101,plain,(
% 8.51/1.50    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 8.51/1.50    inference(definition_unfolding,[],[f79,f96])).
% 8.51/1.50  fof(f79,plain,(
% 8.51/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 8.51/1.50    inference(cnf_transformation,[],[f53])).
% 8.51/1.50  fof(f119,plain,(
% 8.51/1.50    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | spl2_3),
% 8.51/1.50    inference(avatar_component_clause,[],[f117])).
% 8.51/1.50  fof(f356,plain,(
% 8.51/1.50    spl2_4 | ~spl2_2),
% 8.51/1.50    inference(avatar_split_clause,[],[f132,f112,f353])).
% 8.51/1.50  fof(f112,plain,(
% 8.51/1.50    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 8.51/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 8.51/1.50  fof(f132,plain,(
% 8.51/1.50    k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 8.51/1.50    inference(unit_resulting_resolution,[],[f114,f74])).
% 8.51/1.50  fof(f74,plain,(
% 8.51/1.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 8.51/1.50    inference(cnf_transformation,[],[f43])).
% 8.51/1.50  fof(f43,plain,(
% 8.51/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 8.51/1.50    inference(ennf_transformation,[],[f5])).
% 8.51/1.50  fof(f5,axiom,(
% 8.51/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 8.51/1.50  fof(f114,plain,(
% 8.51/1.50    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 8.51/1.50    inference(avatar_component_clause,[],[f112])).
% 8.51/1.50  fof(f120,plain,(
% 8.51/1.50    ~spl2_3),
% 8.51/1.50    inference(avatar_split_clause,[],[f56,f117])).
% 8.51/1.50  fof(f56,plain,(
% 8.51/1.50    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 8.51/1.50    inference(cnf_transformation,[],[f50])).
% 8.51/1.50  fof(f50,plain,(
% 8.51/1.50    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 8.51/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f49])).
% 8.51/1.50  fof(f49,plain,(
% 8.51/1.50    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 8.51/1.50    introduced(choice_axiom,[])).
% 8.51/1.50  fof(f34,plain,(
% 8.51/1.50    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 8.51/1.50    inference(flattening,[],[f33])).
% 8.51/1.50  fof(f33,plain,(
% 8.51/1.50    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 8.51/1.50    inference(ennf_transformation,[],[f31])).
% 8.51/1.50  fof(f31,negated_conjecture,(
% 8.51/1.50    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 8.51/1.50    inference(negated_conjecture,[],[f30])).
% 8.51/1.50  fof(f30,conjecture,(
% 8.51/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 8.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 8.51/1.50  fof(f115,plain,(
% 8.51/1.50    spl2_2),
% 8.51/1.50    inference(avatar_split_clause,[],[f55,f112])).
% 8.51/1.50  fof(f55,plain,(
% 8.51/1.50    r1_tarski(sK0,k1_relat_1(sK1))),
% 8.51/1.50    inference(cnf_transformation,[],[f50])).
% 8.51/1.50  fof(f110,plain,(
% 8.51/1.50    spl2_1),
% 8.51/1.50    inference(avatar_split_clause,[],[f54,f107])).
% 8.51/1.50  fof(f54,plain,(
% 8.51/1.50    v1_relat_1(sK1)),
% 8.51/1.50    inference(cnf_transformation,[],[f50])).
% 8.51/1.50  % SZS output end Proof for theBenchmark
% 8.51/1.50  % (18249)------------------------------
% 8.51/1.50  % (18249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.51/1.50  % (18249)Termination reason: Refutation
% 8.51/1.50  
% 8.51/1.50  % (18249)Memory used [KB]: 18166
% 8.51/1.50  % (18249)Time elapsed: 1.069 s
% 8.51/1.50  % (18249)------------------------------
% 8.51/1.50  % (18249)------------------------------
% 8.85/1.52  % (18289)Time limit reached!
% 8.85/1.52  % (18289)------------------------------
% 8.85/1.52  % (18289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.85/1.52  % (18289)Termination reason: Time limit
% 8.85/1.52  % (18289)Termination phase: Saturation
% 8.85/1.52  
% 8.85/1.52  % (18289)Memory used [KB]: 14328
% 8.85/1.52  % (18289)Time elapsed: 0.600 s
% 8.85/1.52  % (18289)------------------------------
% 8.85/1.52  % (18289)------------------------------
% 8.85/1.53  % (18228)Success in time 1.163 s
%------------------------------------------------------------------------------
