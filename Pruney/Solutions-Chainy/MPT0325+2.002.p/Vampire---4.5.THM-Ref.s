%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:37 EST 2020

% Result     : Theorem 32.61s
% Output     : Refutation 32.61s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 463 expanded)
%              Number of leaves         :   28 ( 149 expanded)
%              Depth                    :   19
%              Number of atoms          :  238 ( 791 expanded)
%              Number of equality atoms :  133 ( 503 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f9337,f10249,f10286,f12188,f12411,f12917,f49834,f66234])).

fof(f66234,plain,(
    spl11_23 ),
    inference(avatar_contradiction_clause,[],[f66233])).

fof(f66233,plain,
    ( $false
    | spl11_23 ),
    inference(subsumption_resolution,[],[f66137,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f66137,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | spl11_23 ),
    inference(backward_demodulation,[],[f9336,f66119])).

fof(f66119,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f66118,f96])).

fof(f96,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f57,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f71,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f84,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f86,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f87,f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f66118,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),sK1) ),
    inference(forward_demodulation,[],[f66117,f95])).

fof(f95,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f56,f93,f93])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f66117,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),sK0)),sK1) ),
    inference(forward_demodulation,[],[f66043,f96])).

fof(f66043,plain,(
    k2_zfmisc_1(k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),sK0)),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) ),
    inference(superposition,[],[f16887,f5177])).

fof(f5177,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X0,X1))) ),
    inference(superposition,[],[f102,f95])).

fof(f102,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f72,f94,f94])).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f16887,plain,(
    ! [X14] : k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14))) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,k3_xboole_0(sK1,sK3)))) ),
    inference(forward_demodulation,[],[f16846,f95])).

fof(f16846,plain,(
    ! [X14] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f4305,f121])).

fof(f121,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f4305,plain,(
    ! [X6,X8,X7,X5,X9] : k2_zfmisc_1(k3_xboole_0(X5,X6),k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,k3_xboole_0(X7,X8)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8)))) ),
    inference(superposition,[],[f101,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f101,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f73,f94,f94])).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f9336,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))
    | spl11_23 ),
    inference(avatar_component_clause,[],[f9334])).

fof(f9334,plain,
    ( spl11_23
  <=> k1_xboole_0 = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f49834,plain,
    ( ~ spl11_2
    | spl11_35 ),
    inference(avatar_contradiction_clause,[],[f49833])).

fof(f49833,plain,
    ( $false
    | ~ spl11_2
    | spl11_35 ),
    inference(subsumption_resolution,[],[f49592,f52])).

fof(f49592,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl11_2
    | spl11_35 ),
    inference(backward_demodulation,[],[f9611,f49576])).

fof(f49576,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl11_2 ),
    inference(resolution,[],[f118,f63])).

fof(f118,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl11_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f9611,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl11_35 ),
    inference(avatar_component_clause,[],[f9609])).

fof(f9609,plain,
    ( spl11_35
  <=> k1_xboole_0 = k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f12917,plain,(
    ~ spl11_33 ),
    inference(avatar_contradiction_clause,[],[f12916])).

fof(f12916,plain,
    ( $false
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f12877,f50])).

fof(f50,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f12877,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl11_33 ),
    inference(backward_demodulation,[],[f121,f12551])).

fof(f12551,plain,
    ( ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,sK3))
    | ~ spl11_33 ),
    inference(forward_demodulation,[],[f12532,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f12532,plain,
    ( ! [X2,X3] : k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,sK3)) = k2_zfmisc_1(k3_xboole_0(X2,X3),k1_xboole_0)
    | ~ spl11_33 ),
    inference(superposition,[],[f85,f9603])).

fof(f9603,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f9601])).

fof(f9601,plain,
    ( spl11_33
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f12411,plain,
    ( spl11_1
    | ~ spl11_34 ),
    inference(avatar_contradiction_clause,[],[f12410])).

fof(f12410,plain,
    ( $false
    | spl11_1
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f12381,f115])).

fof(f115,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl11_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f12381,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl11_34 ),
    inference(trivial_inequality_removal,[],[f12380])).

fof(f12380,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | ~ spl11_34 ),
    inference(superposition,[],[f100,f9607])).

fof(f9607,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f9605])).

fof(f9605,plain,
    ( spl11_34
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f12188,plain,
    ( spl11_33
    | spl11_34
    | ~ spl11_35 ),
    inference(avatar_split_clause,[],[f10436,f9609,f9605,f9601])).

fof(f10436,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f66,f9511])).

fof(f9511,plain,(
    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f8625,f121])).

fof(f8625,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X2,X3)) = k5_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(superposition,[],[f8537,f85])).

fof(f8537,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f104,f191])).

fof(f191,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f85,f55])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f104,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f74,f60,f60])).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10286,plain,(
    ~ spl11_22 ),
    inference(avatar_contradiction_clause,[],[f10285])).

fof(f10285,plain,
    ( $false
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f10263,f50])).

fof(f10263,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl11_22 ),
    inference(backward_demodulation,[],[f121,f10230])).

fof(f10230,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1))
    | ~ spl11_22 ),
    inference(forward_demodulation,[],[f10217,f106])).

fof(f106,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10217,plain,
    ( ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1))
    | ~ spl11_22 ),
    inference(superposition,[],[f85,f9332])).

fof(f9332,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f9330])).

fof(f9330,plain,
    ( spl11_22
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f10249,plain,
    ( spl11_2
    | ~ spl11_21 ),
    inference(avatar_contradiction_clause,[],[f10248])).

fof(f10248,plain,
    ( $false
    | spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f10246,f119])).

fof(f119,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f10246,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl11_21 ),
    inference(trivial_inequality_removal,[],[f10245])).

fof(f10245,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | ~ spl11_21 ),
    inference(superposition,[],[f100,f9328])).

fof(f9328,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f9326])).

fof(f9326,plain,
    ( spl11_21
  <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f9337,plain,
    ( spl11_21
    | spl11_22
    | ~ spl11_23 ),
    inference(avatar_split_clause,[],[f9303,f9334,f9330,f9326])).

fof(f9303,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f66,f9243])).

fof(f9243,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f8103,f121])).

fof(f8103,plain,(
    ! [X6,X8,X7,X9] : k2_zfmisc_1(k3_xboole_0(X6,X7),k5_xboole_0(X8,k3_xboole_0(X8,X9))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X6,X7),X8),k3_xboole_0(k2_zfmisc_1(X6,X8),k2_zfmisc_1(X7,X9))) ),
    inference(superposition,[],[f6669,f85])).

fof(f6669,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f103,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f85,f55])).

fof(f103,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f75,f60,f60])).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f51,f117,f113])).

fof(f51,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:12:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (10680)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (10703)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.50  % (10679)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (10695)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (10686)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.16/0.52  % (10687)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.16/0.52  % (10692)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.16/0.53  % (10681)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.16/0.53  % (10702)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (10682)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (10701)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.54  % (10684)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.54  % (10683)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (10693)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.55  % (10701)Refutation not found, incomplete strategy% (10701)------------------------------
% 1.35/0.55  % (10701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (10701)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (10701)Memory used [KB]: 10746
% 1.35/0.55  % (10701)Time elapsed: 0.098 s
% 1.35/0.55  % (10701)------------------------------
% 1.35/0.55  % (10701)------------------------------
% 1.35/0.55  % (10696)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (10705)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (10685)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.55  % (10708)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.55  % (10697)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.56  % (10694)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.56  % (10688)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.56  % (10689)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.56  % (10700)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.56  % (10699)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.56  % (10707)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.57  % (10704)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.57  % (10691)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.57  % (10696)Refutation not found, incomplete strategy% (10696)------------------------------
% 1.35/0.57  % (10696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (10696)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (10696)Memory used [KB]: 10618
% 1.35/0.57  % (10696)Time elapsed: 0.169 s
% 1.35/0.57  % (10696)------------------------------
% 1.35/0.57  % (10696)------------------------------
% 1.35/0.58  % (10706)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.58  % (10690)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.59  % (10698)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.52/0.70  % (10719)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.52/0.71  % (10720)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.53/0.84  % (10684)Time limit reached!
% 3.53/0.84  % (10684)------------------------------
% 3.53/0.84  % (10684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.84  % (10684)Termination reason: Time limit
% 3.53/0.84  
% 3.53/0.84  % (10684)Memory used [KB]: 8443
% 3.53/0.84  % (10684)Time elapsed: 0.435 s
% 3.53/0.84  % (10684)------------------------------
% 3.53/0.84  % (10684)------------------------------
% 3.53/0.90  % (10680)Time limit reached!
% 3.53/0.90  % (10680)------------------------------
% 3.53/0.90  % (10680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.90  % (10680)Termination reason: Time limit
% 3.53/0.90  
% 3.53/0.90  % (10680)Memory used [KB]: 9978
% 3.53/0.90  % (10680)Time elapsed: 0.518 s
% 3.53/0.90  % (10680)------------------------------
% 3.53/0.90  % (10680)------------------------------
% 3.53/0.91  % (10691)Time limit reached!
% 3.53/0.91  % (10691)------------------------------
% 3.53/0.91  % (10691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.91  % (10691)Termination reason: Time limit
% 3.53/0.91  
% 3.53/0.91  % (10691)Memory used [KB]: 8059
% 3.53/0.92  % (10691)Time elapsed: 0.505 s
% 3.53/0.92  % (10691)------------------------------
% 3.53/0.92  % (10691)------------------------------
% 3.53/0.92  % (10679)Time limit reached!
% 3.53/0.92  % (10679)------------------------------
% 3.53/0.92  % (10679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.92  % (10679)Termination reason: Time limit
% 3.53/0.92  % (10679)Termination phase: Saturation
% 3.53/0.92  
% 3.53/0.92  % (10679)Memory used [KB]: 5245
% 3.53/0.92  % (10679)Time elapsed: 0.511 s
% 3.53/0.92  % (10679)------------------------------
% 3.53/0.92  % (10679)------------------------------
% 3.53/0.92  % (10689)Time limit reached!
% 3.53/0.92  % (10689)------------------------------
% 3.53/0.92  % (10689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.94  % (10689)Termination reason: Time limit
% 4.26/0.94  
% 4.26/0.94  % (10689)Memory used [KB]: 14967
% 4.26/0.94  % (10689)Time elapsed: 0.522 s
% 4.26/0.94  % (10689)------------------------------
% 4.26/0.94  % (10689)------------------------------
% 4.26/0.96  % (10721)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.26/0.99  % (10695)Time limit reached!
% 4.26/0.99  % (10695)------------------------------
% 4.26/0.99  % (10695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.99  % (10695)Termination reason: Time limit
% 4.26/0.99  
% 4.26/0.99  % (10695)Memory used [KB]: 15607
% 4.26/0.99  % (10695)Time elapsed: 0.600 s
% 4.26/0.99  % (10695)------------------------------
% 4.26/0.99  % (10695)------------------------------
% 4.70/1.01  % (10686)Time limit reached!
% 4.70/1.01  % (10686)------------------------------
% 4.70/1.01  % (10686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.70/1.01  % (10707)Time limit reached!
% 4.70/1.01  % (10707)------------------------------
% 4.70/1.01  % (10707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.70/1.01  % (10707)Termination reason: Time limit
% 4.70/1.01  
% 4.70/1.01  % (10707)Memory used [KB]: 8955
% 4.70/1.01  % (10707)Time elapsed: 0.608 s
% 4.70/1.01  % (10707)------------------------------
% 4.70/1.01  % (10707)------------------------------
% 4.70/1.01  % (10686)Termination reason: Time limit
% 4.70/1.01  
% 4.70/1.01  % (10686)Memory used [KB]: 11641
% 4.70/1.01  % (10686)Time elapsed: 0.609 s
% 4.70/1.01  % (10686)------------------------------
% 4.70/1.01  % (10686)------------------------------
% 4.70/1.04  % (10723)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.70/1.05  % (10722)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.04/1.07  % (10725)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.04/1.08  % (10724)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.04/1.09  % (10726)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.04/1.15  % (10727)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.04/1.15  % (10728)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.65/1.22  % (10700)Time limit reached!
% 6.65/1.22  % (10700)------------------------------
% 6.65/1.22  % (10700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.65/1.22  % (10700)Termination reason: Time limit
% 6.65/1.22  
% 6.65/1.22  % (10700)Memory used [KB]: 6908
% 6.65/1.22  % (10700)Time elapsed: 0.820 s
% 6.65/1.22  % (10700)------------------------------
% 6.65/1.22  % (10700)------------------------------
% 7.62/1.35  % (10722)Time limit reached!
% 7.62/1.35  % (10722)------------------------------
% 7.62/1.35  % (10722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.62/1.35  % (10722)Termination reason: Time limit
% 7.62/1.35  % (10722)Termination phase: Saturation
% 7.62/1.35  
% 7.62/1.35  % (10722)Memory used [KB]: 7164
% 7.62/1.35  % (10722)Time elapsed: 0.414 s
% 7.62/1.35  % (10722)------------------------------
% 7.62/1.35  % (10722)------------------------------
% 7.62/1.37  % (10723)Time limit reached!
% 7.62/1.37  % (10723)------------------------------
% 7.62/1.37  % (10723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.62/1.37  % (10723)Termination reason: Time limit
% 7.62/1.37  % (10723)Termination phase: Saturation
% 7.62/1.37  
% 7.62/1.37  % (10723)Memory used [KB]: 13688
% 7.62/1.37  % (10723)Time elapsed: 0.400 s
% 7.62/1.37  % (10723)------------------------------
% 7.62/1.37  % (10723)------------------------------
% 7.62/1.38  % (10729)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.01/1.40  % (10681)Time limit reached!
% 8.01/1.40  % (10681)------------------------------
% 8.01/1.40  % (10681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.01/1.40  % (10681)Termination reason: Time limit
% 8.01/1.40  % (10681)Termination phase: Saturation
% 8.01/1.40  
% 8.01/1.40  % (10681)Memory used [KB]: 21364
% 8.01/1.40  % (10681)Time elapsed: 1.0000 s
% 8.01/1.40  % (10681)------------------------------
% 8.01/1.40  % (10681)------------------------------
% 8.56/1.48  % (10730)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.96/1.53  % (10731)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.19/1.58  % (10733)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.80/1.64  % (10705)Time limit reached!
% 9.80/1.64  % (10705)------------------------------
% 9.80/1.64  % (10705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.80/1.64  % (10705)Termination reason: Time limit
% 9.80/1.64  % (10705)Termination phase: Saturation
% 9.80/1.64  
% 9.80/1.64  % (10705)Memory used [KB]: 18677
% 9.80/1.64  % (10705)Time elapsed: 1.200 s
% 9.80/1.64  % (10705)------------------------------
% 9.80/1.64  % (10705)------------------------------
% 10.11/1.71  % (10703)Time limit reached!
% 10.11/1.71  % (10703)------------------------------
% 10.11/1.71  % (10703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.11/1.71  % (10703)Termination reason: Time limit
% 10.11/1.71  % (10703)Termination phase: Saturation
% 10.11/1.71  
% 10.11/1.71  % (10703)Memory used [KB]: 24050
% 10.11/1.71  % (10703)Time elapsed: 1.300 s
% 10.11/1.71  % (10703)------------------------------
% 10.11/1.71  % (10703)------------------------------
% 11.13/1.79  % (10694)Time limit reached!
% 11.13/1.79  % (10694)------------------------------
% 11.13/1.79  % (10694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.13/1.79  % (10694)Termination reason: Time limit
% 11.13/1.79  
% 11.13/1.79  % (10694)Memory used [KB]: 18038
% 11.13/1.79  % (10694)Time elapsed: 1.343 s
% 11.13/1.79  % (10694)------------------------------
% 11.13/1.79  % (10694)------------------------------
% 11.13/1.82  % (10734)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.71/1.88  % (10735)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.71/1.91  % (10731)Time limit reached!
% 11.71/1.91  % (10731)------------------------------
% 11.71/1.91  % (10731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.71/1.91  % (10731)Termination reason: Time limit
% 11.71/1.91  
% 11.71/1.91  % (10731)Memory used [KB]: 3582
% 11.71/1.91  % (10731)Time elapsed: 0.509 s
% 11.71/1.91  % (10731)------------------------------
% 11.71/1.91  % (10731)------------------------------
% 12.24/1.92  % (10683)Time limit reached!
% 12.24/1.92  % (10683)------------------------------
% 12.24/1.92  % (10683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.24/1.92  % (10683)Termination reason: Time limit
% 12.24/1.92  % (10683)Termination phase: Saturation
% 12.24/1.92  
% 12.24/1.92  % (10683)Memory used [KB]: 20084
% 12.24/1.92  % (10683)Time elapsed: 1.500 s
% 12.24/1.92  % (10683)------------------------------
% 12.24/1.92  % (10683)------------------------------
% 12.24/1.93  % (10736)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 12.24/1.94  % (10706)Time limit reached!
% 12.24/1.94  % (10706)------------------------------
% 12.24/1.94  % (10706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.24/1.94  % (10706)Termination reason: Time limit
% 12.24/1.94  
% 12.24/1.94  % (10706)Memory used [KB]: 13944
% 12.24/1.94  % (10706)Time elapsed: 1.511 s
% 12.24/1.94  % (10706)------------------------------
% 12.24/1.94  % (10706)------------------------------
% 12.64/2.04  % (10737)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.11/2.07  % (10690)Time limit reached!
% 13.11/2.07  % (10690)------------------------------
% 13.11/2.07  % (10690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.32/2.08  % (10690)Termination reason: Time limit
% 13.32/2.08  
% 13.32/2.08  % (10690)Memory used [KB]: 20596
% 13.32/2.08  % (10690)Time elapsed: 1.617 s
% 13.32/2.08  % (10690)------------------------------
% 13.32/2.08  % (10690)------------------------------
% 13.32/2.08  % (10739)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.32/2.11  % (10738)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.81/2.19  % (10725)Time limit reached!
% 13.81/2.19  % (10725)------------------------------
% 13.81/2.19  % (10725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.81/2.19  % (10725)Termination reason: Time limit
% 13.81/2.19  
% 13.81/2.19  % (10725)Memory used [KB]: 9722
% 13.81/2.19  % (10725)Time elapsed: 1.217 s
% 13.81/2.19  % (10725)------------------------------
% 13.81/2.19  % (10725)------------------------------
% 13.81/2.21  % (10740)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.27/2.22  % (10736)Time limit reached!
% 14.27/2.22  % (10736)------------------------------
% 14.27/2.22  % (10736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.27/2.22  % (10736)Termination reason: Time limit
% 14.27/2.22  % (10736)Termination phase: Saturation
% 14.27/2.22  
% 14.27/2.23  % (10736)Memory used [KB]: 4221
% 14.27/2.23  % (10736)Time elapsed: 0.400 s
% 14.27/2.23  % (10736)------------------------------
% 14.27/2.23  % (10736)------------------------------
% 15.12/2.34  % (10693)Time limit reached!
% 15.12/2.34  % (10693)------------------------------
% 15.12/2.34  % (10693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.12/2.34  % (10693)Termination reason: Time limit
% 15.12/2.34  % (10693)Termination phase: Saturation
% 15.12/2.34  
% 15.12/2.34  % (10693)Memory used [KB]: 5373
% 15.12/2.34  % (10693)Time elapsed: 1.800 s
% 15.12/2.34  % (10693)------------------------------
% 15.12/2.34  % (10693)------------------------------
% 15.74/2.37  % (10741)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 16.03/2.39  % (10742)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 16.03/2.40  % (10739)Time limit reached!
% 16.03/2.40  % (10739)------------------------------
% 16.03/2.40  % (10739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.03/2.40  % (10739)Termination reason: Time limit
% 16.03/2.40  % (10739)Termination phase: Saturation
% 16.03/2.40  
% 16.03/2.40  % (10739)Memory used [KB]: 3454
% 16.03/2.40  % (10739)Time elapsed: 0.400 s
% 16.03/2.40  % (10739)------------------------------
% 16.03/2.40  % (10739)------------------------------
% 16.96/2.51  % (10697)Time limit reached!
% 16.96/2.51  % (10697)------------------------------
% 16.96/2.51  % (10697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.96/2.51  % (10697)Termination reason: Time limit
% 16.96/2.51  
% 16.96/2.51  % (10697)Memory used [KB]: 14456
% 16.96/2.51  % (10697)Time elapsed: 2.085 s
% 16.96/2.51  % (10697)------------------------------
% 16.96/2.51  % (10697)------------------------------
% 16.96/2.55  % (10743)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 17.40/2.59  % (10744)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.40/2.60  % (10685)Time limit reached!
% 17.40/2.60  % (10685)------------------------------
% 17.40/2.60  % (10685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.40/2.60  % (10685)Termination reason: Time limit
% 17.40/2.60  
% 17.40/2.60  % (10685)Memory used [KB]: 18549
% 17.40/2.60  % (10685)Time elapsed: 2.126 s
% 17.40/2.60  % (10685)------------------------------
% 17.40/2.60  % (10685)------------------------------
% 17.40/2.60  % (10721)Time limit reached!
% 17.40/2.60  % (10721)------------------------------
% 17.40/2.60  % (10721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.40/2.60  % (10721)Termination reason: Time limit
% 17.40/2.60  
% 17.40/2.60  % (10721)Memory used [KB]: 17654
% 17.40/2.60  % (10721)Time elapsed: 1.725 s
% 17.40/2.60  % (10721)------------------------------
% 17.40/2.60  % (10721)------------------------------
% 18.24/2.70  % (10745)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 18.59/2.75  % (10747)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 18.59/2.76  % (10746)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 18.59/2.82  % (10727)Time limit reached!
% 18.59/2.82  % (10727)------------------------------
% 18.59/2.82  % (10727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.45/2.84  % (10727)Termination reason: Time limit
% 19.45/2.84  
% 19.45/2.84  % (10727)Memory used [KB]: 18933
% 19.45/2.84  % (10727)Time elapsed: 1.728 s
% 19.45/2.84  % (10727)------------------------------
% 19.45/2.84  % (10727)------------------------------
% 19.45/2.86  % (10744)Time limit reached!
% 19.45/2.86  % (10744)------------------------------
% 19.45/2.86  % (10744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.45/2.88  % (10744)Termination reason: Time limit
% 19.45/2.88  
% 19.45/2.88  % (10744)Memory used [KB]: 10490
% 19.45/2.88  % (10744)Time elapsed: 0.422 s
% 19.45/2.88  % (10744)------------------------------
% 19.45/2.88  % (10744)------------------------------
% 19.92/2.95  % (10735)Time limit reached!
% 19.92/2.95  % (10735)------------------------------
% 19.92/2.95  % (10735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.92/2.95  % (10735)Termination reason: Time limit
% 19.92/2.95  
% 19.92/2.95  % (10735)Memory used [KB]: 13816
% 19.92/2.95  % (10735)Time elapsed: 1.215 s
% 19.92/2.95  % (10735)------------------------------
% 19.92/2.95  % (10735)------------------------------
% 19.92/2.97  % (10687)Time limit reached!
% 19.92/2.97  % (10687)------------------------------
% 19.92/2.97  % (10687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.92/2.97  % (10687)Termination reason: Time limit
% 19.92/2.97  
% 19.92/2.97  % (10687)Memory used [KB]: 23666
% 19.92/2.97  % (10687)Time elapsed: 2.571 s
% 19.92/2.97  % (10687)------------------------------
% 19.92/2.97  % (10687)------------------------------
% 21.10/3.04  % (10746)Time limit reached!
% 21.10/3.04  % (10746)------------------------------
% 21.10/3.04  % (10746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.10/3.04  % (10746)Termination reason: Time limit
% 21.10/3.04  
% 21.10/3.04  % (10746)Memory used [KB]: 10234
% 21.10/3.04  % (10746)Time elapsed: 0.413 s
% 21.10/3.04  % (10746)------------------------------
% 21.10/3.04  % (10746)------------------------------
% 21.10/3.07  % (10698)Time limit reached!
% 21.10/3.07  % (10698)------------------------------
% 21.10/3.07  % (10698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.10/3.07  % (10698)Termination reason: Time limit
% 21.10/3.07  % (10698)Termination phase: Saturation
% 21.10/3.07  
% 21.10/3.07  % (10698)Memory used [KB]: 32622
% 21.10/3.07  % (10698)Time elapsed: 2.600 s
% 21.10/3.07  % (10698)------------------------------
% 21.10/3.07  % (10698)------------------------------
% 23.58/3.36  % (10738)Time limit reached!
% 23.58/3.36  % (10738)------------------------------
% 23.58/3.36  % (10738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.58/3.36  % (10738)Termination reason: Time limit
% 23.58/3.36  % (10738)Termination phase: Saturation
% 23.58/3.36  
% 23.58/3.36  % (10738)Memory used [KB]: 9083
% 23.58/3.36  % (10738)Time elapsed: 1.300 s
% 23.58/3.36  % (10738)------------------------------
% 23.58/3.36  % (10738)------------------------------
% 24.33/3.45  % (10692)Time limit reached!
% 24.33/3.45  % (10692)------------------------------
% 24.33/3.45  % (10692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.33/3.45  % (10692)Termination reason: Time limit
% 24.33/3.45  
% 24.33/3.45  % (10692)Memory used [KB]: 19061
% 24.33/3.45  % (10692)Time elapsed: 3.037 s
% 24.33/3.45  % (10692)------------------------------
% 24.33/3.45  % (10692)------------------------------
% 24.33/3.47  % (10720)Time limit reached!
% 24.33/3.47  % (10720)------------------------------
% 24.33/3.47  % (10720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.33/3.47  % (10720)Termination reason: Time limit
% 24.33/3.47  
% 24.33/3.47  % (10720)Memory used [KB]: 26353
% 24.33/3.47  % (10720)Time elapsed: 2.836 s
% 24.33/3.47  % (10720)------------------------------
% 24.33/3.47  % (10720)------------------------------
% 31.29/4.33  % (10708)Time limit reached!
% 31.29/4.33  % (10708)------------------------------
% 31.29/4.33  % (10708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.29/4.33  % (10708)Termination reason: Time limit
% 31.29/4.33  
% 31.29/4.33  % (10708)Memory used [KB]: 38506
% 31.29/4.33  % (10708)Time elapsed: 3.916 s
% 31.29/4.33  % (10708)------------------------------
% 31.29/4.33  % (10708)------------------------------
% 32.61/4.54  % (10682)Refutation found. Thanks to Tanya!
% 32.61/4.54  % SZS status Theorem for theBenchmark
% 32.61/4.54  % SZS output start Proof for theBenchmark
% 32.61/4.54  fof(f66290,plain,(
% 32.61/4.54    $false),
% 32.61/4.54    inference(avatar_sat_refutation,[],[f120,f9337,f10249,f10286,f12188,f12411,f12917,f49834,f66234])).
% 32.61/4.54  fof(f66234,plain,(
% 32.61/4.54    spl11_23),
% 32.61/4.54    inference(avatar_contradiction_clause,[],[f66233])).
% 32.61/4.54  fof(f66233,plain,(
% 32.61/4.54    $false | spl11_23),
% 32.61/4.54    inference(subsumption_resolution,[],[f66137,f52])).
% 32.61/4.54  fof(f52,plain,(
% 32.61/4.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 32.61/4.54    inference(cnf_transformation,[],[f9])).
% 32.61/4.54  fof(f9,axiom,(
% 32.61/4.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 32.61/4.54  fof(f66137,plain,(
% 32.61/4.54    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | spl11_23),
% 32.61/4.54    inference(backward_demodulation,[],[f9336,f66119])).
% 32.61/4.54  fof(f66119,plain,(
% 32.61/4.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 32.61/4.54    inference(forward_demodulation,[],[f66118,f96])).
% 32.61/4.54  fof(f96,plain,(
% 32.61/4.54    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 32.61/4.54    inference(definition_unfolding,[],[f57,f94])).
% 32.61/4.54  fof(f94,plain,(
% 32.61/4.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 32.61/4.54    inference(definition_unfolding,[],[f59,f93])).
% 32.61/4.54  fof(f93,plain,(
% 32.61/4.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 32.61/4.54    inference(definition_unfolding,[],[f58,f92])).
% 32.61/4.54  fof(f92,plain,(
% 32.61/4.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 32.61/4.54    inference(definition_unfolding,[],[f71,f91])).
% 32.61/4.54  fof(f91,plain,(
% 32.61/4.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 32.61/4.54    inference(definition_unfolding,[],[f84,f90])).
% 32.61/4.54  fof(f90,plain,(
% 32.61/4.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 32.61/4.54    inference(definition_unfolding,[],[f86,f89])).
% 32.61/4.54  fof(f89,plain,(
% 32.61/4.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 32.61/4.54    inference(definition_unfolding,[],[f87,f88])).
% 32.61/4.54  fof(f88,plain,(
% 32.61/4.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 32.61/4.54    inference(cnf_transformation,[],[f16])).
% 32.61/4.54  fof(f16,axiom,(
% 32.61/4.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 32.61/4.54  fof(f87,plain,(
% 32.61/4.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 32.61/4.54    inference(cnf_transformation,[],[f15])).
% 32.61/4.54  fof(f15,axiom,(
% 32.61/4.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 32.61/4.54  fof(f86,plain,(
% 32.61/4.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 32.61/4.54    inference(cnf_transformation,[],[f14])).
% 32.61/4.54  fof(f14,axiom,(
% 32.61/4.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 32.61/4.54  fof(f84,plain,(
% 32.61/4.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 32.61/4.54    inference(cnf_transformation,[],[f13])).
% 32.61/4.54  fof(f13,axiom,(
% 32.61/4.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 32.61/4.54  fof(f71,plain,(
% 32.61/4.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 32.61/4.54    inference(cnf_transformation,[],[f12])).
% 32.61/4.54  fof(f12,axiom,(
% 32.61/4.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 32.61/4.54  fof(f58,plain,(
% 32.61/4.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 32.61/4.54    inference(cnf_transformation,[],[f11])).
% 32.61/4.54  fof(f11,axiom,(
% 32.61/4.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 32.61/4.54  fof(f59,plain,(
% 32.61/4.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 32.61/4.54    inference(cnf_transformation,[],[f18])).
% 32.61/4.54  fof(f18,axiom,(
% 32.61/4.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 32.61/4.54  fof(f57,plain,(
% 32.61/4.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 32.61/4.54    inference(cnf_transformation,[],[f6])).
% 32.61/4.54  fof(f6,axiom,(
% 32.61/4.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 32.61/4.54  fof(f66118,plain,(
% 32.61/4.54    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),sK1)),
% 32.61/4.54    inference(forward_demodulation,[],[f66117,f95])).
% 32.61/4.54  fof(f95,plain,(
% 32.61/4.54    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 32.61/4.54    inference(definition_unfolding,[],[f56,f93,f93])).
% 32.61/4.54  fof(f56,plain,(
% 32.61/4.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 32.61/4.54    inference(cnf_transformation,[],[f10])).
% 32.61/4.54  fof(f10,axiom,(
% 32.61/4.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 32.61/4.54  fof(f66117,plain,(
% 32.61/4.54    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),sK0)),sK1)),
% 32.61/4.54    inference(forward_demodulation,[],[f66043,f96])).
% 32.61/4.54  fof(f66043,plain,(
% 32.61/4.54    k2_zfmisc_1(k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),sK0)),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3))))),
% 32.61/4.54    inference(superposition,[],[f16887,f5177])).
% 32.61/4.54  fof(f5177,plain,(
% 32.61/4.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X0,X1)))) )),
% 32.61/4.54    inference(superposition,[],[f102,f95])).
% 32.61/4.54  fof(f102,plain,(
% 32.61/4.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 32.61/4.54    inference(definition_unfolding,[],[f72,f94,f94])).
% 32.61/4.54  fof(f72,plain,(
% 32.61/4.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 32.61/4.54    inference(cnf_transformation,[],[f20])).
% 32.61/4.54  fof(f20,axiom,(
% 32.61/4.54    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 32.61/4.54  fof(f16887,plain,(
% 32.61/4.54    ( ! [X14] : (k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14))) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,k3_xboole_0(sK1,sK3))))) )),
% 32.61/4.54    inference(forward_demodulation,[],[f16846,f95])).
% 32.61/4.54  fof(f16846,plain,(
% 32.61/4.54    ( ! [X14] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X14),k2_zfmisc_1(sK0,sK1)))) )),
% 32.61/4.54    inference(superposition,[],[f4305,f121])).
% 32.61/4.54  fof(f121,plain,(
% 32.61/4.54    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 32.61/4.54    inference(resolution,[],[f63,f49])).
% 32.61/4.54  fof(f49,plain,(
% 32.61/4.54    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 32.61/4.54    inference(cnf_transformation,[],[f32])).
% 32.61/4.54  fof(f32,plain,(
% 32.61/4.54    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 32.61/4.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f31])).
% 32.61/4.54  fof(f31,plain,(
% 32.61/4.54    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 32.61/4.54    introduced(choice_axiom,[])).
% 32.61/4.54  fof(f28,plain,(
% 32.61/4.54    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 32.61/4.54    inference(flattening,[],[f27])).
% 32.61/4.54  fof(f27,plain,(
% 32.61/4.54    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 32.61/4.54    inference(ennf_transformation,[],[f24])).
% 32.61/4.54  fof(f24,negated_conjecture,(
% 32.61/4.54    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 32.61/4.54    inference(negated_conjecture,[],[f23])).
% 32.61/4.54  fof(f23,conjecture,(
% 32.61/4.54    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 32.61/4.54  fof(f63,plain,(
% 32.61/4.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 32.61/4.54    inference(cnf_transformation,[],[f30])).
% 32.61/4.54  fof(f30,plain,(
% 32.61/4.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 32.61/4.54    inference(ennf_transformation,[],[f7])).
% 32.61/4.54  fof(f7,axiom,(
% 32.61/4.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 32.61/4.54  fof(f4305,plain,(
% 32.61/4.54    ( ! [X6,X8,X7,X5,X9] : (k2_zfmisc_1(k3_xboole_0(X5,X6),k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,k3_xboole_0(X7,X8)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k2_zfmisc_1(k3_xboole_0(X5,X6),X9),k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8))))) )),
% 32.61/4.54    inference(superposition,[],[f101,f85])).
% 32.61/4.54  fof(f85,plain,(
% 32.61/4.54    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 32.61/4.54    inference(cnf_transformation,[],[f21])).
% 32.61/4.54  fof(f21,axiom,(
% 32.61/4.54    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 32.61/4.54  fof(f101,plain,(
% 32.61/4.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 32.61/4.54    inference(definition_unfolding,[],[f73,f94,f94])).
% 32.61/4.54  fof(f73,plain,(
% 32.61/4.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 32.61/4.54    inference(cnf_transformation,[],[f20])).
% 32.61/4.54  fof(f9336,plain,(
% 32.61/4.54    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) | spl11_23),
% 32.61/4.54    inference(avatar_component_clause,[],[f9334])).
% 32.61/4.54  fof(f9334,plain,(
% 32.61/4.54    spl11_23 <=> k1_xboole_0 = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))),
% 32.61/4.54    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 32.61/4.54  fof(f49834,plain,(
% 32.61/4.54    ~spl11_2 | spl11_35),
% 32.61/4.54    inference(avatar_contradiction_clause,[],[f49833])).
% 32.61/4.54  fof(f49833,plain,(
% 32.61/4.54    $false | (~spl11_2 | spl11_35)),
% 32.61/4.54    inference(subsumption_resolution,[],[f49592,f52])).
% 32.61/4.54  fof(f49592,plain,(
% 32.61/4.54    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | (~spl11_2 | spl11_35)),
% 32.61/4.54    inference(backward_demodulation,[],[f9611,f49576])).
% 32.61/4.54  fof(f49576,plain,(
% 32.61/4.54    sK1 = k3_xboole_0(sK1,sK3) | ~spl11_2),
% 32.61/4.54    inference(resolution,[],[f118,f63])).
% 32.61/4.54  fof(f118,plain,(
% 32.61/4.54    r1_tarski(sK1,sK3) | ~spl11_2),
% 32.61/4.54    inference(avatar_component_clause,[],[f117])).
% 32.61/4.54  fof(f117,plain,(
% 32.61/4.54    spl11_2 <=> r1_tarski(sK1,sK3)),
% 32.61/4.54    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 32.61/4.54  fof(f9611,plain,(
% 32.61/4.54    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | spl11_35),
% 32.61/4.54    inference(avatar_component_clause,[],[f9609])).
% 32.61/4.54  fof(f9609,plain,(
% 32.61/4.54    spl11_35 <=> k1_xboole_0 = k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))),
% 32.61/4.54    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).
% 32.61/4.54  fof(f12917,plain,(
% 32.61/4.54    ~spl11_33),
% 32.61/4.54    inference(avatar_contradiction_clause,[],[f12916])).
% 32.61/4.54  fof(f12916,plain,(
% 32.61/4.54    $false | ~spl11_33),
% 32.61/4.54    inference(subsumption_resolution,[],[f12877,f50])).
% 32.61/4.54  fof(f50,plain,(
% 32.61/4.54    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 32.61/4.54    inference(cnf_transformation,[],[f32])).
% 32.61/4.54  fof(f12877,plain,(
% 32.61/4.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl11_33),
% 32.61/4.54    inference(backward_demodulation,[],[f121,f12551])).
% 32.61/4.54  fof(f12551,plain,(
% 32.61/4.54    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,sK3))) ) | ~spl11_33),
% 32.61/4.54    inference(forward_demodulation,[],[f12532,f105])).
% 32.61/4.54  fof(f105,plain,(
% 32.61/4.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 32.61/4.54    inference(equality_resolution,[],[f68])).
% 32.61/4.54  fof(f68,plain,(
% 32.61/4.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 32.61/4.54    inference(cnf_transformation,[],[f41])).
% 32.61/4.54  fof(f41,plain,(
% 32.61/4.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 32.61/4.54    inference(flattening,[],[f40])).
% 32.61/4.54  fof(f40,plain,(
% 32.61/4.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 32.61/4.54    inference(nnf_transformation,[],[f19])).
% 32.61/4.54  fof(f19,axiom,(
% 32.61/4.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 32.61/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 32.61/4.54  fof(f12532,plain,(
% 32.61/4.54    ( ! [X2,X3] : (k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,sK3)) = k2_zfmisc_1(k3_xboole_0(X2,X3),k1_xboole_0)) ) | ~spl11_33),
% 32.61/4.54    inference(superposition,[],[f85,f9603])).
% 32.61/4.54  fof(f9603,plain,(
% 32.61/4.54    k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl11_33),
% 32.61/4.54    inference(avatar_component_clause,[],[f9601])).
% 32.61/4.54  fof(f9601,plain,(
% 32.61/4.54    spl11_33 <=> k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 32.61/4.54    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).
% 32.61/4.54  fof(f12411,plain,(
% 32.61/4.54    spl11_1 | ~spl11_34),
% 32.61/4.54    inference(avatar_contradiction_clause,[],[f12410])).
% 32.61/4.55  fof(f12410,plain,(
% 32.61/4.55    $false | (spl11_1 | ~spl11_34)),
% 32.61/4.55    inference(subsumption_resolution,[],[f12381,f115])).
% 32.61/4.55  fof(f115,plain,(
% 32.61/4.55    ~r1_tarski(sK0,sK2) | spl11_1),
% 32.61/4.55    inference(avatar_component_clause,[],[f113])).
% 32.61/4.55  fof(f113,plain,(
% 32.61/4.55    spl11_1 <=> r1_tarski(sK0,sK2)),
% 32.61/4.55    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 32.61/4.55  fof(f12381,plain,(
% 32.61/4.55    r1_tarski(sK0,sK2) | ~spl11_34),
% 32.61/4.55    inference(trivial_inequality_removal,[],[f12380])).
% 32.61/4.55  fof(f12380,plain,(
% 32.61/4.55    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | ~spl11_34),
% 32.61/4.55    inference(superposition,[],[f100,f9607])).
% 32.61/4.55  fof(f9607,plain,(
% 32.61/4.55    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl11_34),
% 32.61/4.55    inference(avatar_component_clause,[],[f9605])).
% 32.61/4.55  fof(f9605,plain,(
% 32.61/4.55    spl11_34 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 32.61/4.55    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).
% 32.61/4.55  fof(f100,plain,(
% 32.61/4.55    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 32.61/4.55    inference(definition_unfolding,[],[f69,f60])).
% 32.61/4.55  fof(f60,plain,(
% 32.61/4.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 32.61/4.55    inference(cnf_transformation,[],[f5])).
% 32.61/4.55  fof(f5,axiom,(
% 32.61/4.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 32.61/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 32.61/4.55  fof(f69,plain,(
% 32.61/4.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 32.61/4.55    inference(cnf_transformation,[],[f42])).
% 32.61/4.55  fof(f42,plain,(
% 32.61/4.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 32.61/4.55    inference(nnf_transformation,[],[f4])).
% 32.61/4.55  fof(f4,axiom,(
% 32.61/4.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 32.61/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 32.61/4.55  fof(f12188,plain,(
% 32.61/4.55    spl11_33 | spl11_34 | ~spl11_35),
% 32.61/4.55    inference(avatar_split_clause,[],[f10436,f9609,f9605,f9601])).
% 32.61/4.55  fof(f10436,plain,(
% 32.61/4.55    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 32.61/4.55    inference(superposition,[],[f66,f9511])).
% 32.61/4.55  fof(f9511,plain,(
% 32.61/4.55    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))),
% 32.61/4.55    inference(superposition,[],[f8625,f121])).
% 32.61/4.55  fof(f8625,plain,(
% 32.61/4.55    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X2,X3)) = k5_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 32.61/4.55    inference(superposition,[],[f8537,f85])).
% 32.61/4.55  fof(f8537,plain,(
% 32.61/4.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2))) )),
% 32.61/4.55    inference(backward_demodulation,[],[f104,f191])).
% 32.61/4.55  fof(f191,plain,(
% 32.61/4.55    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 32.61/4.55    inference(superposition,[],[f85,f55])).
% 32.61/4.55  fof(f55,plain,(
% 32.61/4.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 32.61/4.55    inference(cnf_transformation,[],[f25])).
% 32.61/4.55  fof(f25,plain,(
% 32.61/4.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 32.61/4.55    inference(rectify,[],[f2])).
% 32.61/4.55  fof(f2,axiom,(
% 32.61/4.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 32.61/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 32.61/4.55  fof(f104,plain,(
% 32.61/4.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 32.61/4.55    inference(definition_unfolding,[],[f74,f60,f60])).
% 32.61/4.55  fof(f74,plain,(
% 32.61/4.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 32.61/4.55    inference(cnf_transformation,[],[f22])).
% 32.61/4.55  fof(f22,axiom,(
% 32.61/4.55    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 32.61/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 32.61/4.55  fof(f66,plain,(
% 32.61/4.55    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 32.61/4.55    inference(cnf_transformation,[],[f41])).
% 32.61/4.55  fof(f10286,plain,(
% 32.61/4.55    ~spl11_22),
% 32.61/4.55    inference(avatar_contradiction_clause,[],[f10285])).
% 32.61/4.55  fof(f10285,plain,(
% 32.61/4.55    $false | ~spl11_22),
% 32.61/4.55    inference(subsumption_resolution,[],[f10263,f50])).
% 32.61/4.55  fof(f10263,plain,(
% 32.61/4.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl11_22),
% 32.61/4.55    inference(backward_demodulation,[],[f121,f10230])).
% 32.61/4.55  fof(f10230,plain,(
% 32.61/4.55    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1))) ) | ~spl11_22),
% 32.61/4.55    inference(forward_demodulation,[],[f10217,f106])).
% 32.61/4.55  fof(f106,plain,(
% 32.61/4.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 32.61/4.55    inference(equality_resolution,[],[f67])).
% 32.61/4.55  fof(f67,plain,(
% 32.61/4.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 32.61/4.55    inference(cnf_transformation,[],[f41])).
% 32.61/4.55  fof(f10217,plain,(
% 32.61/4.55    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1))) ) | ~spl11_22),
% 32.61/4.55    inference(superposition,[],[f85,f9332])).
% 32.61/4.55  fof(f9332,plain,(
% 32.61/4.55    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl11_22),
% 32.61/4.55    inference(avatar_component_clause,[],[f9330])).
% 32.61/4.55  fof(f9330,plain,(
% 32.61/4.55    spl11_22 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 32.61/4.55    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 32.61/4.55  fof(f10249,plain,(
% 32.61/4.55    spl11_2 | ~spl11_21),
% 32.61/4.55    inference(avatar_contradiction_clause,[],[f10248])).
% 32.61/4.55  fof(f10248,plain,(
% 32.61/4.55    $false | (spl11_2 | ~spl11_21)),
% 32.61/4.55    inference(subsumption_resolution,[],[f10246,f119])).
% 32.61/4.55  fof(f119,plain,(
% 32.61/4.55    ~r1_tarski(sK1,sK3) | spl11_2),
% 32.61/4.55    inference(avatar_component_clause,[],[f117])).
% 32.61/4.55  fof(f10246,plain,(
% 32.61/4.55    r1_tarski(sK1,sK3) | ~spl11_21),
% 32.61/4.55    inference(trivial_inequality_removal,[],[f10245])).
% 32.61/4.55  fof(f10245,plain,(
% 32.61/4.55    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | ~spl11_21),
% 32.61/4.55    inference(superposition,[],[f100,f9328])).
% 32.61/4.55  fof(f9328,plain,(
% 32.61/4.55    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | ~spl11_21),
% 32.61/4.55    inference(avatar_component_clause,[],[f9326])).
% 32.61/4.55  fof(f9326,plain,(
% 32.61/4.55    spl11_21 <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 32.61/4.55    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 32.61/4.55  fof(f9337,plain,(
% 32.61/4.55    spl11_21 | spl11_22 | ~spl11_23),
% 32.61/4.55    inference(avatar_split_clause,[],[f9303,f9334,f9330,f9326])).
% 32.61/4.55  fof(f9303,plain,(
% 32.61/4.55    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 32.61/4.55    inference(superposition,[],[f66,f9243])).
% 32.61/4.55  fof(f9243,plain,(
% 32.61/4.55    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))),
% 32.61/4.55    inference(superposition,[],[f8103,f121])).
% 32.61/4.55  fof(f8103,plain,(
% 32.61/4.55    ( ! [X6,X8,X7,X9] : (k2_zfmisc_1(k3_xboole_0(X6,X7),k5_xboole_0(X8,k3_xboole_0(X8,X9))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X6,X7),X8),k3_xboole_0(k2_zfmisc_1(X6,X8),k2_zfmisc_1(X7,X9)))) )),
% 32.61/4.55    inference(superposition,[],[f6669,f85])).
% 32.61/4.55  fof(f6669,plain,(
% 32.61/4.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))) )),
% 32.61/4.55    inference(backward_demodulation,[],[f103,f189])).
% 32.61/4.55  fof(f189,plain,(
% 32.61/4.55    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 32.61/4.55    inference(superposition,[],[f85,f55])).
% 32.61/4.55  fof(f103,plain,(
% 32.61/4.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 32.61/4.55    inference(definition_unfolding,[],[f75,f60,f60])).
% 32.61/4.55  fof(f75,plain,(
% 32.61/4.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 32.61/4.55    inference(cnf_transformation,[],[f22])).
% 32.61/4.55  fof(f120,plain,(
% 32.61/4.55    ~spl11_1 | ~spl11_2),
% 32.61/4.55    inference(avatar_split_clause,[],[f51,f117,f113])).
% 32.61/4.55  fof(f51,plain,(
% 32.61/4.55    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 32.61/4.55    inference(cnf_transformation,[],[f32])).
% 32.61/4.55  % SZS output end Proof for theBenchmark
% 32.61/4.55  % (10682)------------------------------
% 32.61/4.55  % (10682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 32.61/4.55  % (10682)Termination reason: Refutation
% 32.61/4.55  
% 32.61/4.55  % (10682)Memory used [KB]: 44775
% 32.61/4.55  % (10682)Time elapsed: 4.125 s
% 32.61/4.55  % (10682)------------------------------
% 32.61/4.55  % (10682)------------------------------
% 32.61/4.55  % (10670)Success in time 4.187 s
%------------------------------------------------------------------------------
