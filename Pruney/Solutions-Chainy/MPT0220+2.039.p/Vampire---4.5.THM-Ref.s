%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 414 expanded)
%              Number of leaves         :   21 ( 140 expanded)
%              Depth                    :   16
%              Number of atoms          :   96 ( 458 expanded)
%              Number of equality atoms :   74 ( 391 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f388,f390])).

fof(f390,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f387,f376])).

fof(f376,plain,(
    ! [X4,X2] : k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X4)) = X4 ),
    inference(forward_demodulation,[],[f374,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f30,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f374,plain,(
    ! [X4,X2] : k5_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X4)) ),
    inference(backward_demodulation,[],[f358,f373])).

fof(f373,plain,(
    ! [X12,X11] : k1_xboole_0 = k4_xboole_0(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12)) ),
    inference(forward_demodulation,[],[f362,f290])).

fof(f290,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f289,f209])).

fof(f209,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f208,f26])).

fof(f208,plain,(
    ! [X4] : k5_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f194,f81])).

fof(f81,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f76,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f25,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f76,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f53,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f194,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f83,f81])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f48,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f34,f34])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f289,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f271,f209])).

fof(f271,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f84,f81])).

fof(f84,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f48,f51])).

fof(f362,plain,(
    ! [X12,X11] : k4_xboole_0(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12)) = k5_xboole_0(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11)) ),
    inference(superposition,[],[f48,f87])).

fof(f87,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(unit_resulting_resolution,[],[f50,f52])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f47,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f46])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f358,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X4) = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X4)) ),
    inference(superposition,[],[f72,f87])).

fof(f72,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f37,f48])).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f387,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl2_2
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f388,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f370,f90,f385])).

fof(f90,plain,
    ( spl2_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f370,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f369,f30])).

fof(f369,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl2_1 ),
    inference(backward_demodulation,[],[f92,f359])).

fof(f359,plain,(
    ! [X6,X5] : k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)) = k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)) ),
    inference(superposition,[],[f83,f87])).

fof(f92,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f93,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f49,f90])).

fof(f49,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f24,f46,f32,f47,f46])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:10:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (5499)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (5497)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (5505)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (5511)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (5498)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (5510)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (5502)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (5513)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (5506)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (5509)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (5512)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (5496)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (5511)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f391,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f93,f388,f390])).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    spl2_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f389])).
% 0.20/0.49  fof(f389,plain,(
% 0.20/0.49    $false | spl2_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f387,f376])).
% 0.20/0.49  fof(f376,plain,(
% 0.20/0.49    ( ! [X4,X2] : (k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X4)) = X4) )),
% 0.20/0.49    inference(forward_demodulation,[],[f374,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.49    inference(superposition,[],[f30,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.49  fof(f374,plain,(
% 0.20/0.49    ( ! [X4,X2] : (k5_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X4))) )),
% 0.20/0.49    inference(backward_demodulation,[],[f358,f373])).
% 0.20/0.49  fof(f373,plain,(
% 0.20/0.49    ( ! [X12,X11] : (k1_xboole_0 = k4_xboole_0(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f362,f290])).
% 0.20/0.49  fof(f290,plain,(
% 0.20/0.49    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f289,f209])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 0.20/0.49    inference(forward_demodulation,[],[f208,f26])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k1_xboole_0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f194,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f76,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f25,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f35,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 0.20/0.49    inference(superposition,[],[f53,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f33,f34])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 0.20/0.49    inference(superposition,[],[f83,f81])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.20/0.49    inference(superposition,[],[f48,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f29,f34,f34])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f271,f209])).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    ( ! [X5] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) )),
% 0.20/0.49    inference(superposition,[],[f84,f81])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) )),
% 0.20/0.49    inference(superposition,[],[f48,f51])).
% 0.20/0.49  fof(f362,plain,(
% 0.20/0.49    ( ! [X12,X11] : (k4_xboole_0(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12)) = k5_xboole_0(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11))) )),
% 0.20/0.49    inference(superposition,[],[f48,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f50,f52])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f47,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f31,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f36,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f38,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f39,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f40,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f27,f46])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.20/0.49  fof(f358,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (k5_xboole_0(k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X4) = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X4))) )),
% 0.20/0.49    inference(superposition,[],[f72,f87])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 0.20/0.49    inference(superposition,[],[f37,f48])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.49  fof(f387,plain,(
% 0.20/0.49    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | spl2_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f385])).
% 0.20/0.49  fof(f385,plain,(
% 0.20/0.49    spl2_2 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.49  fof(f388,plain,(
% 0.20/0.49    ~spl2_2 | spl2_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f370,f90,f385])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl2_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.49  fof(f370,plain,(
% 0.20/0.49    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | spl2_1),
% 0.20/0.49    inference(forward_demodulation,[],[f369,f30])).
% 0.20/0.49  fof(f369,plain,(
% 0.20/0.49    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl2_1),
% 0.20/0.49    inference(backward_demodulation,[],[f92,f359])).
% 0.20/0.49  fof(f359,plain,(
% 0.20/0.49    ( ! [X6,X5] : (k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)) = k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) )),
% 0.20/0.49    inference(superposition,[],[f83,f87])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl2_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ~spl2_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f49,f90])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.20/0.49    inference(definition_unfolding,[],[f24,f46,f32,f47,f46])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f18])).
% 0.20/0.49  fof(f18,conjecture,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (5511)------------------------------
% 0.20/0.49  % (5511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5511)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (5511)Memory used [KB]: 11257
% 0.20/0.49  % (5511)Time elapsed: 0.032 s
% 0.20/0.49  % (5511)------------------------------
% 0.20/0.49  % (5511)------------------------------
% 0.20/0.50  % (5500)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (5503)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (5495)Success in time 0.143 s
%------------------------------------------------------------------------------
