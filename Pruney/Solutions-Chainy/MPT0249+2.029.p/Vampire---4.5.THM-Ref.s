%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:14 EST 2020

% Result     : Theorem 3.29s
% Output     : Refutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  214 (2643 expanded)
%              Number of leaves         :   38 ( 837 expanded)
%              Depth                    :   20
%              Number of atoms          :  513 (4468 expanded)
%              Number of equality atoms :  132 (2499 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3053,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f133,f143,f182,f196,f372,f398,f412,f575,f2597,f2602,f2603,f2691,f2825,f3052])).

fof(f3052,plain,
    ( spl6_6
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f3046])).

fof(f3046,plain,
    ( $false
    | spl6_6
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(resolution,[],[f2872,f360])).

fof(f360,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f357,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f357,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f164,f91])).

fof(f91,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f164,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(backward_demodulation,[],[f105,f163])).

fof(f163,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f158,f104])).

fof(f104,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f103,f91])).

fof(f103,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f90,f49])).

fof(f90,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f52,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f158,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f71,f49])).

fof(f71,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X0) ),
    inference(backward_demodulation,[],[f93,f71])).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(definition_unfolding,[],[f55,f87])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f58,f86])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2872,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_6
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f141,f2869])).

fof(f2869,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f2862,f49])).

fof(f2862,plain,
    ( sK2 = k5_xboole_0(sK1,sK1)
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(superposition,[],[f528,f2836])).

fof(f2836,plain,
    ( sK1 = k5_xboole_0(sK2,sK1)
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f397,f319])).

fof(f319,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl6_13
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f397,plain,
    ( sK1 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl6_15
  <=> sK1 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f528,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k5_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f516,f470])).

fof(f470,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f163,f49])).

fof(f516,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f163,f161])).

fof(f161,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(superposition,[],[f71,f49])).

fof(f141,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl6_6
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f2825,plain,
    ( spl6_4
    | ~ spl6_7
    | ~ spl6_13
    | spl6_14
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f2814])).

fof(f2814,plain,
    ( $false
    | spl6_4
    | ~ spl6_7
    | ~ spl6_13
    | spl6_14
    | ~ spl6_16 ),
    inference(resolution,[],[f2811,f2765])).

fof(f2765,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f440,f2761])).

fof(f2761,plain,
    ( sK0 = sK4(sK1,sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f780,f1805])).

fof(f1805,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK0 = sK4(sK1,X0) ) ),
    inference(resolution,[],[f1802,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1802,plain,(
    ! [X20] :
      ( ~ r2_hidden(X20,sK1)
      | sK0 = X20 ) ),
    inference(resolution,[],[f334,f307])).

fof(f307,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f92,f89])).

fof(f89,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f45,f88,f85])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f84])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f85])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f334,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X6,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4))
      | ~ r2_hidden(X5,X6)
      | X4 = X5 ) ),
    inference(resolution,[],[f102,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f102,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f88])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f780,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f455,f98])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f455,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | ~ r1_tarski(X1,sK2) )
    | ~ spl6_16 ),
    inference(resolution,[],[f411,f98])).

fof(f411,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,sK2) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f440,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f337,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f337,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl6_7 ),
    inference(superposition,[],[f305,f91])).

fof(f305,plain,
    ( ! [X4] : ~ r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X4)),sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f92,f181])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_7
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f2811,plain,
    ( r2_hidden(sK0,sK2)
    | spl6_4
    | ~ spl6_13
    | spl6_14 ),
    inference(resolution,[],[f2679,f1880])).

fof(f1880,plain,
    ( ! [X56] :
        ( r2_hidden(sK0,k5_xboole_0(sK1,X56))
        | r2_hidden(sK0,X56) )
    | spl6_4 ),
    inference(forward_demodulation,[],[f1819,f1803])).

fof(f1803,plain,
    ( sK0 = sK4(sK1,k1_xboole_0)
    | spl6_4 ),
    inference(resolution,[],[f1802,f1050])).

fof(f1050,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK1)
    | spl6_4 ),
    inference(condensation,[],[f1049])).

fof(f1049,plain,
    ( ! [X20] :
        ( r2_hidden(sK4(sK1,k1_xboole_0),X20)
        | r2_hidden(sK4(sK1,k1_xboole_0),sK1) )
    | spl6_4 ),
    inference(duplicate_literal_removal,[],[f1036])).

fof(f1036,plain,
    ( ! [X20] :
        ( r2_hidden(sK4(sK1,k1_xboole_0),X20)
        | r2_hidden(sK4(sK1,k1_xboole_0),sK1)
        | r2_hidden(sK4(sK1,k1_xboole_0),X20) )
    | spl6_4 ),
    inference(resolution,[],[f1016,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1016,plain,
    ( ! [X56] :
        ( r2_hidden(sK4(sK1,k1_xboole_0),k5_xboole_0(sK1,X56))
        | r2_hidden(sK4(sK1,k1_xboole_0),X56) )
    | spl6_4 ),
    inference(resolution,[],[f229,f131])).

fof(f131,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_4
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f229,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(X2,X3)
      | r2_hidden(sK4(X2,X3),k5_xboole_0(X2,X4))
      | r2_hidden(sK4(X2,X3),X4) ) ),
    inference(resolution,[],[f74,f64])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1819,plain,
    ( ! [X56] :
        ( r2_hidden(sK0,k5_xboole_0(sK1,X56))
        | r2_hidden(sK4(sK1,k1_xboole_0),X56) )
    | spl6_4 ),
    inference(backward_demodulation,[],[f1016,f1803])).

fof(f2679,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl6_13
    | spl6_14 ),
    inference(forward_demodulation,[],[f2640,f932])).

fof(f932,plain,(
    ! [X10,X9] : k5_xboole_0(X10,X9) = k5_xboole_0(X9,X10) ),
    inference(superposition,[],[f163,f528])).

fof(f2640,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,sK1))
    | ~ spl6_13
    | spl6_14 ),
    inference(backward_demodulation,[],[f2075,f319])).

fof(f2075,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl6_14 ),
    inference(backward_demodulation,[],[f401,f2058])).

fof(f2058,plain,
    ( sK0 = sK4(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl6_14 ),
    inference(resolution,[],[f1805,f393])).

fof(f393,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl6_14
  <=> r1_tarski(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f401,plain,
    ( ~ r2_hidden(sK4(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl6_14 ),
    inference(resolution,[],[f393,f65])).

fof(f2691,plain,
    ( ~ spl6_8
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f2682])).

fof(f2682,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(resolution,[],[f2649,f1597])).

fof(f1597,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f1591,f290])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,sK1),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f262,f98])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(sK4(sK2,X0),X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f256,f63])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f195,f65])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1591,plain,
    ( r2_hidden(sK4(sK2,sK1),k5_xboole_0(sK1,sK2))
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f1583,f932])).

fof(f1583,plain,
    ( r2_hidden(sK4(sK2,sK1),k5_xboole_0(sK2,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f1578,f98])).

fof(f1578,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r2_hidden(sK4(sK2,sK1),k5_xboole_0(sK2,X0)) )
    | ~ spl6_8 ),
    inference(superposition,[],[f1516,f163])).

fof(f1516,plain,
    ( ! [X9] :
        ( ~ r1_tarski(k5_xboole_0(sK2,X9),sK1)
        | r2_hidden(sK4(sK2,sK1),X9) )
    | ~ spl6_8 ),
    inference(resolution,[],[f1025,f290])).

fof(f1025,plain,
    ( ! [X79] :
        ( r2_hidden(sK4(sK2,sK1),k5_xboole_0(sK2,X79))
        | r2_hidden(sK4(sK2,sK1),X79) )
    | ~ spl6_8 ),
    inference(resolution,[],[f229,f339])).

fof(f339,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl6_8 ),
    inference(superposition,[],[f306,f91])).

fof(f306,plain,
    ( ! [X5] : ~ r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X5)),sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f92,f195])).

fof(f2649,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f2609,f932])).

fof(f2609,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK1),sK1)
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f356,f319])).

fof(f356,plain,(
    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[],[f164,f89])).

fof(f2603,plain,
    ( spl6_13
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f2463,f313,f317])).

fof(f313,plain,
    ( spl6_12
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f2463,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f302,f89])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ) ),
    inference(resolution,[],[f92,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2602,plain,
    ( spl6_4
    | spl6_44 ),
    inference(avatar_contradiction_clause,[],[f2599])).

fof(f2599,plain,
    ( $false
    | spl6_4
    | spl6_44 ),
    inference(resolution,[],[f2596,f1829])).

fof(f1829,plain,
    ( r2_hidden(sK0,sK1)
    | spl6_4 ),
    inference(backward_demodulation,[],[f1050,f1803])).

fof(f2596,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl6_44 ),
    inference(avatar_component_clause,[],[f2594])).

fof(f2594,plain,
    ( spl6_44
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f2597,plain,
    ( spl6_12
    | ~ spl6_44
    | spl6_12 ),
    inference(avatar_split_clause,[],[f2572,f313,f2594,f313])).

fof(f2572,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl6_12 ),
    inference(superposition,[],[f321,f333])).

fof(f333,plain,(
    ! [X2,X3] :
      ( sK4(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3) = X2
      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3) ) ),
    inference(resolution,[],[f102,f64])).

fof(f321,plain,
    ( ~ r2_hidden(sK4(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK1)
    | spl6_12 ),
    inference(resolution,[],[f315,f65])).

fof(f315,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f313])).

fof(f575,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f137,f360])).

fof(f137,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_5
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f412,plain,
    ( spl6_1
    | spl6_16
    | spl6_1 ),
    inference(avatar_split_clause,[],[f406,f115,f410,f115])).

fof(f115,plain,
    ( spl6_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f406,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,sK2)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,sK2) )
    | spl6_1 ),
    inference(resolution,[],[f279,f64])).

fof(f279,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(sK4(sK1,sK2),X3)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X1,sK2)
        | ~ r1_tarski(X3,X2) )
    | spl6_1 ),
    inference(resolution,[],[f203,f63])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK1,sK2),X1)
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,X0) )
    | spl6_1 ),
    inference(resolution,[],[f199,f63])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,sK2),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl6_1 ),
    inference(resolution,[],[f197,f63])).

fof(f197,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | spl6_1 ),
    inference(resolution,[],[f117,f65])).

fof(f117,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f398,plain,
    ( ~ spl6_14
    | spl6_15 ),
    inference(avatar_split_clause,[],[f389,f395,f391])).

fof(f389,plain,
    ( sK1 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(resolution,[],[f356,f62])).

fof(f372,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl6_3 ),
    inference(resolution,[],[f360,f127])).

fof(f127,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_3
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f196,plain,
    ( spl6_2
    | spl6_8
    | spl6_2 ),
    inference(avatar_split_clause,[],[f191,f119,f194,f119])).

fof(f119,plain,
    ( spl6_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK2,X0)
        | r1_tarski(sK2,sK1) )
    | spl6_2 ),
    inference(resolution,[],[f168,f64])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK2,sK1),X1)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X1,X0) )
    | spl6_2 ),
    inference(resolution,[],[f151,f63])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,sK1),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl6_2 ),
    inference(resolution,[],[f145,f63])).

fof(f145,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl6_2 ),
    inference(resolution,[],[f121,f65])).

fof(f121,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f182,plain,
    ( spl6_1
    | spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f177,f115,f180,f115])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,sK2) )
    | spl6_1 ),
    inference(resolution,[],[f157,f64])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK1,sK2),X1)
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,X0) )
    | spl6_1 ),
    inference(resolution,[],[f150,f63])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,sK2),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl6_1 ),
    inference(resolution,[],[f144,f63])).

fof(f144,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | spl6_1 ),
    inference(resolution,[],[f117,f65])).

fof(f143,plain,
    ( ~ spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f111,f135,f139])).

fof(f111,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(extensionality_resolution,[],[f62,f48])).

fof(f48,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f133,plain,
    ( ~ spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f109,f125,f129])).

fof(f109,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(extensionality_resolution,[],[f62,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f123,plain,
    ( ~ spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f107,f115,f119])).

fof(f107,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK2,sK1) ),
    inference(extensionality_resolution,[],[f62,f46])).

fof(f46,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:07:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (2004)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.49  % (1996)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (2006)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (1998)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (1998)Refutation not found, incomplete strategy% (1998)------------------------------
% 0.21/0.51  % (1998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1998)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1998)Memory used [KB]: 10746
% 0.21/0.51  % (1998)Time elapsed: 0.097 s
% 0.21/0.51  % (1998)------------------------------
% 0.21/0.51  % (1998)------------------------------
% 0.21/0.51  % (2014)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (2003)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (2002)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (2012)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (2018)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (1995)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (1992)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (1994)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (1990)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (1992)Refutation not found, incomplete strategy% (1992)------------------------------
% 0.21/0.54  % (1992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1992)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1992)Memory used [KB]: 10746
% 0.21/0.54  % (1992)Time elapsed: 0.119 s
% 0.21/0.54  % (1992)------------------------------
% 0.21/0.54  % (1992)------------------------------
% 0.21/0.54  % (2008)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (2013)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (1991)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (1993)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (2010)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (2011)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (2000)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (1997)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (2011)Refutation not found, incomplete strategy% (2011)------------------------------
% 0.21/0.55  % (2011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2011)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (2011)Memory used [KB]: 1791
% 0.21/0.55  % (2011)Time elapsed: 0.145 s
% 0.21/0.55  % (2011)------------------------------
% 0.21/0.55  % (2011)------------------------------
% 0.21/0.55  % (2000)Refutation not found, incomplete strategy% (2000)------------------------------
% 0.21/0.55  % (2000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2000)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (2000)Memory used [KB]: 10618
% 0.21/0.55  % (2000)Time elapsed: 0.141 s
% 0.21/0.55  % (2000)------------------------------
% 0.21/0.55  % (2000)------------------------------
% 0.21/0.55  % (2007)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (2005)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (2016)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (2019)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.57  % (1999)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.57  % (2017)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.58  % (2009)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.58  % (2001)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.58  % (2015)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.68/0.61  % (2001)Refutation not found, incomplete strategy% (2001)------------------------------
% 1.68/0.61  % (2001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.62  % (2001)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.62  
% 1.68/0.62  % (2001)Memory used [KB]: 10874
% 1.68/0.62  % (2001)Time elapsed: 0.192 s
% 1.68/0.62  % (2001)------------------------------
% 1.68/0.62  % (2001)------------------------------
% 2.18/0.66  % (2041)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.18/0.66  % (2039)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.24/0.71  % (2040)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.24/0.71  % (2042)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.75/0.79  % (2043)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.75/0.81  % (1995)Time limit reached!
% 2.75/0.81  % (1995)------------------------------
% 2.75/0.81  % (1995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.81  % (1995)Termination reason: Time limit
% 2.75/0.81  % (1995)Termination phase: Saturation
% 2.75/0.81  
% 2.75/0.81  % (1995)Memory used [KB]: 9210
% 2.75/0.81  % (1995)Time elapsed: 0.400 s
% 2.75/0.81  % (1995)------------------------------
% 2.75/0.81  % (1995)------------------------------
% 3.29/0.86  % (2002)Refutation found. Thanks to Tanya!
% 3.29/0.86  % SZS status Theorem for theBenchmark
% 3.29/0.86  % SZS output start Proof for theBenchmark
% 3.29/0.86  fof(f3053,plain,(
% 3.29/0.86    $false),
% 3.29/0.86    inference(avatar_sat_refutation,[],[f123,f133,f143,f182,f196,f372,f398,f412,f575,f2597,f2602,f2603,f2691,f2825,f3052])).
% 3.29/0.86  fof(f3052,plain,(
% 3.29/0.86    spl6_6 | ~spl6_13 | ~spl6_15),
% 3.29/0.86    inference(avatar_contradiction_clause,[],[f3046])).
% 3.29/0.86  fof(f3046,plain,(
% 3.29/0.86    $false | (spl6_6 | ~spl6_13 | ~spl6_15)),
% 3.29/0.86    inference(resolution,[],[f2872,f360])).
% 3.29/0.86  fof(f360,plain,(
% 3.29/0.86    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.29/0.86    inference(forward_demodulation,[],[f357,f49])).
% 3.29/0.86  fof(f49,plain,(
% 3.29/0.86    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f11])).
% 3.29/0.86  fof(f11,axiom,(
% 3.29/0.86    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.29/0.86  fof(f357,plain,(
% 3.29/0.86    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 3.29/0.86    inference(superposition,[],[f164,f91])).
% 3.29/0.86  fof(f91,plain,(
% 3.29/0.86    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.29/0.86    inference(definition_unfolding,[],[f53,f85])).
% 3.29/0.86  fof(f85,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.29/0.86    inference(definition_unfolding,[],[f56,f84])).
% 3.29/0.86  fof(f84,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.29/0.86    inference(definition_unfolding,[],[f57,f83])).
% 3.29/0.86  fof(f83,plain,(
% 3.29/0.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.29/0.86    inference(definition_unfolding,[],[f70,f82])).
% 3.29/0.86  fof(f82,plain,(
% 3.29/0.86    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.29/0.86    inference(definition_unfolding,[],[f76,f81])).
% 3.29/0.86  fof(f81,plain,(
% 3.29/0.86    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.29/0.86    inference(definition_unfolding,[],[f77,f80])).
% 3.29/0.86  fof(f80,plain,(
% 3.29/0.86    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.29/0.86    inference(definition_unfolding,[],[f78,f79])).
% 3.29/0.86  fof(f79,plain,(
% 3.29/0.86    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f20])).
% 3.29/0.86  fof(f20,axiom,(
% 3.29/0.86    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.29/0.86  fof(f78,plain,(
% 3.29/0.86    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f19])).
% 3.29/0.86  fof(f19,axiom,(
% 3.29/0.86    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.29/0.86  fof(f77,plain,(
% 3.29/0.86    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f18])).
% 3.29/0.86  fof(f18,axiom,(
% 3.29/0.86    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.29/0.86  fof(f76,plain,(
% 3.29/0.86    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f17])).
% 3.29/0.86  fof(f17,axiom,(
% 3.29/0.86    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.29/0.86  fof(f70,plain,(
% 3.29/0.86    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f16])).
% 3.29/0.86  fof(f16,axiom,(
% 3.29/0.86    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.29/0.86  fof(f57,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f15])).
% 3.29/0.86  fof(f15,axiom,(
% 3.29/0.86    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.29/0.86  fof(f56,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.29/0.86    inference(cnf_transformation,[],[f21])).
% 3.29/0.86  fof(f21,axiom,(
% 3.29/0.86    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.29/0.86  fof(f53,plain,(
% 3.29/0.86    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.29/0.86    inference(cnf_transformation,[],[f25])).
% 3.29/0.86  fof(f25,plain,(
% 3.29/0.86    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.29/0.86    inference(rectify,[],[f2])).
% 3.29/0.86  fof(f2,axiom,(
% 3.29/0.86    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 3.29/0.86  fof(f164,plain,(
% 3.29/0.86    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 3.29/0.86    inference(backward_demodulation,[],[f105,f163])).
% 3.29/0.86  fof(f163,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 3.29/0.86    inference(forward_demodulation,[],[f158,f104])).
% 3.29/0.86  fof(f104,plain,(
% 3.29/0.86    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.29/0.86    inference(backward_demodulation,[],[f103,f91])).
% 3.29/0.86  fof(f103,plain,(
% 3.29/0.86    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 3.29/0.86    inference(forward_demodulation,[],[f90,f49])).
% 3.29/0.86  fof(f90,plain,(
% 3.29/0.86    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 3.29/0.86    inference(definition_unfolding,[],[f52,f86])).
% 3.29/0.86  fof(f86,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.29/0.86    inference(definition_unfolding,[],[f59,f85])).
% 3.29/0.86  fof(f59,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.29/0.86    inference(cnf_transformation,[],[f12])).
% 3.29/0.86  fof(f12,axiom,(
% 3.29/0.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 3.29/0.86  fof(f52,plain,(
% 3.29/0.86    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.29/0.86    inference(cnf_transformation,[],[f24])).
% 3.29/0.86  fof(f24,plain,(
% 3.29/0.86    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.29/0.86    inference(rectify,[],[f3])).
% 3.29/0.86  fof(f3,axiom,(
% 3.29/0.86    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.29/0.86  fof(f158,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 3.29/0.86    inference(superposition,[],[f71,f49])).
% 3.29/0.86  fof(f71,plain,(
% 3.29/0.86    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.29/0.86    inference(cnf_transformation,[],[f10])).
% 3.29/0.86  fof(f10,axiom,(
% 3.29/0.86    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.29/0.86  fof(f105,plain,(
% 3.29/0.86    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X0)) )),
% 3.29/0.86    inference(backward_demodulation,[],[f93,f71])).
% 3.29/0.86  fof(f93,plain,(
% 3.29/0.86    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 3.29/0.86    inference(definition_unfolding,[],[f55,f87])).
% 3.29/0.86  fof(f87,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.29/0.86    inference(definition_unfolding,[],[f58,f86])).
% 3.29/0.86  fof(f58,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.29/0.86    inference(cnf_transformation,[],[f7])).
% 3.29/0.86  fof(f7,axiom,(
% 3.29/0.86    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.29/0.86  fof(f55,plain,(
% 3.29/0.86    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f8])).
% 3.29/0.86  fof(f8,axiom,(
% 3.29/0.86    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.29/0.86  fof(f2872,plain,(
% 3.29/0.86    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl6_6 | ~spl6_13 | ~spl6_15)),
% 3.29/0.86    inference(backward_demodulation,[],[f141,f2869])).
% 3.29/0.86  fof(f2869,plain,(
% 3.29/0.86    k1_xboole_0 = sK2 | (~spl6_13 | ~spl6_15)),
% 3.29/0.86    inference(forward_demodulation,[],[f2862,f49])).
% 3.29/0.86  fof(f2862,plain,(
% 3.29/0.86    sK2 = k5_xboole_0(sK1,sK1) | (~spl6_13 | ~spl6_15)),
% 3.29/0.86    inference(superposition,[],[f528,f2836])).
% 3.29/0.86  fof(f2836,plain,(
% 3.29/0.86    sK1 = k5_xboole_0(sK2,sK1) | (~spl6_13 | ~spl6_15)),
% 3.29/0.86    inference(forward_demodulation,[],[f397,f319])).
% 3.29/0.86  fof(f319,plain,(
% 3.29/0.86    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl6_13),
% 3.29/0.86    inference(avatar_component_clause,[],[f317])).
% 3.29/0.86  fof(f317,plain,(
% 3.29/0.86    spl6_13 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 3.29/0.86  fof(f397,plain,(
% 3.29/0.86    sK1 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl6_15),
% 3.29/0.86    inference(avatar_component_clause,[],[f395])).
% 3.29/0.86  fof(f395,plain,(
% 3.29/0.86    spl6_15 <=> sK1 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 3.29/0.86  fof(f528,plain,(
% 3.29/0.86    ( ! [X2,X3] : (k5_xboole_0(X3,k5_xboole_0(X2,X3)) = X2) )),
% 3.29/0.86    inference(forward_demodulation,[],[f516,f470])).
% 3.29/0.86  fof(f470,plain,(
% 3.29/0.86    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.29/0.86    inference(superposition,[],[f163,f49])).
% 3.29/0.86  fof(f516,plain,(
% 3.29/0.86    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(X2,X3))) )),
% 3.29/0.86    inference(superposition,[],[f163,f161])).
% 3.29/0.86  fof(f161,plain,(
% 3.29/0.86    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 3.29/0.86    inference(superposition,[],[f71,f49])).
% 3.29/0.86  fof(f141,plain,(
% 3.29/0.86    ~r1_tarski(sK2,k1_xboole_0) | spl6_6),
% 3.29/0.86    inference(avatar_component_clause,[],[f139])).
% 3.29/0.86  fof(f139,plain,(
% 3.29/0.86    spl6_6 <=> r1_tarski(sK2,k1_xboole_0)),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 3.29/0.86  fof(f2825,plain,(
% 3.29/0.86    spl6_4 | ~spl6_7 | ~spl6_13 | spl6_14 | ~spl6_16),
% 3.29/0.86    inference(avatar_contradiction_clause,[],[f2814])).
% 3.29/0.86  fof(f2814,plain,(
% 3.29/0.86    $false | (spl6_4 | ~spl6_7 | ~spl6_13 | spl6_14 | ~spl6_16)),
% 3.29/0.86    inference(resolution,[],[f2811,f2765])).
% 3.29/0.86  fof(f2765,plain,(
% 3.29/0.86    ~r2_hidden(sK0,sK2) | (~spl6_7 | ~spl6_16)),
% 3.29/0.86    inference(backward_demodulation,[],[f440,f2761])).
% 3.29/0.86  fof(f2761,plain,(
% 3.29/0.86    sK0 = sK4(sK1,sK2) | ~spl6_16),
% 3.29/0.86    inference(resolution,[],[f780,f1805])).
% 3.29/0.86  fof(f1805,plain,(
% 3.29/0.86    ( ! [X0] : (r1_tarski(sK1,X0) | sK0 = sK4(sK1,X0)) )),
% 3.29/0.86    inference(resolution,[],[f1802,f64])).
% 3.29/0.86  fof(f64,plain,(
% 3.29/0.86    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f39])).
% 3.29/0.86  fof(f39,plain,(
% 3.29/0.86    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.29/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 3.29/0.86  fof(f38,plain,(
% 3.29/0.86    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.29/0.86    introduced(choice_axiom,[])).
% 3.29/0.86  fof(f37,plain,(
% 3.29/0.86    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.29/0.86    inference(rectify,[],[f36])).
% 3.29/0.86  fof(f36,plain,(
% 3.29/0.86    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.29/0.86    inference(nnf_transformation,[],[f28])).
% 3.29/0.86  fof(f28,plain,(
% 3.29/0.86    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.29/0.86    inference(ennf_transformation,[],[f1])).
% 3.29/0.86  fof(f1,axiom,(
% 3.29/0.86    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.29/0.86  fof(f1802,plain,(
% 3.29/0.86    ( ! [X20] : (~r2_hidden(X20,sK1) | sK0 = X20) )),
% 3.29/0.86    inference(resolution,[],[f334,f307])).
% 3.29/0.86  fof(f307,plain,(
% 3.29/0.86    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 3.29/0.86    inference(superposition,[],[f92,f89])).
% 3.29/0.86  fof(f89,plain,(
% 3.29/0.86    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 3.29/0.86    inference(definition_unfolding,[],[f45,f88,f85])).
% 3.29/0.86  fof(f88,plain,(
% 3.29/0.86    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.29/0.86    inference(definition_unfolding,[],[f50,f84])).
% 3.29/0.86  fof(f50,plain,(
% 3.29/0.86    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f14])).
% 3.29/0.86  fof(f14,axiom,(
% 3.29/0.86    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.29/0.86  fof(f45,plain,(
% 3.29/0.86    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 3.29/0.86    inference(cnf_transformation,[],[f31])).
% 3.29/0.86  fof(f31,plain,(
% 3.29/0.86    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 3.29/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).
% 3.29/0.86  fof(f30,plain,(
% 3.29/0.86    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 3.29/0.86    introduced(choice_axiom,[])).
% 3.29/0.86  fof(f26,plain,(
% 3.29/0.86    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 3.29/0.86    inference(ennf_transformation,[],[f23])).
% 3.29/0.86  fof(f23,negated_conjecture,(
% 3.29/0.86    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 3.29/0.86    inference(negated_conjecture,[],[f22])).
% 3.29/0.86  fof(f22,conjecture,(
% 3.29/0.86    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 3.29/0.86  fof(f92,plain,(
% 3.29/0.86    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.29/0.86    inference(definition_unfolding,[],[f54,f85])).
% 3.29/0.86  fof(f54,plain,(
% 3.29/0.86    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.29/0.86    inference(cnf_transformation,[],[f9])).
% 3.29/0.86  fof(f9,axiom,(
% 3.29/0.86    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.29/0.86  fof(f334,plain,(
% 3.29/0.86    ( ! [X6,X4,X5] : (~r1_tarski(X6,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)) | ~r2_hidden(X5,X6) | X4 = X5) )),
% 3.29/0.86    inference(resolution,[],[f102,f63])).
% 3.29/0.86  fof(f63,plain,(
% 3.29/0.86    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f39])).
% 3.29/0.86  fof(f102,plain,(
% 3.29/0.86    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 3.29/0.86    inference(equality_resolution,[],[f97])).
% 3.29/0.86  fof(f97,plain,(
% 3.29/0.86    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.29/0.86    inference(definition_unfolding,[],[f66,f88])).
% 3.29/0.86  fof(f66,plain,(
% 3.29/0.86    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.29/0.86    inference(cnf_transformation,[],[f43])).
% 3.29/0.86  fof(f43,plain,(
% 3.29/0.86    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 3.29/0.86  fof(f42,plain,(
% 3.29/0.86    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 3.29/0.86    introduced(choice_axiom,[])).
% 3.29/0.86  fof(f41,plain,(
% 3.29/0.86    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/0.86    inference(rectify,[],[f40])).
% 3.29/0.86  fof(f40,plain,(
% 3.29/0.86    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.29/0.86    inference(nnf_transformation,[],[f13])).
% 3.29/0.86  fof(f13,axiom,(
% 3.29/0.86    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 3.29/0.86  fof(f780,plain,(
% 3.29/0.86    ~r1_tarski(sK1,sK2) | ~spl6_16),
% 3.29/0.86    inference(resolution,[],[f455,f98])).
% 3.29/0.86  fof(f98,plain,(
% 3.29/0.86    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.29/0.86    inference(equality_resolution,[],[f61])).
% 3.29/0.86  fof(f61,plain,(
% 3.29/0.86    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.29/0.86    inference(cnf_transformation,[],[f35])).
% 3.29/0.86  fof(f35,plain,(
% 3.29/0.86    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.29/0.86    inference(flattening,[],[f34])).
% 3.29/0.86  fof(f34,plain,(
% 3.29/0.86    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.29/0.86    inference(nnf_transformation,[],[f6])).
% 3.29/0.86  fof(f6,axiom,(
% 3.29/0.86    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.29/0.86  fof(f455,plain,(
% 3.29/0.86    ( ! [X1] : (~r1_tarski(sK1,X1) | ~r1_tarski(X1,sK2)) ) | ~spl6_16),
% 3.29/0.86    inference(resolution,[],[f411,f98])).
% 3.29/0.86  fof(f411,plain,(
% 3.29/0.86    ( ! [X0,X1] : (~r1_tarski(sK1,X0) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,sK2)) ) | ~spl6_16),
% 3.29/0.86    inference(avatar_component_clause,[],[f410])).
% 3.29/0.86  fof(f410,plain,(
% 3.29/0.86    spl6_16 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~r1_tarski(sK1,X0) | ~r1_tarski(X1,sK2))),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 3.29/0.86  fof(f440,plain,(
% 3.29/0.86    ~r2_hidden(sK4(sK1,sK2),sK2) | ~spl6_7),
% 3.29/0.86    inference(resolution,[],[f337,f65])).
% 3.29/0.86  fof(f65,plain,(
% 3.29/0.86    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f39])).
% 3.29/0.86  fof(f337,plain,(
% 3.29/0.86    ~r1_tarski(sK1,sK2) | ~spl6_7),
% 3.29/0.86    inference(superposition,[],[f305,f91])).
% 3.29/0.86  fof(f305,plain,(
% 3.29/0.86    ( ! [X4] : (~r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X4)),sK2)) ) | ~spl6_7),
% 3.29/0.86    inference(resolution,[],[f92,f181])).
% 3.29/0.86  fof(f181,plain,(
% 3.29/0.86    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_tarski(X0,sK2)) ) | ~spl6_7),
% 3.29/0.86    inference(avatar_component_clause,[],[f180])).
% 3.29/0.86  fof(f180,plain,(
% 3.29/0.86    spl6_7 <=> ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(sK1,X0))),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 3.29/0.86  fof(f2811,plain,(
% 3.29/0.86    r2_hidden(sK0,sK2) | (spl6_4 | ~spl6_13 | spl6_14)),
% 3.29/0.86    inference(resolution,[],[f2679,f1880])).
% 3.29/0.86  fof(f1880,plain,(
% 3.29/0.86    ( ! [X56] : (r2_hidden(sK0,k5_xboole_0(sK1,X56)) | r2_hidden(sK0,X56)) ) | spl6_4),
% 3.29/0.86    inference(forward_demodulation,[],[f1819,f1803])).
% 3.29/0.86  fof(f1803,plain,(
% 3.29/0.86    sK0 = sK4(sK1,k1_xboole_0) | spl6_4),
% 3.29/0.86    inference(resolution,[],[f1802,f1050])).
% 3.29/0.86  fof(f1050,plain,(
% 3.29/0.86    r2_hidden(sK4(sK1,k1_xboole_0),sK1) | spl6_4),
% 3.29/0.86    inference(condensation,[],[f1049])).
% 3.29/0.86  fof(f1049,plain,(
% 3.29/0.86    ( ! [X20] : (r2_hidden(sK4(sK1,k1_xboole_0),X20) | r2_hidden(sK4(sK1,k1_xboole_0),sK1)) ) | spl6_4),
% 3.29/0.86    inference(duplicate_literal_removal,[],[f1036])).
% 3.29/0.86  fof(f1036,plain,(
% 3.29/0.86    ( ! [X20] : (r2_hidden(sK4(sK1,k1_xboole_0),X20) | r2_hidden(sK4(sK1,k1_xboole_0),sK1) | r2_hidden(sK4(sK1,k1_xboole_0),X20)) ) | spl6_4),
% 3.29/0.86    inference(resolution,[],[f1016,f72])).
% 3.29/0.86  fof(f72,plain,(
% 3.29/0.86    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f44])).
% 3.29/0.86  fof(f44,plain,(
% 3.29/0.86    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.29/0.86    inference(nnf_transformation,[],[f29])).
% 3.29/0.86  fof(f29,plain,(
% 3.29/0.86    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.29/0.86    inference(ennf_transformation,[],[f4])).
% 3.29/0.86  fof(f4,axiom,(
% 3.29/0.86    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.29/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 3.29/0.86  fof(f1016,plain,(
% 3.29/0.86    ( ! [X56] : (r2_hidden(sK4(sK1,k1_xboole_0),k5_xboole_0(sK1,X56)) | r2_hidden(sK4(sK1,k1_xboole_0),X56)) ) | spl6_4),
% 3.29/0.86    inference(resolution,[],[f229,f131])).
% 3.29/0.86  fof(f131,plain,(
% 3.29/0.86    ~r1_tarski(sK1,k1_xboole_0) | spl6_4),
% 3.29/0.86    inference(avatar_component_clause,[],[f129])).
% 3.29/0.86  fof(f129,plain,(
% 3.29/0.86    spl6_4 <=> r1_tarski(sK1,k1_xboole_0)),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.29/0.86  fof(f229,plain,(
% 3.29/0.86    ( ! [X4,X2,X3] : (r1_tarski(X2,X3) | r2_hidden(sK4(X2,X3),k5_xboole_0(X2,X4)) | r2_hidden(sK4(X2,X3),X4)) )),
% 3.29/0.86    inference(resolution,[],[f74,f64])).
% 3.29/0.86  fof(f74,plain,(
% 3.29/0.86    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,X2) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.29/0.86    inference(cnf_transformation,[],[f44])).
% 3.29/0.86  fof(f1819,plain,(
% 3.29/0.86    ( ! [X56] : (r2_hidden(sK0,k5_xboole_0(sK1,X56)) | r2_hidden(sK4(sK1,k1_xboole_0),X56)) ) | spl6_4),
% 3.29/0.86    inference(backward_demodulation,[],[f1016,f1803])).
% 3.29/0.86  fof(f2679,plain,(
% 3.29/0.86    ~r2_hidden(sK0,k5_xboole_0(sK1,sK2)) | (~spl6_13 | spl6_14)),
% 3.29/0.86    inference(forward_demodulation,[],[f2640,f932])).
% 3.29/0.86  fof(f932,plain,(
% 3.29/0.86    ( ! [X10,X9] : (k5_xboole_0(X10,X9) = k5_xboole_0(X9,X10)) )),
% 3.29/0.86    inference(superposition,[],[f163,f528])).
% 3.29/0.86  fof(f2640,plain,(
% 3.29/0.86    ~r2_hidden(sK0,k5_xboole_0(sK2,sK1)) | (~spl6_13 | spl6_14)),
% 3.29/0.86    inference(backward_demodulation,[],[f2075,f319])).
% 3.29/0.86  fof(f2075,plain,(
% 3.29/0.86    ~r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl6_14),
% 3.29/0.86    inference(backward_demodulation,[],[f401,f2058])).
% 3.29/0.86  fof(f2058,plain,(
% 3.29/0.86    sK0 = sK4(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl6_14),
% 3.29/0.86    inference(resolution,[],[f1805,f393])).
% 3.29/0.86  fof(f393,plain,(
% 3.29/0.86    ~r1_tarski(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl6_14),
% 3.29/0.86    inference(avatar_component_clause,[],[f391])).
% 3.29/0.86  fof(f391,plain,(
% 3.29/0.86    spl6_14 <=> r1_tarski(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 3.29/0.86  fof(f401,plain,(
% 3.29/0.86    ~r2_hidden(sK4(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl6_14),
% 3.29/0.86    inference(resolution,[],[f393,f65])).
% 3.29/0.86  fof(f2691,plain,(
% 3.29/0.86    ~spl6_8 | ~spl6_13),
% 3.29/0.86    inference(avatar_contradiction_clause,[],[f2682])).
% 3.29/0.86  fof(f2682,plain,(
% 3.29/0.86    $false | (~spl6_8 | ~spl6_13)),
% 3.29/0.86    inference(resolution,[],[f2649,f1597])).
% 3.29/0.86  fof(f1597,plain,(
% 3.29/0.86    ~r1_tarski(k5_xboole_0(sK1,sK2),sK1) | ~spl6_8),
% 3.29/0.86    inference(resolution,[],[f1591,f290])).
% 3.29/0.86  fof(f290,plain,(
% 3.29/0.86    ( ! [X0] : (~r2_hidden(sK4(sK2,sK1),X0) | ~r1_tarski(X0,sK1)) ) | ~spl6_8),
% 3.29/0.86    inference(resolution,[],[f262,f98])).
% 3.29/0.86  fof(f262,plain,(
% 3.29/0.86    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK4(sK2,X0),X1) | ~r1_tarski(X1,X0)) ) | ~spl6_8),
% 3.29/0.86    inference(resolution,[],[f256,f63])).
% 3.29/0.86  fof(f256,plain,(
% 3.29/0.86    ( ! [X0] : (~r2_hidden(sK4(sK2,X0),X0) | ~r1_tarski(X0,sK1)) ) | ~spl6_8),
% 3.29/0.86    inference(resolution,[],[f195,f65])).
% 3.29/0.86  fof(f195,plain,(
% 3.29/0.86    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,sK1)) ) | ~spl6_8),
% 3.29/0.86    inference(avatar_component_clause,[],[f194])).
% 3.29/0.86  fof(f194,plain,(
% 3.29/0.86    spl6_8 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK2,X0))),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 3.29/0.86  fof(f1591,plain,(
% 3.29/0.86    r2_hidden(sK4(sK2,sK1),k5_xboole_0(sK1,sK2)) | ~spl6_8),
% 3.29/0.86    inference(forward_demodulation,[],[f1583,f932])).
% 3.29/0.86  fof(f1583,plain,(
% 3.29/0.86    r2_hidden(sK4(sK2,sK1),k5_xboole_0(sK2,sK1)) | ~spl6_8),
% 3.29/0.86    inference(resolution,[],[f1578,f98])).
% 3.29/0.86  fof(f1578,plain,(
% 3.29/0.86    ( ! [X0] : (~r1_tarski(X0,sK1) | r2_hidden(sK4(sK2,sK1),k5_xboole_0(sK2,X0))) ) | ~spl6_8),
% 3.29/0.86    inference(superposition,[],[f1516,f163])).
% 3.29/0.86  fof(f1516,plain,(
% 3.29/0.86    ( ! [X9] : (~r1_tarski(k5_xboole_0(sK2,X9),sK1) | r2_hidden(sK4(sK2,sK1),X9)) ) | ~spl6_8),
% 3.29/0.86    inference(resolution,[],[f1025,f290])).
% 3.29/0.86  fof(f1025,plain,(
% 3.29/0.86    ( ! [X79] : (r2_hidden(sK4(sK2,sK1),k5_xboole_0(sK2,X79)) | r2_hidden(sK4(sK2,sK1),X79)) ) | ~spl6_8),
% 3.29/0.86    inference(resolution,[],[f229,f339])).
% 3.29/0.86  fof(f339,plain,(
% 3.29/0.86    ~r1_tarski(sK2,sK1) | ~spl6_8),
% 3.29/0.86    inference(superposition,[],[f306,f91])).
% 3.29/0.86  fof(f306,plain,(
% 3.29/0.86    ( ! [X5] : (~r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X5)),sK1)) ) | ~spl6_8),
% 3.29/0.86    inference(resolution,[],[f92,f195])).
% 3.29/0.86  fof(f2649,plain,(
% 3.29/0.86    r1_tarski(k5_xboole_0(sK1,sK2),sK1) | ~spl6_13),
% 3.29/0.86    inference(forward_demodulation,[],[f2609,f932])).
% 3.29/0.86  fof(f2609,plain,(
% 3.29/0.86    r1_tarski(k5_xboole_0(sK2,sK1),sK1) | ~spl6_13),
% 3.29/0.86    inference(backward_demodulation,[],[f356,f319])).
% 3.29/0.86  fof(f356,plain,(
% 3.29/0.86    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 3.29/0.86    inference(superposition,[],[f164,f89])).
% 3.29/0.86  fof(f2603,plain,(
% 3.29/0.86    spl6_13 | ~spl6_12),
% 3.29/0.86    inference(avatar_split_clause,[],[f2463,f313,f317])).
% 3.29/0.86  fof(f313,plain,(
% 3.29/0.86    spl6_12 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 3.29/0.86  fof(f2463,plain,(
% 3.29/0.86    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 3.29/0.86    inference(superposition,[],[f302,f89])).
% 3.29/0.86  fof(f302,plain,(
% 3.29/0.86    ( ! [X0,X1] : (~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0) )),
% 3.29/0.86    inference(resolution,[],[f92,f62])).
% 3.29/0.86  fof(f62,plain,(
% 3.29/0.86    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.29/0.86    inference(cnf_transformation,[],[f35])).
% 3.29/0.86  fof(f2602,plain,(
% 3.29/0.86    spl6_4 | spl6_44),
% 3.29/0.86    inference(avatar_contradiction_clause,[],[f2599])).
% 3.29/0.86  fof(f2599,plain,(
% 3.29/0.86    $false | (spl6_4 | spl6_44)),
% 3.29/0.86    inference(resolution,[],[f2596,f1829])).
% 3.29/0.86  fof(f1829,plain,(
% 3.29/0.86    r2_hidden(sK0,sK1) | spl6_4),
% 3.29/0.86    inference(backward_demodulation,[],[f1050,f1803])).
% 3.29/0.86  fof(f2596,plain,(
% 3.29/0.86    ~r2_hidden(sK0,sK1) | spl6_44),
% 3.29/0.86    inference(avatar_component_clause,[],[f2594])).
% 3.29/0.86  fof(f2594,plain,(
% 3.29/0.86    spl6_44 <=> r2_hidden(sK0,sK1)),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 3.29/0.86  fof(f2597,plain,(
% 3.29/0.86    spl6_12 | ~spl6_44 | spl6_12),
% 3.29/0.86    inference(avatar_split_clause,[],[f2572,f313,f2594,f313])).
% 3.29/0.86  fof(f2572,plain,(
% 3.29/0.86    ~r2_hidden(sK0,sK1) | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl6_12),
% 3.29/0.86    inference(superposition,[],[f321,f333])).
% 3.29/0.86  fof(f333,plain,(
% 3.29/0.86    ( ! [X2,X3] : (sK4(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3) = X2 | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) )),
% 3.29/0.86    inference(resolution,[],[f102,f64])).
% 3.29/0.86  fof(f321,plain,(
% 3.29/0.86    ~r2_hidden(sK4(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK1) | spl6_12),
% 3.29/0.86    inference(resolution,[],[f315,f65])).
% 3.29/0.86  fof(f315,plain,(
% 3.29/0.86    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl6_12),
% 3.29/0.86    inference(avatar_component_clause,[],[f313])).
% 3.29/0.86  fof(f575,plain,(
% 3.29/0.86    spl6_5),
% 3.29/0.86    inference(avatar_contradiction_clause,[],[f573])).
% 3.29/0.86  fof(f573,plain,(
% 3.29/0.86    $false | spl6_5),
% 3.29/0.86    inference(resolution,[],[f137,f360])).
% 3.29/0.86  fof(f137,plain,(
% 3.29/0.86    ~r1_tarski(k1_xboole_0,sK2) | spl6_5),
% 3.29/0.86    inference(avatar_component_clause,[],[f135])).
% 3.29/0.86  fof(f135,plain,(
% 3.29/0.86    spl6_5 <=> r1_tarski(k1_xboole_0,sK2)),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.29/0.86  fof(f412,plain,(
% 3.29/0.86    spl6_1 | spl6_16 | spl6_1),
% 3.29/0.86    inference(avatar_split_clause,[],[f406,f115,f410,f115])).
% 3.29/0.86  fof(f115,plain,(
% 3.29/0.86    spl6_1 <=> r1_tarski(sK1,sK2)),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.29/0.86  fof(f406,plain,(
% 3.29/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,sK2) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,sK2)) ) | spl6_1),
% 3.29/0.86    inference(resolution,[],[f279,f64])).
% 3.29/0.86  fof(f279,plain,(
% 3.29/0.86    ( ! [X2,X3,X1] : (~r2_hidden(sK4(sK1,sK2),X3) | ~r1_tarski(X2,X1) | ~r1_tarski(X1,sK2) | ~r1_tarski(X3,X2)) ) | spl6_1),
% 3.29/0.86    inference(resolution,[],[f203,f63])).
% 3.29/0.86  fof(f203,plain,(
% 3.29/0.86    ( ! [X0,X1] : (~r2_hidden(sK4(sK1,sK2),X1) | ~r1_tarski(X0,sK2) | ~r1_tarski(X1,X0)) ) | spl6_1),
% 3.29/0.86    inference(resolution,[],[f199,f63])).
% 3.29/0.86  fof(f199,plain,(
% 3.29/0.86    ( ! [X0] : (~r2_hidden(sK4(sK1,sK2),X0) | ~r1_tarski(X0,sK2)) ) | spl6_1),
% 3.29/0.86    inference(resolution,[],[f197,f63])).
% 3.29/0.86  fof(f197,plain,(
% 3.29/0.86    ~r2_hidden(sK4(sK1,sK2),sK2) | spl6_1),
% 3.29/0.86    inference(resolution,[],[f117,f65])).
% 3.29/0.86  fof(f117,plain,(
% 3.29/0.86    ~r1_tarski(sK1,sK2) | spl6_1),
% 3.29/0.86    inference(avatar_component_clause,[],[f115])).
% 3.29/0.86  fof(f398,plain,(
% 3.29/0.86    ~spl6_14 | spl6_15),
% 3.29/0.86    inference(avatar_split_clause,[],[f389,f395,f391])).
% 3.29/0.86  fof(f389,plain,(
% 3.29/0.86    sK1 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r1_tarski(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 3.29/0.86    inference(resolution,[],[f356,f62])).
% 3.29/0.86  fof(f372,plain,(
% 3.29/0.86    spl6_3),
% 3.29/0.86    inference(avatar_contradiction_clause,[],[f362])).
% 3.29/0.86  fof(f362,plain,(
% 3.29/0.86    $false | spl6_3),
% 3.29/0.86    inference(resolution,[],[f360,f127])).
% 3.29/0.86  fof(f127,plain,(
% 3.29/0.86    ~r1_tarski(k1_xboole_0,sK1) | spl6_3),
% 3.29/0.86    inference(avatar_component_clause,[],[f125])).
% 3.29/0.86  fof(f125,plain,(
% 3.29/0.86    spl6_3 <=> r1_tarski(k1_xboole_0,sK1)),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.29/0.86  fof(f196,plain,(
% 3.29/0.86    spl6_2 | spl6_8 | spl6_2),
% 3.29/0.86    inference(avatar_split_clause,[],[f191,f119,f194,f119])).
% 3.29/0.86  fof(f119,plain,(
% 3.29/0.86    spl6_2 <=> r1_tarski(sK2,sK1)),
% 3.29/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.29/0.86  fof(f191,plain,(
% 3.29/0.86    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,sK1)) ) | spl6_2),
% 3.29/0.86    inference(resolution,[],[f168,f64])).
% 3.29/0.86  fof(f168,plain,(
% 3.29/0.86    ( ! [X0,X1] : (~r2_hidden(sK4(sK2,sK1),X1) | ~r1_tarski(X0,sK1) | ~r1_tarski(X1,X0)) ) | spl6_2),
% 3.29/0.86    inference(resolution,[],[f151,f63])).
% 3.29/0.86  fof(f151,plain,(
% 3.29/0.86    ( ! [X0] : (~r2_hidden(sK4(sK2,sK1),X0) | ~r1_tarski(X0,sK1)) ) | spl6_2),
% 3.29/0.86    inference(resolution,[],[f145,f63])).
% 3.29/0.86  fof(f145,plain,(
% 3.29/0.86    ~r2_hidden(sK4(sK2,sK1),sK1) | spl6_2),
% 3.29/0.86    inference(resolution,[],[f121,f65])).
% 3.29/0.86  fof(f121,plain,(
% 3.29/0.86    ~r1_tarski(sK2,sK1) | spl6_2),
% 3.29/0.86    inference(avatar_component_clause,[],[f119])).
% 3.29/0.86  fof(f182,plain,(
% 3.29/0.86    spl6_1 | spl6_7 | spl6_1),
% 3.29/0.86    inference(avatar_split_clause,[],[f177,f115,f180,f115])).
% 3.29/0.86  fof(f177,plain,(
% 3.29/0.86    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,sK2)) ) | spl6_1),
% 3.29/0.86    inference(resolution,[],[f157,f64])).
% 3.29/0.86  fof(f157,plain,(
% 3.29/0.86    ( ! [X0,X1] : (~r2_hidden(sK4(sK1,sK2),X1) | ~r1_tarski(X0,sK2) | ~r1_tarski(X1,X0)) ) | spl6_1),
% 3.29/0.86    inference(resolution,[],[f150,f63])).
% 3.29/0.86  fof(f150,plain,(
% 3.29/0.86    ( ! [X0] : (~r2_hidden(sK4(sK1,sK2),X0) | ~r1_tarski(X0,sK2)) ) | spl6_1),
% 3.29/0.86    inference(resolution,[],[f144,f63])).
% 3.29/0.86  fof(f144,plain,(
% 3.29/0.86    ~r2_hidden(sK4(sK1,sK2),sK2) | spl6_1),
% 3.29/0.86    inference(resolution,[],[f117,f65])).
% 3.29/0.86  fof(f143,plain,(
% 3.29/0.86    ~spl6_6 | ~spl6_5),
% 3.29/0.86    inference(avatar_split_clause,[],[f111,f135,f139])).
% 3.29/0.86  fof(f111,plain,(
% 3.29/0.86    ~r1_tarski(k1_xboole_0,sK2) | ~r1_tarski(sK2,k1_xboole_0)),
% 3.29/0.86    inference(extensionality_resolution,[],[f62,f48])).
% 3.29/0.86  fof(f48,plain,(
% 3.29/0.86    k1_xboole_0 != sK2),
% 3.29/0.86    inference(cnf_transformation,[],[f31])).
% 3.29/0.86  fof(f133,plain,(
% 3.29/0.86    ~spl6_4 | ~spl6_3),
% 3.29/0.86    inference(avatar_split_clause,[],[f109,f125,f129])).
% 3.29/0.86  fof(f109,plain,(
% 3.29/0.86    ~r1_tarski(k1_xboole_0,sK1) | ~r1_tarski(sK1,k1_xboole_0)),
% 3.29/0.86    inference(extensionality_resolution,[],[f62,f47])).
% 3.29/0.86  fof(f47,plain,(
% 3.29/0.86    k1_xboole_0 != sK1),
% 3.29/0.86    inference(cnf_transformation,[],[f31])).
% 3.29/0.86  fof(f123,plain,(
% 3.29/0.86    ~spl6_2 | ~spl6_1),
% 3.29/0.86    inference(avatar_split_clause,[],[f107,f115,f119])).
% 3.29/0.86  fof(f107,plain,(
% 3.29/0.86    ~r1_tarski(sK1,sK2) | ~r1_tarski(sK2,sK1)),
% 3.29/0.86    inference(extensionality_resolution,[],[f62,f46])).
% 3.29/0.86  fof(f46,plain,(
% 3.29/0.86    sK1 != sK2),
% 3.29/0.86    inference(cnf_transformation,[],[f31])).
% 3.29/0.86  % SZS output end Proof for theBenchmark
% 3.29/0.86  % (2002)------------------------------
% 3.29/0.86  % (2002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.86  % (2002)Termination reason: Refutation
% 3.29/0.86  
% 3.29/0.86  % (2002)Memory used [KB]: 8187
% 3.29/0.86  % (2002)Time elapsed: 0.427 s
% 3.29/0.86  % (2002)------------------------------
% 3.29/0.86  % (2002)------------------------------
% 3.29/0.86  % (1988)Success in time 0.495 s
%------------------------------------------------------------------------------
