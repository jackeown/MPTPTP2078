%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:38 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 841 expanded)
%              Number of leaves         :   28 ( 263 expanded)
%              Depth                    :   40
%              Number of atoms          :  268 (1360 expanded)
%              Number of equality atoms :  138 ( 957 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f189,f1227,f1461])).

fof(f1461,plain,
    ( spl6_2
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f1460])).

fof(f1460,plain,
    ( $false
    | spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f1451,f92])).

fof(f92,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1451,plain,
    ( r1_tarski(sK1,sK3)
    | spl6_5 ),
    inference(trivial_inequality_removal,[],[f1450])).

fof(f1450,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | spl6_5 ),
    inference(superposition,[],[f81,f1438])).

fof(f1438,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | spl6_5 ),
    inference(subsumption_resolution,[],[f1436,f241])).

fof(f241,plain,
    ( k1_xboole_0 != sK0
    | spl6_5 ),
    inference(resolution,[],[f194,f170])).

fof(f170,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl6_5
  <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f194,plain,(
    ! [X6,X4,X5] :
      ( r1_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,X6))
      | k1_xboole_0 != X4 ) ),
    inference(superposition,[],[f116,f151])).

fof(f151,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f79,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f48,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,X2)
      | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1436,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(trivial_inequality_removal,[],[f1428])).

fof(f1428,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f60,f1422])).

fof(f1422,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f1413,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1413,plain,(
    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f1205,f94])).

fof(f94,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f31])).

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

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1205,plain,(
    ! [X1] : k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1))) = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
    inference(forward_demodulation,[],[f1195,f216])).

fof(f216,plain,(
    ! [X2] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = X2 ),
    inference(superposition,[],[f149,f77])).

fof(f77,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f47,f75,f75])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f149,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f78,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f1195,plain,(
    ! [X1] : k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1))) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1))))) ),
    inference(superposition,[],[f82,f1188])).

fof(f1188,plain,(
    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f1162,f42])).

fof(f42,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f1162,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(trivial_inequality_removal,[],[f1155])).

fof(f1155,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(superposition,[],[f60,f1130])).

fof(f1130,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) ),
    inference(forward_demodulation,[],[f1128,f44])).

fof(f1128,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k1_xboole_0) ),
    inference(resolution,[],[f1086,f55])).

fof(f1086,plain,(
    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1085,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f1085,plain,(
    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1016,f45])).

fof(f1016,plain,(
    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))) ),
    inference(superposition,[],[f894,f94])).

fof(f894,plain,(
    ! [X6,X8,X7,X5] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(X5,k3_xboole_0(X5,X6)),X7)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k5_xboole_0(k2_zfmisc_1(X5,X7),k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8))))) ),
    inference(superposition,[],[f874,f82])).

fof(f874,plain,(
    ! [X6,X7] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) ),
    inference(subsumption_resolution,[],[f859,f45])).

fof(f859,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6))
      | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) ) ),
    inference(superposition,[],[f81,f533])).

fof(f533,plain,(
    ! [X2,X1] : k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(subsumption_resolution,[],[f532,f83])).

fof(f532,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ) ),
    inference(forward_demodulation,[],[f523,f45])).

fof(f523,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X1,X1))
      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ) ),
    inference(superposition,[],[f463,f79])).

fof(f463,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X2,k3_xboole_0(X2,X3)))
      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X3)) ) ),
    inference(resolution,[],[f436,f55])).

fof(f436,plain,(
    ! [X8,X9] :
      ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X8),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X9))
      | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X8,k3_xboole_0(X8,X9))) ) ),
    inference(superposition,[],[f81,f394])).

fof(f394,plain,(
    ! [X10,X11] : k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X11))) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X10,k3_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f393,f216])).

fof(f393,plain,(
    ! [X10,X11] : k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X11))) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X10,k3_xboole_0(X10,X11))))) ),
    inference(forward_demodulation,[],[f392,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f392,plain,(
    ! [X10,X11] : k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X11))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X10,k3_xboole_0(X10,X11))))) ),
    inference(forward_demodulation,[],[f371,f45])).

fof(f371,plain,(
    ! [X10,X11] : k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X11))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X10,k3_xboole_0(X10,X11))))) ),
    inference(superposition,[],[f82,f94])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3))))) ),
    inference(definition_unfolding,[],[f65,f52,f76,f52,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f52])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1227,plain,
    ( spl6_1
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f1226])).

fof(f1226,plain,
    ( $false
    | spl6_1
    | spl6_5 ),
    inference(subsumption_resolution,[],[f1217,f88])).

fof(f88,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1217,plain,
    ( r1_tarski(sK0,sK2)
    | spl6_5 ),
    inference(trivial_inequality_removal,[],[f1216])).

fof(f1216,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | spl6_5 ),
    inference(superposition,[],[f81,f1206])).

fof(f1206,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | spl6_5 ),
    inference(subsumption_resolution,[],[f1203,f220])).

fof(f220,plain,
    ( k1_xboole_0 != sK1
    | spl6_5 ),
    inference(resolution,[],[f193,f170])).

fof(f193,plain,(
    ! [X2,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f117,f151])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k3_xboole_0(X1,X3)
      | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f67,f57])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1203,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f1196])).

fof(f1196,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f60,f1188])).

fof(f189,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f185,f42])).

fof(f185,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f184,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f184,plain,
    ( ! [X4] : ~ r2_hidden(X4,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f183,f153])).

fof(f153,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f79,f150])).

fof(f150,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f78,f94])).

fof(f183,plain,
    ( ! [X4] : ~ r2_hidden(X4,k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_5 ),
    inference(resolution,[],[f171,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f171,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f169])).

fof(f93,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f43,f90,f86])).

fof(f43,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:28:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (12877)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.48  % (12895)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (12870)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (12885)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.53  % (12869)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (12878)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (12889)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.53  % (12888)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.54  % (12871)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.54  % (12880)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.54  % (12868)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (12866)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.54  % (12876)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.54  % (12888)Refutation not found, incomplete strategy% (12888)------------------------------
% 1.29/0.54  % (12888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (12888)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (12888)Memory used [KB]: 10746
% 1.29/0.54  % (12888)Time elapsed: 0.090 s
% 1.29/0.54  % (12888)------------------------------
% 1.29/0.54  % (12888)------------------------------
% 1.47/0.54  % (12893)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.54  % (12891)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.54  % (12892)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.54  % (12881)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.55  % (12894)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.55  % (12872)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.55  % (12886)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.55  % (12875)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.55  % (12884)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.55  % (12873)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.55  % (12887)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.55  % (12882)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.55  % (12879)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.56  % (12883)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.56  % (12883)Refutation not found, incomplete strategy% (12883)------------------------------
% 1.47/0.56  % (12883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (12883)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (12883)Memory used [KB]: 10618
% 1.47/0.56  % (12883)Time elapsed: 0.149 s
% 1.47/0.56  % (12883)------------------------------
% 1.47/0.56  % (12883)------------------------------
% 1.47/0.57  % (12890)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.58  % (12867)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.47/0.58  % (12874)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.03/0.64  % (12869)Refutation found. Thanks to Tanya!
% 2.03/0.64  % SZS status Theorem for theBenchmark
% 2.03/0.64  % SZS output start Proof for theBenchmark
% 2.03/0.64  fof(f1462,plain,(
% 2.03/0.64    $false),
% 2.03/0.64    inference(avatar_sat_refutation,[],[f93,f189,f1227,f1461])).
% 2.03/0.64  fof(f1461,plain,(
% 2.03/0.64    spl6_2 | spl6_5),
% 2.03/0.64    inference(avatar_contradiction_clause,[],[f1460])).
% 2.03/0.64  fof(f1460,plain,(
% 2.03/0.64    $false | (spl6_2 | spl6_5)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1451,f92])).
% 2.03/0.64  fof(f92,plain,(
% 2.03/0.64    ~r1_tarski(sK1,sK3) | spl6_2),
% 2.03/0.64    inference(avatar_component_clause,[],[f90])).
% 2.03/0.64  fof(f90,plain,(
% 2.03/0.64    spl6_2 <=> r1_tarski(sK1,sK3)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.03/0.64  fof(f1451,plain,(
% 2.03/0.64    r1_tarski(sK1,sK3) | spl6_5),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f1450])).
% 2.03/0.64  fof(f1450,plain,(
% 2.03/0.64    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | spl6_5),
% 2.03/0.64    inference(superposition,[],[f81,f1438])).
% 2.03/0.64  fof(f1438,plain,(
% 2.03/0.64    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | spl6_5),
% 2.03/0.64    inference(subsumption_resolution,[],[f1436,f241])).
% 2.03/0.64  fof(f241,plain,(
% 2.03/0.64    k1_xboole_0 != sK0 | spl6_5),
% 2.03/0.64    inference(resolution,[],[f194,f170])).
% 2.03/0.64  fof(f170,plain,(
% 2.03/0.64    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | spl6_5),
% 2.03/0.64    inference(avatar_component_clause,[],[f169])).
% 2.03/0.64  fof(f169,plain,(
% 2.03/0.64    spl6_5 <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.03/0.64  fof(f194,plain,(
% 2.03/0.64    ( ! [X6,X4,X5] : (r1_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,X6)) | k1_xboole_0 != X4) )),
% 2.03/0.64    inference(superposition,[],[f116,f151])).
% 2.03/0.64  fof(f151,plain,(
% 2.03/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.03/0.64    inference(superposition,[],[f79,f78])).
% 2.03/0.64  fof(f78,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 2.03/0.64    inference(definition_unfolding,[],[f48,f76])).
% 2.03/0.64  fof(f76,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.03/0.64    inference(definition_unfolding,[],[f50,f75])).
% 2.03/0.64  fof(f75,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f51,f74])).
% 2.03/0.64  fof(f74,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f63,f73])).
% 2.03/0.64  fof(f73,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f64,f72])).
% 2.03/0.64  fof(f72,plain,(
% 2.03/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f68,f71])).
% 2.03/0.64  fof(f71,plain,(
% 2.03/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f69,f70])).
% 2.03/0.64  fof(f70,plain,(
% 2.03/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f17])).
% 2.03/0.64  fof(f17,axiom,(
% 2.03/0.64    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.03/0.64  fof(f69,plain,(
% 2.03/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f16])).
% 2.03/0.64  fof(f16,axiom,(
% 2.03/0.64    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.03/0.64  fof(f68,plain,(
% 2.03/0.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f15])).
% 2.03/0.64  fof(f15,axiom,(
% 2.03/0.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.03/0.64  fof(f64,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f14])).
% 2.03/0.64  fof(f14,axiom,(
% 2.03/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.03/0.64  fof(f63,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f13])).
% 2.03/0.64  fof(f13,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.03/0.64  fof(f51,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f12])).
% 2.03/0.64  fof(f12,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.03/0.64  fof(f50,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f18])).
% 2.03/0.64  fof(f18,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.03/0.64  fof(f48,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f7])).
% 2.03/0.64  fof(f7,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.03/0.64  fof(f79,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 2.03/0.64    inference(definition_unfolding,[],[f49,f76])).
% 2.03/0.64  fof(f49,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f6])).
% 2.03/0.64  fof(f6,axiom,(
% 2.03/0.64    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.03/0.64  fof(f116,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k3_xboole_0(X0,X2) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.03/0.64    inference(resolution,[],[f66,f57])).
% 2.03/0.64  fof(f57,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f37])).
% 2.03/0.64  fof(f37,plain,(
% 2.03/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(nnf_transformation,[],[f1])).
% 2.03/0.64  fof(f1,axiom,(
% 2.03/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.03/0.64  fof(f66,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f30])).
% 2.03/0.64  fof(f30,plain,(
% 2.03/0.64    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(ennf_transformation,[],[f21])).
% 2.03/0.64  fof(f21,axiom,(
% 2.03/0.64    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 2.03/0.64  fof(f1436,plain,(
% 2.03/0.64    k1_xboole_0 = sK0 | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f1428])).
% 2.03/0.64  fof(f1428,plain,(
% 2.03/0.64    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 2.03/0.64    inference(superposition,[],[f60,f1422])).
% 2.03/0.64  fof(f1422,plain,(
% 2.03/0.64    k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))),
% 2.03/0.64    inference(forward_demodulation,[],[f1413,f45])).
% 2.03/0.64  fof(f45,plain,(
% 2.03/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f10])).
% 2.03/0.64  fof(f10,axiom,(
% 2.03/0.64    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.03/0.64  fof(f1413,plain,(
% 2.03/0.64    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))),
% 2.03/0.64    inference(superposition,[],[f1205,f94])).
% 2.03/0.64  fof(f94,plain,(
% 2.03/0.64    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.03/0.64    inference(resolution,[],[f55,f41])).
% 2.03/0.64  fof(f41,plain,(
% 2.03/0.64    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.03/0.64    inference(cnf_transformation,[],[f32])).
% 2.03/0.64  fof(f32,plain,(
% 2.03/0.64    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f31])).
% 2.03/0.64  fof(f31,plain,(
% 2.03/0.64    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f26,plain,(
% 2.03/0.64    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.03/0.64    inference(flattening,[],[f25])).
% 2.03/0.64  fof(f25,plain,(
% 2.03/0.64    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.03/0.64    inference(ennf_transformation,[],[f23])).
% 2.03/0.64  fof(f23,negated_conjecture,(
% 2.03/0.64    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.03/0.64    inference(negated_conjecture,[],[f22])).
% 2.03/0.64  fof(f22,conjecture,(
% 2.03/0.64    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 2.03/0.64  fof(f55,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f29])).
% 2.03/0.64  fof(f29,plain,(
% 2.03/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.03/0.64    inference(ennf_transformation,[],[f8])).
% 2.03/0.64  fof(f8,axiom,(
% 2.03/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.03/0.64  fof(f1205,plain,(
% 2.03/0.64    ( ! [X1] : (k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1))) = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))) )),
% 2.03/0.64    inference(forward_demodulation,[],[f1195,f216])).
% 2.03/0.64  fof(f216,plain,(
% 2.03/0.64    ( ! [X2] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = X2) )),
% 2.03/0.64    inference(superposition,[],[f149,f77])).
% 2.03/0.64  fof(f77,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f47,f75,f75])).
% 2.03/0.64  fof(f47,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f11])).
% 2.03/0.64  fof(f11,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.03/0.64  fof(f149,plain,(
% 2.03/0.64    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 2.03/0.64    inference(superposition,[],[f78,f44])).
% 2.03/0.64  fof(f44,plain,(
% 2.03/0.64    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f9])).
% 2.03/0.64  fof(f9,axiom,(
% 2.03/0.64    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.03/0.64  fof(f1195,plain,(
% 2.03/0.64    ( ! [X1] : (k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1))) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))))) )),
% 2.03/0.64    inference(superposition,[],[f82,f1188])).
% 2.03/0.64  fof(f1188,plain,(
% 2.03/0.64    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1162,f42])).
% 2.03/0.64  fof(f42,plain,(
% 2.03/0.64    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 2.03/0.64    inference(cnf_transformation,[],[f32])).
% 2.03/0.64  fof(f1162,plain,(
% 2.03/0.64    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f1155])).
% 2.03/0.64  fof(f1155,plain,(
% 2.03/0.64    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 2.03/0.64    inference(superposition,[],[f60,f1130])).
% 2.03/0.64  fof(f1130,plain,(
% 2.03/0.64    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1128,f44])).
% 2.03/0.64  fof(f1128,plain,(
% 2.03/0.64    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k1_xboole_0)),
% 2.03/0.64    inference(resolution,[],[f1086,f55])).
% 2.03/0.64  fof(f1086,plain,(
% 2.03/0.64    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k1_xboole_0)),
% 2.03/0.64    inference(forward_demodulation,[],[f1085,f83])).
% 2.03/0.64  fof(f83,plain,(
% 2.03/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.03/0.64    inference(equality_resolution,[],[f62])).
% 2.03/0.64  fof(f62,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.03/0.64    inference(cnf_transformation,[],[f40])).
% 2.03/0.64  fof(f40,plain,(
% 2.03/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.03/0.64    inference(flattening,[],[f39])).
% 2.03/0.64  fof(f39,plain,(
% 2.03/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.03/0.64    inference(nnf_transformation,[],[f19])).
% 2.03/0.64  fof(f19,axiom,(
% 2.03/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.03/0.64  fof(f1085,plain,(
% 2.03/0.64    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k1_xboole_0))),
% 2.03/0.64    inference(forward_demodulation,[],[f1016,f45])).
% 2.03/0.64  fof(f1016,plain,(
% 2.03/0.64    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))))),
% 2.03/0.64    inference(superposition,[],[f894,f94])).
% 2.03/0.64  fof(f894,plain,(
% 2.03/0.64    ( ! [X6,X8,X7,X5] : (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(X5,k3_xboole_0(X5,X6)),X7)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k5_xboole_0(k2_zfmisc_1(X5,X7),k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8)))))) )),
% 2.03/0.64    inference(superposition,[],[f874,f82])).
% 2.03/0.64  fof(f874,plain,(
% 2.03/0.64    ( ! [X6,X7] : (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))))) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f859,f45])).
% 2.03/0.64  fof(f859,plain,(
% 2.03/0.64    ( ! [X6,X7] : (k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6)) | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))))) )),
% 2.03/0.64    inference(superposition,[],[f81,f533])).
% 2.03/0.64  fof(f533,plain,(
% 2.03/0.64    ( ! [X2,X1] : (k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f532,f83])).
% 2.03/0.64  fof(f532,plain,(
% 2.03/0.64    ( ! [X2,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0) | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) )),
% 2.03/0.64    inference(forward_demodulation,[],[f523,f45])).
% 2.03/0.64  fof(f523,plain,(
% 2.03/0.64    ( ! [X2,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X1,X1)) | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) )),
% 2.03/0.64    inference(superposition,[],[f463,f79])).
% 2.03/0.64  fof(f463,plain,(
% 2.03/0.64    ( ! [X2,X3] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2) = k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X3))) )),
% 2.03/0.64    inference(resolution,[],[f436,f55])).
% 2.03/0.64  fof(f436,plain,(
% 2.03/0.64    ( ! [X8,X9] : (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X8),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X9)) | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X8,k3_xboole_0(X8,X9)))) )),
% 2.03/0.64    inference(superposition,[],[f81,f394])).
% 2.03/0.64  fof(f394,plain,(
% 2.03/0.64    ( ! [X10,X11] : (k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X11))) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X10,k3_xboole_0(X10,X11)))) )),
% 2.03/0.64    inference(forward_demodulation,[],[f393,f216])).
% 2.03/0.64  fof(f393,plain,(
% 2.03/0.64    ( ! [X10,X11] : (k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X11))) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X10,k3_xboole_0(X10,X11)))))) )),
% 2.03/0.64    inference(forward_demodulation,[],[f392,f84])).
% 2.03/0.64  fof(f84,plain,(
% 2.03/0.64    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.03/0.64    inference(equality_resolution,[],[f61])).
% 2.03/0.64  fof(f61,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f40])).
% 2.03/0.64  fof(f392,plain,(
% 2.03/0.64    ( ! [X10,X11] : (k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X11))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X10,k3_xboole_0(X10,X11)))))) )),
% 2.03/0.64    inference(forward_demodulation,[],[f371,f45])).
% 2.03/0.64  fof(f371,plain,(
% 2.03/0.64    ( ! [X10,X11] : (k5_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X11))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),X10),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k5_xboole_0(X10,k3_xboole_0(X10,X11)))))) )),
% 2.03/0.64    inference(superposition,[],[f82,f94])).
% 2.03/0.64  fof(f82,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3)))))) )),
% 2.03/0.64    inference(definition_unfolding,[],[f65,f52,f76,f52,f52])).
% 2.03/0.64  fof(f52,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f5])).
% 2.03/0.64  fof(f5,axiom,(
% 2.03/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.03/0.64  fof(f65,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f20])).
% 2.03/0.64  fof(f20,axiom,(
% 2.03/0.64    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).
% 2.03/0.64  fof(f60,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 2.03/0.64    inference(cnf_transformation,[],[f40])).
% 2.03/0.64  fof(f81,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f58,f52])).
% 2.03/0.64  fof(f58,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f38])).
% 2.03/0.64  fof(f38,plain,(
% 2.03/0.64    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.03/0.64    inference(nnf_transformation,[],[f4])).
% 2.03/0.64  fof(f4,axiom,(
% 2.03/0.64    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.03/0.64  fof(f1227,plain,(
% 2.03/0.64    spl6_1 | spl6_5),
% 2.03/0.64    inference(avatar_contradiction_clause,[],[f1226])).
% 2.03/0.64  fof(f1226,plain,(
% 2.03/0.64    $false | (spl6_1 | spl6_5)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1217,f88])).
% 2.03/0.64  fof(f88,plain,(
% 2.03/0.64    ~r1_tarski(sK0,sK2) | spl6_1),
% 2.03/0.64    inference(avatar_component_clause,[],[f86])).
% 2.03/0.64  fof(f86,plain,(
% 2.03/0.64    spl6_1 <=> r1_tarski(sK0,sK2)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.03/0.64  fof(f1217,plain,(
% 2.03/0.64    r1_tarski(sK0,sK2) | spl6_5),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f1216])).
% 2.03/0.64  fof(f1216,plain,(
% 2.03/0.64    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | spl6_5),
% 2.03/0.64    inference(superposition,[],[f81,f1206])).
% 2.03/0.64  fof(f1206,plain,(
% 2.03/0.64    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | spl6_5),
% 2.03/0.64    inference(subsumption_resolution,[],[f1203,f220])).
% 2.03/0.64  fof(f220,plain,(
% 2.03/0.64    k1_xboole_0 != sK1 | spl6_5),
% 2.03/0.64    inference(resolution,[],[f193,f170])).
% 2.03/0.64  fof(f193,plain,(
% 2.03/0.64    ( ! [X2,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1)) | k1_xboole_0 != X1) )),
% 2.03/0.64    inference(superposition,[],[f117,f151])).
% 2.03/0.64  fof(f117,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k3_xboole_0(X1,X3) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.03/0.64    inference(resolution,[],[f67,f57])).
% 2.03/0.64  fof(f67,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f30])).
% 2.03/0.64  fof(f1203,plain,(
% 2.03/0.64    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f1196])).
% 2.03/0.64  fof(f1196,plain,(
% 2.03/0.64    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1),
% 2.03/0.64    inference(superposition,[],[f60,f1188])).
% 2.03/0.64  fof(f189,plain,(
% 2.03/0.64    ~spl6_5),
% 2.03/0.64    inference(avatar_contradiction_clause,[],[f188])).
% 2.03/0.64  fof(f188,plain,(
% 2.03/0.64    $false | ~spl6_5),
% 2.03/0.64    inference(subsumption_resolution,[],[f185,f42])).
% 2.03/0.64  fof(f185,plain,(
% 2.03/0.64    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_5),
% 2.03/0.64    inference(resolution,[],[f184,f46])).
% 2.03/0.64  fof(f46,plain,(
% 2.03/0.64    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f34])).
% 2.03/0.64  fof(f34,plain,(
% 2.03/0.64    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f33])).
% 2.03/0.64  fof(f33,plain,(
% 2.03/0.64    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f27,plain,(
% 2.03/0.64    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.03/0.64    inference(ennf_transformation,[],[f3])).
% 2.03/0.64  fof(f3,axiom,(
% 2.03/0.64    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.03/0.64  fof(f184,plain,(
% 2.03/0.64    ( ! [X4] : (~r2_hidden(X4,k2_zfmisc_1(sK0,sK1))) ) | ~spl6_5),
% 2.03/0.64    inference(forward_demodulation,[],[f183,f153])).
% 2.03/0.64  fof(f153,plain,(
% 2.03/0.64    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 2.03/0.64    inference(superposition,[],[f79,f150])).
% 2.03/0.64  fof(f150,plain,(
% 2.03/0.64    k2_zfmisc_1(sK0,sK1) = k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))),
% 2.03/0.64    inference(superposition,[],[f78,f94])).
% 2.03/0.64  fof(f183,plain,(
% 2.03/0.64    ( ! [X4] : (~r2_hidden(X4,k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))) ) | ~spl6_5),
% 2.03/0.64    inference(resolution,[],[f171,f54])).
% 2.03/0.64  fof(f54,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f36])).
% 2.03/0.64  fof(f36,plain,(
% 2.03/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f35])).
% 2.03/0.64  fof(f35,plain,(
% 2.03/0.64    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f28,plain,(
% 2.03/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(ennf_transformation,[],[f24])).
% 2.03/0.64  fof(f24,plain,(
% 2.03/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(rectify,[],[f2])).
% 2.03/0.64  fof(f2,axiom,(
% 2.03/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.03/0.64  fof(f171,plain,(
% 2.03/0.64    r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | ~spl6_5),
% 2.03/0.64    inference(avatar_component_clause,[],[f169])).
% 2.03/0.64  fof(f93,plain,(
% 2.03/0.64    ~spl6_1 | ~spl6_2),
% 2.03/0.64    inference(avatar_split_clause,[],[f43,f90,f86])).
% 2.03/0.64  fof(f43,plain,(
% 2.03/0.64    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 2.03/0.64    inference(cnf_transformation,[],[f32])).
% 2.03/0.64  % SZS output end Proof for theBenchmark
% 2.03/0.64  % (12869)------------------------------
% 2.03/0.64  % (12869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.64  % (12869)Termination reason: Refutation
% 2.03/0.64  
% 2.03/0.64  % (12869)Memory used [KB]: 11769
% 2.03/0.64  % (12869)Time elapsed: 0.228 s
% 2.03/0.64  % (12869)------------------------------
% 2.03/0.64  % (12869)------------------------------
% 2.03/0.65  % (12865)Success in time 0.283 s
%------------------------------------------------------------------------------
