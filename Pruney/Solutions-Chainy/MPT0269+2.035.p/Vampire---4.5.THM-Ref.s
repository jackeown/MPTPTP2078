%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:51 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 383 expanded)
%              Number of leaves         :   26 ( 124 expanded)
%              Depth                    :   24
%              Number of atoms          :  228 ( 561 expanded)
%              Number of equality atoms :  116 ( 437 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1456,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1455,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK1 != k1_tarski(sK2)
    & k1_xboole_0 != sK1
    & k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK1 != k1_tarski(sK2)
      & k1_xboole_0 != sK1
      & k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f1455,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1450,f1441])).

fof(f1441,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f1434,f91])).

fof(f91,plain,(
    sK1 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f51,f90])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f78,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    sK1 != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f1434,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK1 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(resolution,[],[f1394,f332])).

fof(f332,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 ) ),
    inference(resolution,[],[f154,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f154,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f98,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f90])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1394,plain,(
    r1_tarski(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[],[f95,f354])).

fof(f354,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f353,f54])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f353,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f336,f132])).

fof(f132,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f108,f126])).

fof(f126,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f119,f54])).

fof(f119,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f108,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f108,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f77,f52])).

fof(f77,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f336,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0))) ),
    inference(superposition,[],[f179,f52])).

fof(f179,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)))) = X0 ),
    inference(forward_demodulation,[],[f178,f126])).

fof(f178,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)))) ),
    inference(forward_demodulation,[],[f177,f77])).

fof(f177,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),X0))) ),
    inference(forward_demodulation,[],[f173,f77])).

fof(f173,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),X0)) ),
    inference(superposition,[],[f77,f163])).

fof(f163,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(forward_demodulation,[],[f92,f77])).

fof(f92,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(definition_unfolding,[],[f49,f89,f90])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f61,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f86])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f58,f87])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1450,plain,
    ( r2_hidden(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f56,f1442])).

fof(f1442,plain,(
    sK2 = sK3(sK1) ),
    inference(subsumption_resolution,[],[f1437,f50])).

fof(f1437,plain,
    ( sK2 = sK3(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1394,f304])).

fof(f304,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))
      | sK3(X4) = X5
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f117,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f64,f56])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f101,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
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

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f101,plain,(
    ! [X0] : sP0(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f71,f90])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f12,f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.53  % (23541)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (23558)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (23541)Refutation not found, incomplete strategy% (23541)------------------------------
% 0.20/0.54  % (23541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23550)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (23567)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (23541)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (23541)Memory used [KB]: 10746
% 0.20/0.55  % (23541)Time elapsed: 0.125 s
% 0.20/0.55  % (23541)------------------------------
% 0.20/0.55  % (23541)------------------------------
% 0.20/0.55  % (23545)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (23543)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.56  % (23562)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (23552)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (23560)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % (23554)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.57  % (23555)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.57  % (23553)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (23544)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.57  % (23546)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.57  % (23564)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.58  % (23570)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.58  % (23559)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.58  % (23562)Refutation not found, incomplete strategy% (23562)------------------------------
% 0.20/0.58  % (23562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (23563)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.59  % (23552)Refutation not found, incomplete strategy% (23552)------------------------------
% 0.20/0.59  % (23552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (23552)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (23552)Memory used [KB]: 10618
% 0.20/0.59  % (23552)Time elapsed: 0.161 s
% 0.20/0.59  % (23552)------------------------------
% 0.20/0.59  % (23552)------------------------------
% 1.81/0.59  % (23562)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.59  
% 1.81/0.59  % (23562)Memory used [KB]: 1791
% 1.81/0.59  % (23562)Time elapsed: 0.153 s
% 1.81/0.59  % (23562)------------------------------
% 1.81/0.59  % (23562)------------------------------
% 1.81/0.59  % (23569)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.81/0.60  % (23556)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.81/0.60  % (23551)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.81/0.60  % (23551)Refutation not found, incomplete strategy% (23551)------------------------------
% 1.81/0.60  % (23551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (23551)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (23551)Memory used [KB]: 10618
% 1.81/0.60  % (23551)Time elapsed: 0.186 s
% 1.81/0.60  % (23551)------------------------------
% 1.81/0.60  % (23551)------------------------------
% 1.81/0.60  % (23561)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.81/0.61  % (23540)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.81/0.61  % (23561)Refutation not found, incomplete strategy% (23561)------------------------------
% 1.81/0.61  % (23561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (23561)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (23561)Memory used [KB]: 10746
% 1.81/0.61  % (23561)Time elapsed: 0.196 s
% 1.81/0.61  % (23561)------------------------------
% 1.81/0.61  % (23561)------------------------------
% 1.81/0.61  % (23568)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.81/0.61  % (23548)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.81/0.61  % (23549)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.01/0.62  % (23566)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.01/0.62  % (23557)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.01/0.63  % (23565)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.01/0.63  % (23539)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 2.01/0.64  % (23549)Refutation not found, incomplete strategy% (23549)------------------------------
% 2.01/0.64  % (23549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.64  % (23549)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.64  
% 2.01/0.64  % (23549)Memory used [KB]: 10746
% 2.01/0.64  % (23549)Time elapsed: 0.184 s
% 2.01/0.64  % (23549)------------------------------
% 2.01/0.64  % (23549)------------------------------
% 2.26/0.67  % (23570)Refutation found. Thanks to Tanya!
% 2.26/0.67  % SZS status Theorem for theBenchmark
% 2.26/0.67  % SZS output start Proof for theBenchmark
% 2.26/0.67  fof(f1456,plain,(
% 2.26/0.67    $false),
% 2.26/0.67    inference(subsumption_resolution,[],[f1455,f50])).
% 2.26/0.67  fof(f50,plain,(
% 2.26/0.67    k1_xboole_0 != sK1),
% 2.26/0.67    inference(cnf_transformation,[],[f36])).
% 2.26/0.67  fof(f36,plain,(
% 2.26/0.67    sK1 != k1_tarski(sK2) & k1_xboole_0 != sK1 & k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK2))),
% 2.26/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f35])).
% 2.26/0.67  fof(f35,plain,(
% 2.26/0.67    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK1 != k1_tarski(sK2) & k1_xboole_0 != sK1 & k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK2)))),
% 2.26/0.67    introduced(choice_axiom,[])).
% 2.26/0.67  fof(f27,plain,(
% 2.26/0.67    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.26/0.67    inference(ennf_transformation,[],[f24])).
% 2.26/0.67  fof(f24,negated_conjecture,(
% 2.26/0.67    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.26/0.67    inference(negated_conjecture,[],[f23])).
% 2.26/0.67  fof(f23,conjecture,(
% 2.26/0.67    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 2.26/0.67  fof(f1455,plain,(
% 2.26/0.67    k1_xboole_0 = sK1),
% 2.26/0.67    inference(subsumption_resolution,[],[f1450,f1441])).
% 2.26/0.67  fof(f1441,plain,(
% 2.26/0.67    ~r2_hidden(sK2,sK1)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1434,f91])).
% 2.26/0.67  fof(f91,plain,(
% 2.26/0.67    sK1 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 2.26/0.67    inference(definition_unfolding,[],[f51,f90])).
% 2.26/0.67  fof(f90,plain,(
% 2.26/0.67    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.26/0.67    inference(definition_unfolding,[],[f55,f86])).
% 2.26/0.67  fof(f86,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.26/0.67    inference(definition_unfolding,[],[f60,f85])).
% 2.26/0.67  fof(f85,plain,(
% 2.26/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.26/0.67    inference(definition_unfolding,[],[f76,f84])).
% 2.26/0.67  fof(f84,plain,(
% 2.26/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.26/0.67    inference(definition_unfolding,[],[f78,f83])).
% 2.26/0.67  fof(f83,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.26/0.67    inference(definition_unfolding,[],[f79,f82])).
% 2.26/0.67  fof(f82,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.26/0.67    inference(definition_unfolding,[],[f80,f81])).
% 2.26/0.67  fof(f81,plain,(
% 2.26/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f19])).
% 2.26/0.67  fof(f19,axiom,(
% 2.26/0.67    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.26/0.67  fof(f80,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f18])).
% 2.26/0.67  fof(f18,axiom,(
% 2.26/0.67    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.26/0.67  fof(f79,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f17])).
% 2.26/0.67  fof(f17,axiom,(
% 2.26/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.26/0.67  fof(f78,plain,(
% 2.26/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f16])).
% 2.26/0.67  fof(f16,axiom,(
% 2.26/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.26/0.67  fof(f76,plain,(
% 2.26/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f15])).
% 2.26/0.67  fof(f15,axiom,(
% 2.26/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.26/0.67  fof(f60,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f14])).
% 2.26/0.67  fof(f14,axiom,(
% 2.26/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.26/0.67  fof(f55,plain,(
% 2.26/0.67    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f13])).
% 2.26/0.67  fof(f13,axiom,(
% 2.26/0.67    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.26/0.67  fof(f51,plain,(
% 2.26/0.67    sK1 != k1_tarski(sK2)),
% 2.26/0.67    inference(cnf_transformation,[],[f36])).
% 2.26/0.67  fof(f1434,plain,(
% 2.26/0.67    ~r2_hidden(sK2,sK1) | sK1 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 2.26/0.67    inference(resolution,[],[f1394,f332])).
% 2.26/0.67  fof(f332,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1) )),
% 2.26/0.67    inference(resolution,[],[f154,f75])).
% 2.26/0.67  fof(f75,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f32])).
% 2.26/0.67  fof(f32,plain,(
% 2.26/0.67    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 2.26/0.67    inference(ennf_transformation,[],[f7])).
% 2.26/0.67  fof(f7,axiom,(
% 2.26/0.67    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 2.26/0.67  fof(f154,plain,(
% 2.26/0.67    ( ! [X0,X1] : (r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | ~r2_hidden(X0,X1)) )),
% 2.26/0.67    inference(resolution,[],[f98,f63])).
% 2.26/0.67  fof(f63,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f30])).
% 2.26/0.67  fof(f30,plain,(
% 2.26/0.67    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 2.26/0.67    inference(flattening,[],[f29])).
% 2.26/0.67  fof(f29,plain,(
% 2.26/0.67    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 2.26/0.67    inference(ennf_transformation,[],[f26])).
% 2.26/0.67  fof(f26,plain,(
% 2.26/0.67    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 2.26/0.67    inference(unused_predicate_definition_removal,[],[f2])).
% 2.26/0.67  fof(f2,axiom,(
% 2.26/0.67    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 2.26/0.67  fof(f98,plain,(
% 2.26/0.67    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.26/0.67    inference(definition_unfolding,[],[f74,f90])).
% 2.26/0.67  fof(f74,plain,(
% 2.26/0.67    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f48])).
% 2.26/0.67  fof(f48,plain,(
% 2.26/0.67    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.26/0.67    inference(nnf_transformation,[],[f20])).
% 2.26/0.67  fof(f20,axiom,(
% 2.26/0.67    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.26/0.67  fof(f1394,plain,(
% 2.26/0.67    r1_tarski(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 2.26/0.67    inference(superposition,[],[f95,f354])).
% 2.26/0.67  fof(f354,plain,(
% 2.26/0.67    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 2.26/0.67    inference(forward_demodulation,[],[f353,f54])).
% 2.26/0.67  fof(f54,plain,(
% 2.26/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.26/0.67    inference(cnf_transformation,[],[f6])).
% 2.26/0.67  fof(f6,axiom,(
% 2.26/0.67    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.26/0.67  fof(f353,plain,(
% 2.26/0.67    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0)),
% 2.26/0.67    inference(forward_demodulation,[],[f336,f132])).
% 2.26/0.67  fof(f132,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.26/0.67    inference(backward_demodulation,[],[f108,f126])).
% 2.26/0.67  fof(f126,plain,(
% 2.26/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.26/0.67    inference(forward_demodulation,[],[f119,f54])).
% 2.26/0.67  fof(f119,plain,(
% 2.26/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.26/0.67    inference(superposition,[],[f108,f52])).
% 2.26/0.67  fof(f52,plain,(
% 2.26/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f10])).
% 2.26/0.67  fof(f10,axiom,(
% 2.26/0.67    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.26/0.67  fof(f108,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.26/0.67    inference(superposition,[],[f77,f52])).
% 2.26/0.67  fof(f77,plain,(
% 2.26/0.67    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.26/0.67    inference(cnf_transformation,[],[f9])).
% 2.26/0.67  fof(f9,axiom,(
% 2.26/0.67    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.26/0.67  fof(f336,plain,(
% 2.26/0.67    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0)))),
% 2.26/0.67    inference(superposition,[],[f179,f52])).
% 2.26/0.67  fof(f179,plain,(
% 2.26/0.67    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)))) = X0) )),
% 2.26/0.67    inference(forward_demodulation,[],[f178,f126])).
% 2.26/0.67  fof(f178,plain,(
% 2.26/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0))))) )),
% 2.26/0.67    inference(forward_demodulation,[],[f177,f77])).
% 2.26/0.67  fof(f177,plain,(
% 2.26/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),X0)))) )),
% 2.26/0.67    inference(forward_demodulation,[],[f173,f77])).
% 2.26/0.67  fof(f173,plain,(
% 2.26/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),X0))) )),
% 2.26/0.67    inference(superposition,[],[f77,f163])).
% 2.26/0.67  fof(f163,plain,(
% 2.26/0.67    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 2.26/0.67    inference(forward_demodulation,[],[f92,f77])).
% 2.26/0.67  fof(f92,plain,(
% 2.26/0.67    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 2.26/0.67    inference(definition_unfolding,[],[f49,f89,f90])).
% 2.26/0.67  fof(f89,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.26/0.67    inference(definition_unfolding,[],[f61,f88])).
% 2.26/0.67  fof(f88,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.26/0.67    inference(definition_unfolding,[],[f62,f87])).
% 2.26/0.67  fof(f87,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.26/0.67    inference(definition_unfolding,[],[f59,f86])).
% 2.26/0.67  fof(f59,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.26/0.67    inference(cnf_transformation,[],[f21])).
% 2.26/0.67  fof(f21,axiom,(
% 2.26/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.26/0.67  fof(f62,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.26/0.67    inference(cnf_transformation,[],[f11])).
% 2.26/0.67  fof(f11,axiom,(
% 2.26/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.26/0.67  fof(f61,plain,(
% 2.26/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.26/0.67    inference(cnf_transformation,[],[f5])).
% 2.26/0.67  fof(f5,axiom,(
% 2.26/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.26/0.67  fof(f49,plain,(
% 2.26/0.67    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK2))),
% 2.26/0.67    inference(cnf_transformation,[],[f36])).
% 2.26/0.67  fof(f95,plain,(
% 2.26/0.67    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.26/0.67    inference(definition_unfolding,[],[f58,f87])).
% 2.26/0.67  fof(f58,plain,(
% 2.26/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.26/0.67    inference(cnf_transformation,[],[f8])).
% 2.26/0.67  fof(f8,axiom,(
% 2.26/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.26/0.67  fof(f1450,plain,(
% 2.26/0.67    r2_hidden(sK2,sK1) | k1_xboole_0 = sK1),
% 2.26/0.67    inference(superposition,[],[f56,f1442])).
% 2.26/0.67  fof(f1442,plain,(
% 2.26/0.67    sK2 = sK3(sK1)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1437,f50])).
% 2.26/0.67  fof(f1437,plain,(
% 2.26/0.67    sK2 = sK3(sK1) | k1_xboole_0 = sK1),
% 2.26/0.67    inference(resolution,[],[f1394,f304])).
% 2.26/0.67  fof(f304,plain,(
% 2.26/0.67    ( ! [X4,X5] : (~r1_tarski(X4,k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)) | sK3(X4) = X5 | k1_xboole_0 = X4) )),
% 2.26/0.67    inference(resolution,[],[f117,f105])).
% 2.26/0.67  fof(f105,plain,(
% 2.26/0.67    ( ! [X0,X1] : (r2_hidden(sK3(X0),X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 2.26/0.67    inference(resolution,[],[f64,f56])).
% 2.26/0.67  fof(f64,plain,(
% 2.26/0.67    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f42])).
% 2.26/0.67  fof(f42,plain,(
% 2.26/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.26/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 2.26/0.67  fof(f41,plain,(
% 2.26/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.26/0.67    introduced(choice_axiom,[])).
% 2.26/0.67  fof(f40,plain,(
% 2.26/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.26/0.67    inference(rectify,[],[f39])).
% 2.26/0.67  fof(f39,plain,(
% 2.26/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.26/0.67    inference(nnf_transformation,[],[f31])).
% 2.26/0.67  fof(f31,plain,(
% 2.26/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f1])).
% 2.26/0.67  fof(f1,axiom,(
% 2.26/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.26/0.67  fof(f117,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 2.26/0.67    inference(resolution,[],[f101,f67])).
% 2.26/0.67  fof(f67,plain,(
% 2.26/0.67    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 2.26/0.67    inference(cnf_transformation,[],[f46])).
% 2.26/0.67  fof(f46,plain,(
% 2.26/0.67    ! [X0,X1] : ((sP0(X0,X1) | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.26/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 2.26/0.67  fof(f45,plain,(
% 2.26/0.67    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.26/0.67    introduced(choice_axiom,[])).
% 2.26/0.67  fof(f44,plain,(
% 2.26/0.67    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.26/0.67    inference(rectify,[],[f43])).
% 2.26/0.67  fof(f43,plain,(
% 2.26/0.67    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 2.26/0.67    inference(nnf_transformation,[],[f33])).
% 2.26/0.67  fof(f33,plain,(
% 2.26/0.67    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.26/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.26/0.67  fof(f101,plain,(
% 2.26/0.67    ( ! [X0] : (sP0(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 2.26/0.67    inference(equality_resolution,[],[f97])).
% 2.26/0.67  fof(f97,plain,(
% 2.26/0.67    ( ! [X0,X1] : (sP0(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.26/0.67    inference(definition_unfolding,[],[f71,f90])).
% 2.26/0.67  fof(f71,plain,(
% 2.26/0.67    ( ! [X0,X1] : (sP0(X0,X1) | k1_tarski(X0) != X1) )),
% 2.26/0.67    inference(cnf_transformation,[],[f47])).
% 2.26/0.67  fof(f47,plain,(
% 2.26/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_tarski(X0) != X1))),
% 2.26/0.67    inference(nnf_transformation,[],[f34])).
% 2.26/0.67  fof(f34,plain,(
% 2.26/0.67    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP0(X0,X1))),
% 2.26/0.67    inference(definition_folding,[],[f12,f33])).
% 2.26/0.67  fof(f12,axiom,(
% 2.26/0.67    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.26/0.67  fof(f56,plain,(
% 2.26/0.67    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.26/0.67    inference(cnf_transformation,[],[f38])).
% 2.26/0.67  fof(f38,plain,(
% 2.26/0.67    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.26/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f37])).
% 2.26/0.67  fof(f37,plain,(
% 2.26/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.26/0.67    introduced(choice_axiom,[])).
% 2.26/0.67  fof(f28,plain,(
% 2.26/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.26/0.67    inference(ennf_transformation,[],[f4])).
% 2.26/0.67  fof(f4,axiom,(
% 2.26/0.67    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.26/0.67  % SZS output end Proof for theBenchmark
% 2.26/0.67  % (23570)------------------------------
% 2.26/0.67  % (23570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.67  % (23570)Termination reason: Refutation
% 2.26/0.67  
% 2.26/0.67  % (23570)Memory used [KB]: 2686
% 2.26/0.67  % (23570)Time elapsed: 0.232 s
% 2.26/0.67  % (23570)------------------------------
% 2.26/0.67  % (23570)------------------------------
% 2.26/0.67  % (23532)Success in time 0.315 s
%------------------------------------------------------------------------------
