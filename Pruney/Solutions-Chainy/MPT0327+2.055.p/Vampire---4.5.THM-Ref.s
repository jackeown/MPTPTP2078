%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:56 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   97 (8999 expanded)
%              Number of leaves         :   17 (2449 expanded)
%              Depth                    :   30
%              Number of atoms          :  154 (16446 expanded)
%              Number of equality atoms :   96 (9729 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1854,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1843])).

fof(f1843,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f1452,f1733])).

fof(f1733,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f1597,f1262])).

fof(f1262,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f1252,f85])).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f61,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f70,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f1252,plain,(
    k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f525,f1204])).

fof(f1204,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f200,f1156])).

fof(f1156,plain,(
    k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[],[f525,f1042])).

fof(f1042,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(superposition,[],[f525,f805])).

fof(f805,plain,(
    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f122,f32])).

fof(f32,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f122,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k5_xboole_0(X4,k3_xboole_0(X4,k2_enumset1(X3,X3,X3,X3)))) = X4 ) ),
    inference(resolution,[],[f62,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f200,plain,(
    ! [X2,X3] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f189,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f189,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f83,f183])).

fof(f183,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(superposition,[],[f174,f85])).

fof(f174,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f173,f83])).

fof(f173,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f165,f106])).

fof(f106,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f92,f73])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f92,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(k1_xboole_0,X5)) = k5_xboole_0(X4,X5) ),
    inference(superposition,[],[f50,f85])).

fof(f165,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))))) = X0 ),
    inference(superposition,[],[f164,f83])).

fof(f164,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))))) = X0 ),
    inference(forward_demodulation,[],[f74,f50])).

fof(f74,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f55,f57,f51])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f525,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f201,f443])).

fof(f443,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f408,f85])).

fof(f408,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f201,f189])).

fof(f201,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f50,f189])).

fof(f1597,plain,(
    ! [X0] : sK1 = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(forward_demodulation,[],[f1564,f1461])).

fof(f1461,plain,(
    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f525,f1427])).

fof(f1427,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f1042,f1262])).

fof(f1564,plain,(
    ! [X0] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(superposition,[],[f1480,f186])).

fof(f186,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))))) ),
    inference(resolution,[],[f66,f75])).

fof(f75,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f38,f51,f59])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) ),
    inference(definition_unfolding,[],[f41,f59,f51,f59])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f1480,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0))) ),
    inference(forward_demodulation,[],[f1472,f50])).

fof(f1472,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) ),
    inference(superposition,[],[f50,f1461])).

fof(f1452,plain,(
    sK1 != k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f1437,f1427])).

fof(f1437,plain,(
    sK1 != k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(forward_demodulation,[],[f1426,f525])).

fof(f1426,plain,(
    sK1 != k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))) ),
    inference(backward_demodulation,[],[f1141,f1262])).

fof(f1141,plain,(
    sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))) ),
    inference(backward_demodulation,[],[f97,f1042])).

fof(f97,plain,(
    sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))))) ),
    inference(superposition,[],[f60,f50])).

fof(f60,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))) ),
    inference(definition_unfolding,[],[f33,f57,f51,f59,f59])).

fof(f33,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:40:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (13331)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (13326)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (13335)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (13358)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (13358)Refutation not found, incomplete strategy% (13358)------------------------------
% 0.21/0.53  % (13358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13358)Memory used [KB]: 10746
% 0.21/0.53  % (13358)Time elapsed: 0.126 s
% 0.21/0.53  % (13358)------------------------------
% 0.21/0.53  % (13358)------------------------------
% 0.21/0.53  % (13352)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (13341)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (13344)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (13344)Refutation not found, incomplete strategy% (13344)------------------------------
% 0.21/0.53  % (13344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13344)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13344)Memory used [KB]: 10618
% 0.21/0.53  % (13344)Time elapsed: 0.120 s
% 0.21/0.53  % (13344)------------------------------
% 0.21/0.53  % (13344)------------------------------
% 0.21/0.53  % (13338)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (13332)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (13333)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (13329)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (13360)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (13342)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (13353)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (13328)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (13327)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (13327)Refutation not found, incomplete strategy% (13327)------------------------------
% 0.21/0.54  % (13327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13327)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13327)Memory used [KB]: 1663
% 0.21/0.54  % (13327)Time elapsed: 0.124 s
% 0.21/0.54  % (13327)------------------------------
% 0.21/0.54  % (13327)------------------------------
% 0.21/0.54  % (13357)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (13357)Refutation not found, incomplete strategy% (13357)------------------------------
% 0.21/0.54  % (13357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13357)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13357)Memory used [KB]: 6140
% 0.21/0.54  % (13357)Time elapsed: 0.126 s
% 0.21/0.54  % (13357)------------------------------
% 0.21/0.54  % (13357)------------------------------
% 0.21/0.54  % (13350)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (13343)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (13345)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (13355)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (13334)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (13355)Refutation not found, incomplete strategy% (13355)------------------------------
% 0.21/0.55  % (13355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13355)Memory used [KB]: 6268
% 0.21/0.55  % (13355)Time elapsed: 0.139 s
% 0.21/0.55  % (13355)------------------------------
% 0.21/0.55  % (13355)------------------------------
% 0.21/0.55  % (13348)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (13347)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (13346)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (13346)Refutation not found, incomplete strategy% (13346)------------------------------
% 0.21/0.55  % (13346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13346)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13346)Memory used [KB]: 1663
% 0.21/0.55  % (13346)Time elapsed: 0.138 s
% 0.21/0.55  % (13346)------------------------------
% 0.21/0.55  % (13346)------------------------------
% 1.50/0.55  % (13336)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.55  % (13349)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.55  % (13337)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.55  % (13337)Refutation not found, incomplete strategy% (13337)------------------------------
% 1.50/0.55  % (13337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13339)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.55  % (13360)Refutation not found, incomplete strategy% (13360)------------------------------
% 1.50/0.55  % (13360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13360)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (13360)Memory used [KB]: 1663
% 1.50/0.55  % (13360)Time elapsed: 0.148 s
% 1.50/0.55  % (13360)------------------------------
% 1.50/0.55  % (13360)------------------------------
% 1.50/0.56  % (13337)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (13337)Memory used [KB]: 10746
% 1.50/0.56  % (13337)Time elapsed: 0.151 s
% 1.50/0.56  % (13337)------------------------------
% 1.50/0.56  % (13337)------------------------------
% 1.50/0.56  % (13356)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.50/0.56  % (13353)Refutation not found, incomplete strategy% (13353)------------------------------
% 1.50/0.56  % (13353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (13353)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (13353)Memory used [KB]: 10618
% 1.50/0.56  % (13353)Time elapsed: 0.148 s
% 1.50/0.56  % (13353)------------------------------
% 1.50/0.56  % (13353)------------------------------
% 2.01/0.64  % (13402)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.01/0.65  % (13332)Refutation found. Thanks to Tanya!
% 2.01/0.65  % SZS status Theorem for theBenchmark
% 2.01/0.65  % (13404)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.12/0.67  % (13409)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.12/0.67  % (13403)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.12/0.67  % SZS output start Proof for theBenchmark
% 2.12/0.67  fof(f1854,plain,(
% 2.12/0.67    $false),
% 2.12/0.67    inference(trivial_inequality_removal,[],[f1843])).
% 2.12/0.67  fof(f1843,plain,(
% 2.12/0.67    sK1 != sK1),
% 2.12/0.67    inference(superposition,[],[f1452,f1733])).
% 2.12/0.67  fof(f1733,plain,(
% 2.12/0.67    sK1 = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 2.12/0.67    inference(superposition,[],[f1597,f1262])).
% 2.12/0.67  fof(f1262,plain,(
% 2.12/0.67    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.12/0.67    inference(forward_demodulation,[],[f1252,f85])).
% 2.12/0.67  fof(f85,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/0.67    inference(backward_demodulation,[],[f61,f83])).
% 2.12/0.67  fof(f83,plain,(
% 2.12/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.12/0.67    inference(resolution,[],[f70,f76])).
% 2.12/0.67  fof(f76,plain,(
% 2.12/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.12/0.67    inference(equality_resolution,[],[f48])).
% 2.12/0.67  fof(f48,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.12/0.67    inference(cnf_transformation,[],[f31])).
% 2.12/0.67  fof(f31,plain,(
% 2.12/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.67    inference(flattening,[],[f30])).
% 2.12/0.67  fof(f30,plain,(
% 2.12/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.67    inference(nnf_transformation,[],[f2])).
% 2.12/0.67  fof(f2,axiom,(
% 2.12/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.12/0.67  fof(f70,plain,(
% 2.12/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.67    inference(definition_unfolding,[],[f46,f51])).
% 2.12/0.67  fof(f51,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f4])).
% 2.12/0.67  fof(f4,axiom,(
% 2.12/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.12/0.67  fof(f46,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f29])).
% 2.12/0.67  fof(f29,plain,(
% 2.12/0.67    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.12/0.67    inference(nnf_transformation,[],[f3])).
% 2.12/0.67  fof(f3,axiom,(
% 2.12/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.12/0.67  fof(f61,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.12/0.67    inference(definition_unfolding,[],[f34,f57])).
% 2.12/0.67  fof(f57,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.12/0.67    inference(definition_unfolding,[],[f36,f51])).
% 2.12/0.67  fof(f36,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f9])).
% 2.12/0.67  fof(f9,axiom,(
% 2.12/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.12/0.67  fof(f34,plain,(
% 2.12/0.67    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.12/0.67    inference(cnf_transformation,[],[f20])).
% 2.12/0.67  fof(f20,plain,(
% 2.12/0.67    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.12/0.67    inference(rectify,[],[f1])).
% 2.12/0.67  fof(f1,axiom,(
% 2.12/0.67    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.12/0.67  fof(f1252,plain,(
% 2.12/0.67    k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 2.12/0.67    inference(superposition,[],[f525,f1204])).
% 2.12/0.67  fof(f1204,plain,(
% 2.12/0.67    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.12/0.67    inference(superposition,[],[f200,f1156])).
% 2.12/0.67  fof(f1156,plain,(
% 2.12/0.67    k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 2.12/0.67    inference(superposition,[],[f525,f1042])).
% 2.12/0.67  fof(f1042,plain,(
% 2.12/0.67    k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.12/0.67    inference(superposition,[],[f525,f805])).
% 2.12/0.67  fof(f805,plain,(
% 2.12/0.67    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 2.12/0.67    inference(resolution,[],[f122,f32])).
% 2.12/0.67  fof(f32,plain,(
% 2.12/0.67    r2_hidden(sK0,sK1)),
% 2.12/0.67    inference(cnf_transformation,[],[f24])).
% 2.12/0.67  fof(f24,plain,(
% 2.12/0.67    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 2.12/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 2.12/0.67  fof(f23,plain,(
% 2.12/0.67    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 2.12/0.67    introduced(choice_axiom,[])).
% 2.12/0.67  fof(f21,plain,(
% 2.12/0.67    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 2.12/0.67    inference(ennf_transformation,[],[f19])).
% 2.12/0.67  fof(f19,negated_conjecture,(
% 2.12/0.67    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.12/0.67    inference(negated_conjecture,[],[f18])).
% 2.12/0.67  fof(f18,conjecture,(
% 2.12/0.67    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 2.12/0.67  fof(f122,plain,(
% 2.12/0.67    ( ! [X4,X3] : (~r2_hidden(X3,X4) | k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k5_xboole_0(X4,k3_xboole_0(X4,k2_enumset1(X3,X3,X3,X3)))) = X4) )),
% 2.12/0.67    inference(resolution,[],[f62,f68])).
% 2.12/0.67  fof(f68,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.12/0.67    inference(definition_unfolding,[],[f43,f59])).
% 2.12/0.67  fof(f59,plain,(
% 2.12/0.67    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.12/0.67    inference(definition_unfolding,[],[f44,f58])).
% 2.12/0.67  fof(f58,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.12/0.67    inference(definition_unfolding,[],[f52,f56])).
% 2.12/0.67  fof(f56,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f12])).
% 2.12/0.67  fof(f12,axiom,(
% 2.12/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.12/0.67  fof(f52,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f11])).
% 2.12/0.67  fof(f11,axiom,(
% 2.12/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.12/0.67  fof(f44,plain,(
% 2.12/0.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f10])).
% 2.12/0.67  fof(f10,axiom,(
% 2.12/0.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.12/0.67  fof(f43,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f28])).
% 2.12/0.67  fof(f28,plain,(
% 2.12/0.67    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.12/0.67    inference(nnf_transformation,[],[f14])).
% 2.12/0.67  fof(f14,axiom,(
% 2.12/0.67    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.12/0.67  fof(f62,plain,(
% 2.12/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 2.12/0.67    inference(definition_unfolding,[],[f35,f57])).
% 2.12/0.67  fof(f35,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f22])).
% 2.12/0.67  fof(f22,plain,(
% 2.12/0.67    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.12/0.67    inference(ennf_transformation,[],[f5])).
% 2.12/0.67  fof(f5,axiom,(
% 2.12/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.12/0.67  fof(f200,plain,(
% 2.12/0.67    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 2.12/0.67    inference(superposition,[],[f189,f50])).
% 2.12/0.67  fof(f50,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f8])).
% 2.12/0.67  fof(f8,axiom,(
% 2.12/0.67    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.12/0.67  fof(f189,plain,(
% 2.12/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.12/0.67    inference(backward_demodulation,[],[f83,f183])).
% 2.12/0.67  fof(f183,plain,(
% 2.12/0.67    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 2.12/0.67    inference(superposition,[],[f174,f85])).
% 2.12/0.67  fof(f174,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = X0) )),
% 2.12/0.67    inference(forward_demodulation,[],[f173,f83])).
% 2.12/0.67  fof(f173,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.12/0.67    inference(forward_demodulation,[],[f165,f106])).
% 2.12/0.67  fof(f106,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.12/0.67    inference(superposition,[],[f92,f73])).
% 2.12/0.67  fof(f73,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 2.12/0.67    inference(definition_unfolding,[],[f54,f57])).
% 2.12/0.67  fof(f54,plain,(
% 2.12/0.67    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/0.67    inference(cnf_transformation,[],[f6])).
% 2.12/0.67  fof(f6,axiom,(
% 2.12/0.67    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.12/0.67  fof(f92,plain,(
% 2.12/0.67    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(k1_xboole_0,X5)) = k5_xboole_0(X4,X5)) )),
% 2.12/0.67    inference(superposition,[],[f50,f85])).
% 2.12/0.67  fof(f165,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))))) = X0) )),
% 2.12/0.67    inference(superposition,[],[f164,f83])).
% 2.12/0.67  fof(f164,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))))) = X0) )),
% 2.12/0.67    inference(forward_demodulation,[],[f74,f50])).
% 2.12/0.67  fof(f74,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0) )),
% 2.12/0.67    inference(definition_unfolding,[],[f55,f57,f51])).
% 2.12/0.67  fof(f55,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.12/0.67    inference(cnf_transformation,[],[f7])).
% 2.12/0.67  fof(f7,axiom,(
% 2.12/0.67    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.12/0.67  fof(f525,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.12/0.67    inference(backward_demodulation,[],[f201,f443])).
% 2.12/0.67  fof(f443,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.12/0.67    inference(forward_demodulation,[],[f408,f85])).
% 2.12/0.67  fof(f408,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.12/0.67    inference(superposition,[],[f201,f189])).
% 2.12/0.67  fof(f201,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.12/0.67    inference(superposition,[],[f50,f189])).
% 2.12/0.67  fof(f1597,plain,(
% 2.12/0.67    ( ! [X0] : (sK1 = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0)))))) )),
% 2.12/0.67    inference(forward_demodulation,[],[f1564,f1461])).
% 2.12/0.67  fof(f1461,plain,(
% 2.12/0.67    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.12/0.67    inference(superposition,[],[f525,f1427])).
% 2.12/0.67  fof(f1427,plain,(
% 2.12/0.67    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.12/0.67    inference(backward_demodulation,[],[f1042,f1262])).
% 2.12/0.67  fof(f1564,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0)))))) )),
% 2.12/0.67    inference(superposition,[],[f1480,f186])).
% 2.12/0.67  fof(f186,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))))) )),
% 2.12/0.67    inference(resolution,[],[f66,f75])).
% 2.12/0.67  fof(f75,plain,(
% 2.12/0.67    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 2.12/0.67    inference(equality_resolution,[],[f64])).
% 2.12/0.67  fof(f64,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 2.12/0.67    inference(definition_unfolding,[],[f38,f51,f59])).
% 2.12/0.67  fof(f38,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f26])).
% 2.12/0.67  fof(f26,plain,(
% 2.12/0.67    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 2.12/0.67    inference(flattening,[],[f25])).
% 2.12/0.67  fof(f25,plain,(
% 2.12/0.67    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 2.12/0.67    inference(nnf_transformation,[],[f17])).
% 2.12/0.67  fof(f17,axiom,(
% 2.12/0.67    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 2.12/0.67  fof(f66,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) )),
% 2.12/0.67    inference(definition_unfolding,[],[f41,f59,f51,f59])).
% 2.12/0.67  fof(f41,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f27])).
% 2.12/0.67  fof(f27,plain,(
% 2.12/0.67    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 2.12/0.67    inference(nnf_transformation,[],[f15])).
% 2.12/0.67  fof(f15,axiom,(
% 2.12/0.67    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 2.12/0.67  fof(f1480,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)))) )),
% 2.12/0.67    inference(forward_demodulation,[],[f1472,f50])).
% 2.12/0.67  fof(f1472,plain,(
% 2.12/0.67    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0))) )),
% 2.12/0.67    inference(superposition,[],[f50,f1461])).
% 2.12/0.67  fof(f1452,plain,(
% 2.12/0.67    sK1 != k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 2.12/0.67    inference(backward_demodulation,[],[f1437,f1427])).
% 2.12/0.67  fof(f1437,plain,(
% 2.12/0.67    sK1 != k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.12/0.67    inference(forward_demodulation,[],[f1426,f525])).
% 2.12/0.67  fof(f1426,plain,(
% 2.12/0.67    sK1 != k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))))),
% 2.12/0.67    inference(backward_demodulation,[],[f1141,f1262])).
% 2.12/0.67  fof(f1141,plain,(
% 2.12/0.67    sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))))),
% 2.12/0.67    inference(backward_demodulation,[],[f97,f1042])).
% 2.12/0.67  fof(f97,plain,(
% 2.12/0.67    sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))))),
% 2.12/0.67    inference(superposition,[],[f60,f50])).
% 2.12/0.67  fof(f60,plain,(
% 2.12/0.67    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))))),
% 2.12/0.67    inference(definition_unfolding,[],[f33,f57,f51,f59,f59])).
% 2.12/0.67  fof(f33,plain,(
% 2.12/0.67    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.12/0.67    inference(cnf_transformation,[],[f24])).
% 2.12/0.67  % SZS output end Proof for theBenchmark
% 2.12/0.67  % (13332)------------------------------
% 2.12/0.67  % (13332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.67  % (13332)Termination reason: Refutation
% 2.12/0.67  
% 2.12/0.67  % (13332)Memory used [KB]: 2942
% 2.12/0.67  % (13332)Time elapsed: 0.218 s
% 2.12/0.67  % (13332)------------------------------
% 2.12/0.67  % (13332)------------------------------
% 2.12/0.67  % (13322)Success in time 0.302 s
%------------------------------------------------------------------------------
