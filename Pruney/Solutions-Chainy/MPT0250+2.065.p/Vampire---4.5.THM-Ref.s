%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:28 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 364 expanded)
%              Number of leaves         :   23 ( 122 expanded)
%              Depth                    :   16
%              Number of atoms          :  123 ( 406 expanded)
%              Number of equality atoms :   62 ( 333 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f864,plain,(
    $false ),
    inference(subsumption_resolution,[],[f863,f113])).

fof(f113,plain,(
    ! [X0] : ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f35,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f35,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f863,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(forward_demodulation,[],[f862,f118])).

fof(f118,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f85,f117])).

fof(f117,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f116,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f116,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f72,f73])).

fof(f73,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f38,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f85,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f51,f36])).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f862,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(forward_demodulation,[],[f860,f90])).

fof(f90,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f51,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f860,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(superposition,[],[f124,f821])).

fof(f821,plain,(
    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f74,f749,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f749,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(backward_demodulation,[],[f169,f194])).

fof(f194,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6) ),
    inference(superposition,[],[f81,f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f61,f67,f62,f66])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f60,f59,f67,f62,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f66])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f169,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(forward_demodulation,[],[f168,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f49,f65,f65])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f168,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(forward_demodulation,[],[f71,f76])).

fof(f71,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f34,f67,f69])).

fof(f34,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f124,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(forward_demodulation,[],[f75,f51])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:14:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.47  % (25015)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.48  % (25039)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (25031)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.50  % (25023)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.50  % (25011)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.50  % (25026)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.50  % (25011)Refutation not found, incomplete strategy% (25011)------------------------------
% 0.19/0.50  % (25011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (25039)Refutation not found, incomplete strategy% (25039)------------------------------
% 0.19/0.50  % (25039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (25039)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (25039)Memory used [KB]: 1663
% 0.19/0.50  % (25039)Time elapsed: 0.111 s
% 0.19/0.50  % (25039)------------------------------
% 0.19/0.50  % (25039)------------------------------
% 0.19/0.50  % (25011)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (25011)Memory used [KB]: 1663
% 0.19/0.50  % (25011)Time elapsed: 0.093 s
% 0.19/0.50  % (25011)------------------------------
% 0.19/0.50  % (25011)------------------------------
% 0.19/0.51  % (25019)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.51  % (25026)Refutation not found, incomplete strategy% (25026)------------------------------
% 0.19/0.51  % (25026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (25026)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (25026)Memory used [KB]: 10618
% 0.19/0.51  % (25026)Time elapsed: 0.107 s
% 0.19/0.51  % (25026)------------------------------
% 0.19/0.51  % (25026)------------------------------
% 0.19/0.51  % (25025)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.52  % (25024)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (25017)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.52  % (25024)Refutation not found, incomplete strategy% (25024)------------------------------
% 0.19/0.52  % (25024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (25024)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (25024)Memory used [KB]: 1663
% 0.19/0.52  % (25024)Time elapsed: 0.114 s
% 0.19/0.52  % (25024)------------------------------
% 0.19/0.52  % (25024)------------------------------
% 0.19/0.52  % (25012)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.53  % (25016)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.53  % (25033)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.53  % (25014)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.53  % (25035)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.53  % (25035)Refutation not found, incomplete strategy% (25035)------------------------------
% 0.19/0.53  % (25035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (25035)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (25035)Memory used [KB]: 6268
% 0.19/0.53  % (25035)Time elapsed: 0.130 s
% 0.19/0.53  % (25035)------------------------------
% 0.19/0.53  % (25035)------------------------------
% 0.19/0.53  % (25010)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.53  % (25034)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.53  % (25037)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.53  % (25020)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.53  % (25037)Refutation not found, incomplete strategy% (25037)------------------------------
% 0.19/0.53  % (25037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (25037)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (25037)Memory used [KB]: 6268
% 0.19/0.53  % (25037)Time elapsed: 0.127 s
% 0.19/0.53  % (25037)------------------------------
% 0.19/0.53  % (25037)------------------------------
% 0.19/0.53  % (25034)Refutation not found, incomplete strategy% (25034)------------------------------
% 0.19/0.53  % (25034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (25034)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (25034)Memory used [KB]: 10746
% 0.19/0.53  % (25034)Time elapsed: 0.109 s
% 0.19/0.53  % (25034)------------------------------
% 0.19/0.53  % (25034)------------------------------
% 0.19/0.54  % (25036)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (25038)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.54  % (25036)Refutation not found, incomplete strategy% (25036)------------------------------
% 0.19/0.54  % (25036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (25036)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (25036)Memory used [KB]: 6268
% 0.19/0.54  % (25036)Time elapsed: 0.138 s
% 0.19/0.54  % (25036)------------------------------
% 0.19/0.54  % (25036)------------------------------
% 0.19/0.54  % (25032)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.54  % (25018)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.54  % (25038)Refutation not found, incomplete strategy% (25038)------------------------------
% 0.19/0.54  % (25038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (25038)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (25038)Memory used [KB]: 10746
% 0.19/0.54  % (25038)Time elapsed: 0.138 s
% 0.19/0.54  % (25038)------------------------------
% 0.19/0.54  % (25038)------------------------------
% 0.19/0.54  % (25028)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.54  % (25028)Refutation not found, incomplete strategy% (25028)------------------------------
% 0.19/0.54  % (25028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (25028)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (25028)Memory used [KB]: 1663
% 0.19/0.54  % (25028)Time elapsed: 0.140 s
% 0.19/0.54  % (25028)------------------------------
% 0.19/0.54  % (25028)------------------------------
% 0.19/0.54  % (25022)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.54  % (25030)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.54  % (25022)Refutation not found, incomplete strategy% (25022)------------------------------
% 0.19/0.54  % (25022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (25022)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (25022)Memory used [KB]: 10618
% 0.19/0.54  % (25022)Time elapsed: 0.139 s
% 0.19/0.54  % (25022)------------------------------
% 0.19/0.54  % (25022)------------------------------
% 0.19/0.55  % (25029)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.55  % (25013)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.56  % (25020)Refutation not found, incomplete strategy% (25020)------------------------------
% 0.19/0.56  % (25020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (25020)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (25020)Memory used [KB]: 10746
% 0.19/0.56  % (25020)Time elapsed: 0.158 s
% 0.19/0.56  % (25020)------------------------------
% 0.19/0.56  % (25020)------------------------------
% 0.19/0.57  % (25027)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.58  % (25021)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.58  % (25021)Refutation not found, incomplete strategy% (25021)------------------------------
% 0.19/0.58  % (25021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.59  % (25027)Refutation not found, incomplete strategy% (25027)------------------------------
% 0.19/0.59  % (25027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.59  % (25021)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.59  
% 0.19/0.59  % (25021)Memory used [KB]: 6268
% 0.19/0.59  % (25021)Time elapsed: 0.157 s
% 0.19/0.59  % (25021)------------------------------
% 0.19/0.59  % (25021)------------------------------
% 0.19/0.59  % (25027)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.59  
% 0.19/0.59  % (25027)Memory used [KB]: 1791
% 0.19/0.59  % (25027)Time elapsed: 0.156 s
% 0.19/0.59  % (25027)------------------------------
% 0.19/0.59  % (25027)------------------------------
% 2.12/0.64  % (25013)Refutation not found, incomplete strategy% (25013)------------------------------
% 2.12/0.64  % (25013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.64  % (25013)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.64  
% 2.12/0.64  % (25013)Memory used [KB]: 6140
% 2.12/0.64  % (25013)Time elapsed: 0.219 s
% 2.12/0.64  % (25013)------------------------------
% 2.12/0.64  % (25013)------------------------------
% 2.12/0.64  % (25043)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.12/0.65  % (25014)Refutation found. Thanks to Tanya!
% 2.12/0.65  % SZS status Theorem for theBenchmark
% 2.12/0.65  % SZS output start Proof for theBenchmark
% 2.12/0.65  fof(f864,plain,(
% 2.12/0.65    $false),
% 2.12/0.65    inference(subsumption_resolution,[],[f863,f113])).
% 2.12/0.65  fof(f113,plain,(
% 2.12/0.65    ( ! [X0] : (~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1)) )),
% 2.12/0.65    inference(unit_resulting_resolution,[],[f35,f79])).
% 2.12/0.65  fof(f79,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f52,f66])).
% 2.12/0.65  fof(f66,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f44,f65])).
% 2.12/0.65  fof(f65,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f50,f64])).
% 2.12/0.65  fof(f64,plain,(
% 2.12/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f56,f63])).
% 2.12/0.65  fof(f63,plain,(
% 2.12/0.65    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f57,f62])).
% 2.12/0.65  fof(f62,plain,(
% 2.12/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f58,f59])).
% 2.12/0.65  fof(f59,plain,(
% 2.12/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f20])).
% 2.12/0.65  fof(f20,axiom,(
% 2.12/0.65    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.12/0.65  fof(f58,plain,(
% 2.12/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f19])).
% 2.12/0.65  fof(f19,axiom,(
% 2.12/0.65    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.12/0.65  fof(f57,plain,(
% 2.12/0.65    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f18])).
% 2.12/0.65  fof(f18,axiom,(
% 2.12/0.65    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.12/0.65  fof(f56,plain,(
% 2.12/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f17])).
% 2.12/0.65  fof(f17,axiom,(
% 2.12/0.65    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.12/0.65  fof(f50,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f16])).
% 2.12/0.65  fof(f16,axiom,(
% 2.12/0.65    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.12/0.65  fof(f44,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f15])).
% 2.12/0.65  fof(f15,axiom,(
% 2.12/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.12/0.65  fof(f52,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f33])).
% 2.12/0.65  fof(f33,plain,(
% 2.12/0.65    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.12/0.65    inference(flattening,[],[f32])).
% 2.12/0.65  fof(f32,plain,(
% 2.12/0.65    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.12/0.65    inference(nnf_transformation,[],[f22])).
% 2.12/0.65  fof(f22,axiom,(
% 2.12/0.65    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.12/0.65  fof(f35,plain,(
% 2.12/0.65    ~r2_hidden(sK0,sK1)),
% 2.12/0.65    inference(cnf_transformation,[],[f29])).
% 2.12/0.65  fof(f29,plain,(
% 2.12/0.65    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.12/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 2.12/0.65  fof(f28,plain,(
% 2.12/0.65    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 2.12/0.65    introduced(choice_axiom,[])).
% 2.12/0.65  fof(f27,plain,(
% 2.12/0.65    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 2.12/0.65    inference(ennf_transformation,[],[f24])).
% 2.12/0.65  fof(f24,negated_conjecture,(
% 2.12/0.65    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.12/0.65    inference(negated_conjecture,[],[f23])).
% 2.12/0.65  fof(f23,conjecture,(
% 2.12/0.65    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 2.12/0.65  fof(f863,plain,(
% 2.12/0.65    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 2.12/0.65    inference(forward_demodulation,[],[f862,f118])).
% 2.12/0.65  fof(f118,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.12/0.65    inference(backward_demodulation,[],[f85,f117])).
% 2.12/0.65  fof(f117,plain,(
% 2.12/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.12/0.65    inference(forward_demodulation,[],[f116,f36])).
% 2.12/0.65  fof(f36,plain,(
% 2.12/0.65    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.12/0.65    inference(cnf_transformation,[],[f8])).
% 2.12/0.65  fof(f8,axiom,(
% 2.12/0.65    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.12/0.65  fof(f116,plain,(
% 2.12/0.65    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 2.12/0.65    inference(forward_demodulation,[],[f72,f73])).
% 2.12/0.65  fof(f73,plain,(
% 2.12/0.65    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.12/0.65    inference(definition_unfolding,[],[f39,f67])).
% 2.12/0.65  fof(f67,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.12/0.65    inference(definition_unfolding,[],[f43,f66])).
% 2.12/0.65  fof(f43,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f21])).
% 2.12/0.65  fof(f21,axiom,(
% 2.12/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.12/0.65  fof(f39,plain,(
% 2.12/0.65    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.12/0.65    inference(cnf_transformation,[],[f26])).
% 2.12/0.65  fof(f26,plain,(
% 2.12/0.65    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.12/0.65    inference(rectify,[],[f2])).
% 2.12/0.65  fof(f2,axiom,(
% 2.12/0.65    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.12/0.65  fof(f72,plain,(
% 2.12/0.65    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.12/0.65    inference(definition_unfolding,[],[f38,f68])).
% 2.12/0.65  fof(f68,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.12/0.65    inference(definition_unfolding,[],[f45,f67])).
% 2.12/0.65  fof(f45,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f9])).
% 2.12/0.65  fof(f9,axiom,(
% 2.12/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.12/0.65  fof(f38,plain,(
% 2.12/0.65    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.12/0.65    inference(cnf_transformation,[],[f25])).
% 2.12/0.65  fof(f25,plain,(
% 2.12/0.65    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.12/0.65    inference(rectify,[],[f3])).
% 2.12/0.65  fof(f3,axiom,(
% 2.12/0.65    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.12/0.65  fof(f85,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.12/0.65    inference(superposition,[],[f51,f36])).
% 2.12/0.65  fof(f51,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f7])).
% 2.12/0.65  fof(f7,axiom,(
% 2.12/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.12/0.65  fof(f862,plain,(
% 2.12/0.65    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.12/0.65    inference(forward_demodulation,[],[f860,f90])).
% 2.12/0.65  fof(f90,plain,(
% 2.12/0.65    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 2.12/0.65    inference(superposition,[],[f51,f42])).
% 2.12/0.65  fof(f42,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f1])).
% 2.12/0.65  fof(f1,axiom,(
% 2.12/0.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.12/0.65  fof(f860,plain,(
% 2.12/0.65    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 2.12/0.65    inference(superposition,[],[f124,f821])).
% 2.12/0.65  fof(f821,plain,(
% 2.12/0.65    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.12/0.65    inference(unit_resulting_resolution,[],[f74,f749,f48])).
% 2.12/0.65  fof(f48,plain,(
% 2.12/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f31])).
% 2.12/0.65  fof(f31,plain,(
% 2.12/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.65    inference(flattening,[],[f30])).
% 2.12/0.65  fof(f30,plain,(
% 2.12/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.65    inference(nnf_transformation,[],[f4])).
% 2.12/0.65  fof(f4,axiom,(
% 2.12/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.12/0.65  fof(f749,plain,(
% 2.12/0.65    r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.12/0.65    inference(backward_demodulation,[],[f169,f194])).
% 2.12/0.65  fof(f194,plain,(
% 2.12/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6)) )),
% 2.12/0.65    inference(superposition,[],[f81,f70])).
% 2.12/0.65  fof(f70,plain,(
% 2.12/0.65    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) )),
% 2.12/0.65    inference(definition_unfolding,[],[f61,f67,f62,f66])).
% 2.12/0.65  fof(f61,plain,(
% 2.12/0.65    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f13])).
% 2.12/0.65  fof(f13,axiom,(
% 2.12/0.65    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 2.12/0.65  fof(f81,plain,(
% 2.12/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))) )),
% 2.12/0.65    inference(definition_unfolding,[],[f60,f59,f67,f62,f69])).
% 2.12/0.65  fof(f69,plain,(
% 2.12/0.65    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f37,f66])).
% 2.12/0.65  fof(f37,plain,(
% 2.12/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f14])).
% 2.12/0.65  fof(f14,axiom,(
% 2.12/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.12/0.65  fof(f60,plain,(
% 2.12/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f12])).
% 2.12/0.65  fof(f12,axiom,(
% 2.12/0.65    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 2.12/0.65  fof(f169,plain,(
% 2.12/0.65    r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.12/0.65    inference(forward_demodulation,[],[f168,f76])).
% 2.12/0.65  fof(f76,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f49,f65,f65])).
% 2.12/0.65  fof(f49,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f10])).
% 2.12/0.65  fof(f10,axiom,(
% 2.12/0.65    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 2.12/0.65  fof(f168,plain,(
% 2.12/0.65    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.12/0.65    inference(forward_demodulation,[],[f71,f76])).
% 2.12/0.65  fof(f71,plain,(
% 2.12/0.65    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 2.12/0.65    inference(definition_unfolding,[],[f34,f67,f69])).
% 2.12/0.65  fof(f34,plain,(
% 2.12/0.65    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.12/0.65    inference(cnf_transformation,[],[f29])).
% 2.12/0.65  fof(f74,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.12/0.65    inference(definition_unfolding,[],[f40,f67])).
% 2.12/0.65  fof(f40,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f6])).
% 2.12/0.65  fof(f6,axiom,(
% 2.12/0.65    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.12/0.65  fof(f124,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 2.12/0.65    inference(forward_demodulation,[],[f75,f51])).
% 2.12/0.65  fof(f75,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f41,f68])).
% 2.12/0.65  fof(f41,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f5])).
% 2.12/0.65  fof(f5,axiom,(
% 2.12/0.65    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.12/0.65  % SZS output end Proof for theBenchmark
% 2.12/0.65  % (25014)------------------------------
% 2.12/0.65  % (25014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.65  % (25014)Termination reason: Refutation
% 2.12/0.65  
% 2.12/0.65  % (25014)Memory used [KB]: 2430
% 2.12/0.65  % (25014)Time elapsed: 0.247 s
% 2.12/0.65  % (25014)------------------------------
% 2.12/0.65  % (25014)------------------------------
% 2.12/0.65  % (25009)Success in time 0.288 s
%------------------------------------------------------------------------------
