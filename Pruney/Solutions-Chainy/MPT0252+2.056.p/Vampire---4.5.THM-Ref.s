%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:58 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 366 expanded)
%              Number of leaves         :   22 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 408 expanded)
%              Number of equality atoms :   59 ( 336 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f604,plain,(
    $false ),
    inference(subsumption_resolution,[],[f603,f107])).

fof(f107,plain,(
    ! [X0] : ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f33,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f33,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f603,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f601,f163])).

fof(f163,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f112,f40])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f112,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f79,f111])).

fof(f111,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f110,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f67,f68])).

fof(f68,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f36,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f48,f34])).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f601,plain,(
    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(superposition,[],[f118,f576])).

fof(f576,plain,(
    sK2 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f69,f575,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f575,plain,(
    r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(forward_demodulation,[],[f528,f157])).

fof(f157,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5) ),
    inference(superposition,[],[f75,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f57,f62,f58,f61])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f56,f55,f62,f58,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f61])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f528,plain,(
    r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(backward_demodulation,[],[f135,f157])).

fof(f135,plain,(
    r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(forward_demodulation,[],[f66,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f52,f59,f59])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f66,plain,(
    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f32,f62,f61])).

fof(f32,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f62])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f118,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(forward_demodulation,[],[f70,f48])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:14:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.35  ipcrm: permission denied for id (795115521)
% 0.12/0.35  ipcrm: permission denied for id (795148291)
% 0.12/0.36  ipcrm: permission denied for id (795246598)
% 0.12/0.36  ipcrm: permission denied for id (795312136)
% 0.12/0.36  ipcrm: permission denied for id (795344905)
% 0.12/0.36  ipcrm: permission denied for id (795377674)
% 0.12/0.37  ipcrm: permission denied for id (795443212)
% 0.12/0.37  ipcrm: permission denied for id (795475981)
% 0.12/0.37  ipcrm: permission denied for id (795508750)
% 0.12/0.37  ipcrm: permission denied for id (795541519)
% 0.12/0.37  ipcrm: permission denied for id (795574288)
% 0.12/0.37  ipcrm: permission denied for id (795607057)
% 0.12/0.37  ipcrm: permission denied for id (795639826)
% 0.12/0.37  ipcrm: permission denied for id (795672595)
% 0.12/0.38  ipcrm: permission denied for id (795705364)
% 0.12/0.38  ipcrm: permission denied for id (795738133)
% 0.12/0.38  ipcrm: permission denied for id (795770902)
% 0.12/0.38  ipcrm: permission denied for id (795803671)
% 0.12/0.38  ipcrm: permission denied for id (795836440)
% 0.12/0.38  ipcrm: permission denied for id (795869209)
% 0.12/0.38  ipcrm: permission denied for id (795901978)
% 0.12/0.39  ipcrm: permission denied for id (796098591)
% 0.12/0.39  ipcrm: permission denied for id (796164130)
% 0.12/0.40  ipcrm: permission denied for id (796262437)
% 0.12/0.40  ipcrm: permission denied for id (796327975)
% 0.12/0.40  ipcrm: permission denied for id (796360744)
% 0.19/0.40  ipcrm: permission denied for id (796393513)
% 0.19/0.41  ipcrm: permission denied for id (796426282)
% 0.19/0.41  ipcrm: permission denied for id (796459051)
% 0.19/0.41  ipcrm: permission denied for id (796491820)
% 0.19/0.41  ipcrm: permission denied for id (796524589)
% 0.19/0.41  ipcrm: permission denied for id (796557358)
% 0.19/0.41  ipcrm: permission denied for id (796622896)
% 0.19/0.42  ipcrm: permission denied for id (796655667)
% 0.19/0.42  ipcrm: permission denied for id (796819512)
% 0.19/0.42  ipcrm: permission denied for id (796852281)
% 0.19/0.42  ipcrm: permission denied for id (796885050)
% 0.19/0.43  ipcrm: permission denied for id (796917819)
% 0.19/0.43  ipcrm: permission denied for id (796950588)
% 0.19/0.43  ipcrm: permission denied for id (797016126)
% 0.19/0.43  ipcrm: permission denied for id (797048895)
% 0.19/0.43  ipcrm: permission denied for id (797081664)
% 0.19/0.44  ipcrm: permission denied for id (797245509)
% 0.19/0.44  ipcrm: permission denied for id (797311047)
% 0.19/0.45  ipcrm: permission denied for id (797507663)
% 0.19/0.45  ipcrm: permission denied for id (797540432)
% 0.19/0.45  ipcrm: permission denied for id (797573201)
% 0.19/0.45  ipcrm: permission denied for id (797671508)
% 0.19/0.46  ipcrm: permission denied for id (797802584)
% 0.19/0.46  ipcrm: permission denied for id (797835353)
% 0.19/0.46  ipcrm: permission denied for id (797966429)
% 0.19/0.46  ipcrm: permission denied for id (797999199)
% 0.19/0.47  ipcrm: permission denied for id (798031968)
% 0.19/0.47  ipcrm: permission denied for id (798064737)
% 0.19/0.47  ipcrm: permission denied for id (798130275)
% 0.19/0.47  ipcrm: permission denied for id (798163044)
% 0.19/0.48  ipcrm: permission denied for id (798326892)
% 0.19/0.48  ipcrm: permission denied for id (798359662)
% 0.19/0.48  ipcrm: permission denied for id (798490738)
% 0.19/0.49  ipcrm: permission denied for id (798687353)
% 0.19/0.49  ipcrm: permission denied for id (798720122)
% 0.19/0.49  ipcrm: permission denied for id (798752891)
% 0.19/0.50  ipcrm: permission denied for id (798818429)
% 0.19/0.50  ipcrm: permission denied for id (798851198)
% 1.27/0.65  % (14154)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.66  % (14148)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.67  % (14171)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.67  % (14159)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.36/0.67  % (14159)Refutation not found, incomplete strategy% (14159)------------------------------
% 1.36/0.67  % (14159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.67  % (14175)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.67  % (14159)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.67  
% 1.36/0.67  % (14159)Memory used [KB]: 6268
% 1.36/0.67  % (14159)Time elapsed: 0.110 s
% 1.36/0.67  % (14159)------------------------------
% 1.36/0.67  % (14159)------------------------------
% 1.36/0.68  % (14167)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.36/0.68  % (14170)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.68  % (14175)Refutation not found, incomplete strategy% (14175)------------------------------
% 1.36/0.68  % (14175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.68  % (14175)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.68  
% 1.36/0.68  % (14175)Memory used [KB]: 6140
% 1.36/0.68  % (14175)Time elapsed: 0.112 s
% 1.36/0.68  % (14175)------------------------------
% 1.36/0.68  % (14175)------------------------------
% 1.36/0.68  % (14153)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.68  % (14149)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.36/0.68  % (14163)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.36/0.69  % (14162)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.69  % (14162)Refutation not found, incomplete strategy% (14162)------------------------------
% 1.36/0.69  % (14162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.69  % (14162)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.69  
% 1.36/0.69  % (14162)Memory used [KB]: 1663
% 1.36/0.69  % (14162)Time elapsed: 0.121 s
% 1.36/0.69  % (14162)------------------------------
% 1.36/0.69  % (14162)------------------------------
% 1.36/0.69  % (14150)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.36/0.69  % (14155)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.36/0.70  % (14151)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.36/0.70  % (14176)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.36/0.71  % (14149)Refutation not found, incomplete strategy% (14149)------------------------------
% 1.36/0.71  % (14149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.71  % (14149)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.71  
% 1.36/0.71  % (14149)Memory used [KB]: 1663
% 1.36/0.71  % (14149)Time elapsed: 0.141 s
% 1.36/0.71  % (14149)------------------------------
% 1.36/0.71  % (14149)------------------------------
% 1.72/0.71  % (14168)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.72/0.71  % (14173)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.72/0.71  % (14172)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.72/0.72  % (14174)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.72/0.72  % (14177)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.72/0.72  % (14177)Refutation not found, incomplete strategy% (14177)------------------------------
% 1.72/0.72  % (14177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.72  % (14177)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.72  
% 1.72/0.72  % (14177)Memory used [KB]: 1663
% 1.72/0.72  % (14177)Time elapsed: 0.151 s
% 1.72/0.72  % (14177)------------------------------
% 1.72/0.72  % (14177)------------------------------
% 1.72/0.72  % (14152)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.72/0.72  % (14164)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.72/0.72  % (14169)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.72/0.72  % (14160)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.72/0.72  % (14165)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.72/0.72  % (14160)Refutation not found, incomplete strategy% (14160)------------------------------
% 1.72/0.72  % (14160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.72  % (14160)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.72  
% 1.72/0.72  % (14160)Memory used [KB]: 10618
% 1.72/0.72  % (14160)Time elapsed: 0.178 s
% 1.72/0.72  % (14160)------------------------------
% 1.72/0.72  % (14160)------------------------------
% 1.72/0.73  % (14158)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.72/0.73  % (14165)Refutation not found, incomplete strategy% (14165)------------------------------
% 1.72/0.73  % (14165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.73  % (14165)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.73  
% 1.72/0.73  % (14165)Memory used [KB]: 1791
% 1.72/0.73  % (14165)Time elapsed: 0.163 s
% 1.72/0.73  % (14165)------------------------------
% 1.72/0.73  % (14165)------------------------------
% 1.72/0.73  % (14158)Refutation not found, incomplete strategy% (14158)------------------------------
% 1.72/0.73  % (14158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.73  % (14158)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.73  
% 1.72/0.73  % (14158)Memory used [KB]: 10746
% 1.72/0.73  % (14158)Time elapsed: 0.162 s
% 1.72/0.73  % (14158)------------------------------
% 1.72/0.73  % (14158)------------------------------
% 1.72/0.73  % (14156)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.72/0.73  % (14176)Refutation not found, incomplete strategy% (14176)------------------------------
% 1.72/0.73  % (14176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.73  % (14176)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.73  
% 1.72/0.73  % (14176)Memory used [KB]: 10746
% 1.72/0.73  % (14176)Time elapsed: 0.179 s
% 1.72/0.73  % (14176)------------------------------
% 1.72/0.73  % (14176)------------------------------
% 1.72/0.73  % (14164)Refutation not found, incomplete strategy% (14164)------------------------------
% 1.72/0.73  % (14164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.73  % (14166)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.72/0.73  % (14164)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.73  
% 1.72/0.73  % (14164)Memory used [KB]: 10618
% 1.72/0.73  % (14164)Time elapsed: 0.163 s
% 1.72/0.73  % (14164)------------------------------
% 1.72/0.73  % (14164)------------------------------
% 1.72/0.73  % (14161)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.72/0.73  % (14166)Refutation not found, incomplete strategy% (14166)------------------------------
% 1.72/0.73  % (14166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.73  % (14166)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.73  
% 1.72/0.73  % (14166)Memory used [KB]: 1663
% 1.72/0.73  % (14166)Time elapsed: 0.160 s
% 1.72/0.73  % (14166)------------------------------
% 1.72/0.73  % (14166)------------------------------
% 1.72/0.73  % (14172)Refutation not found, incomplete strategy% (14172)------------------------------
% 1.72/0.73  % (14172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.73  % (14157)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.72/0.73  % (14172)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.73  
% 1.72/0.73  % (14172)Memory used [KB]: 10746
% 1.72/0.73  % (14172)Time elapsed: 0.162 s
% 1.72/0.73  % (14172)------------------------------
% 1.72/0.73  % (14172)------------------------------
% 1.72/0.73  % (14173)Refutation not found, incomplete strategy% (14173)------------------------------
% 1.72/0.73  % (14173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.73  % (14173)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.73  
% 1.72/0.73  % (14173)Memory used [KB]: 6140
% 1.72/0.73  % (14173)Time elapsed: 0.170 s
% 1.72/0.73  % (14173)------------------------------
% 1.72/0.73  % (14173)------------------------------
% 1.72/0.74  % (14174)Refutation not found, incomplete strategy% (14174)------------------------------
% 1.72/0.74  % (14174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.74  % (14174)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.74  
% 1.72/0.74  % (14174)Memory used [KB]: 6140
% 1.72/0.74  % (14174)Time elapsed: 0.170 s
% 1.72/0.74  % (14174)------------------------------
% 1.72/0.74  % (14174)------------------------------
% 2.09/0.79  % (14152)Refutation found. Thanks to Tanya!
% 2.09/0.79  % SZS status Theorem for theBenchmark
% 2.09/0.79  % SZS output start Proof for theBenchmark
% 2.09/0.79  fof(f604,plain,(
% 2.09/0.79    $false),
% 2.09/0.79    inference(subsumption_resolution,[],[f603,f107])).
% 2.09/0.79  fof(f107,plain,(
% 2.09/0.79    ( ! [X0] : (~r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0),sK2)) )),
% 2.09/0.79    inference(unit_resulting_resolution,[],[f33,f73])).
% 2.09/0.79  fof(f73,plain,(
% 2.09/0.79    ( ! [X2,X0,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.09/0.79    inference(definition_unfolding,[],[f49,f61])).
% 2.09/0.79  fof(f61,plain,(
% 2.09/0.79    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.09/0.79    inference(definition_unfolding,[],[f42,f60])).
% 2.09/0.79  fof(f60,plain,(
% 2.09/0.79    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.09/0.79    inference(definition_unfolding,[],[f47,f59])).
% 2.09/0.79  fof(f59,plain,(
% 2.09/0.79    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.09/0.79    inference(definition_unfolding,[],[f53,f58])).
% 2.09/0.79  fof(f58,plain,(
% 2.09/0.79    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.09/0.79    inference(definition_unfolding,[],[f54,f55])).
% 2.09/0.79  fof(f55,plain,(
% 2.09/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.09/0.79    inference(cnf_transformation,[],[f18])).
% 2.09/0.79  fof(f18,axiom,(
% 2.09/0.79    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.09/0.79  fof(f54,plain,(
% 2.09/0.79    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.09/0.79    inference(cnf_transformation,[],[f17])).
% 2.09/0.79  fof(f17,axiom,(
% 2.09/0.79    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.09/0.79  fof(f53,plain,(
% 2.09/0.79    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.09/0.79    inference(cnf_transformation,[],[f16])).
% 2.09/0.79  fof(f16,axiom,(
% 2.09/0.79    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.09/0.79  fof(f47,plain,(
% 2.09/0.79    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.09/0.79    inference(cnf_transformation,[],[f15])).
% 2.09/0.79  fof(f15,axiom,(
% 2.09/0.79    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.09/0.79  fof(f42,plain,(
% 2.09/0.79    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.09/0.79    inference(cnf_transformation,[],[f14])).
% 2.09/0.79  fof(f14,axiom,(
% 2.09/0.79    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.09/0.79  fof(f49,plain,(
% 2.09/0.79    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.09/0.79    inference(cnf_transformation,[],[f31])).
% 2.09/0.79  fof(f31,plain,(
% 2.09/0.79    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.09/0.79    inference(flattening,[],[f30])).
% 2.09/0.79  fof(f30,plain,(
% 2.09/0.79    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.09/0.79    inference(nnf_transformation,[],[f20])).
% 2.09/0.79  fof(f20,axiom,(
% 2.09/0.79    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.09/0.79  fof(f33,plain,(
% 2.09/0.79    ~r2_hidden(sK0,sK2)),
% 2.09/0.79    inference(cnf_transformation,[],[f27])).
% 2.09/0.79  fof(f27,plain,(
% 2.09/0.79    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.09/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).
% 2.09/0.79  fof(f26,plain,(
% 2.09/0.79    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 2.09/0.79    introduced(choice_axiom,[])).
% 2.09/0.79  fof(f25,plain,(
% 2.09/0.79    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 2.09/0.79    inference(ennf_transformation,[],[f22])).
% 2.09/0.79  fof(f22,negated_conjecture,(
% 2.09/0.79    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.09/0.79    inference(negated_conjecture,[],[f21])).
% 2.09/0.79  fof(f21,conjecture,(
% 2.09/0.79    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 2.09/0.79  fof(f603,plain,(
% 2.09/0.79    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 2.09/0.79    inference(forward_demodulation,[],[f601,f163])).
% 2.09/0.79  fof(f163,plain,(
% 2.09/0.79    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.09/0.79    inference(superposition,[],[f112,f40])).
% 2.09/0.81  fof(f40,plain,(
% 2.09/0.81    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.09/0.81    inference(cnf_transformation,[],[f1])).
% 2.09/0.81  fof(f1,axiom,(
% 2.09/0.81    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.09/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.09/0.81  fof(f112,plain,(
% 2.09/0.81    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.09/0.81    inference(backward_demodulation,[],[f79,f111])).
% 2.09/0.81  fof(f111,plain,(
% 2.09/0.81    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.09/0.81    inference(forward_demodulation,[],[f110,f34])).
% 2.09/0.81  fof(f34,plain,(
% 2.09/0.81    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.09/0.81    inference(cnf_transformation,[],[f8])).
% 2.09/0.81  fof(f8,axiom,(
% 2.09/0.81    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.09/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.09/0.81  fof(f110,plain,(
% 2.09/0.81    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 2.09/0.81    inference(forward_demodulation,[],[f67,f68])).
% 2.09/0.81  fof(f68,plain,(
% 2.09/0.81    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.09/0.81    inference(definition_unfolding,[],[f37,f62])).
% 2.09/0.81  fof(f62,plain,(
% 2.09/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 2.09/0.81    inference(definition_unfolding,[],[f41,f61])).
% 2.09/0.81  fof(f41,plain,(
% 2.09/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.09/0.81    inference(cnf_transformation,[],[f19])).
% 2.09/0.81  fof(f19,axiom,(
% 2.09/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.09/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.09/0.81  fof(f37,plain,(
% 2.09/0.81    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.09/0.81    inference(cnf_transformation,[],[f24])).
% 2.09/0.81  fof(f24,plain,(
% 2.09/0.81    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.09/0.81    inference(rectify,[],[f2])).
% 2.09/0.81  fof(f2,axiom,(
% 2.09/0.81    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.09/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.09/0.81  fof(f67,plain,(
% 2.09/0.81    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.09/0.81    inference(definition_unfolding,[],[f36,f63])).
% 2.09/0.81  fof(f63,plain,(
% 2.09/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.09/0.81    inference(definition_unfolding,[],[f43,f62])).
% 2.09/0.81  fof(f43,plain,(
% 2.09/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.09/0.81    inference(cnf_transformation,[],[f9])).
% 2.09/0.81  fof(f9,axiom,(
% 2.09/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.09/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.09/0.81  fof(f36,plain,(
% 2.09/0.81    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.09/0.81    inference(cnf_transformation,[],[f23])).
% 2.09/0.81  fof(f23,plain,(
% 2.09/0.81    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.09/0.81    inference(rectify,[],[f3])).
% 2.09/0.82  fof(f3,axiom,(
% 2.09/0.82    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.09/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.09/0.82  fof(f79,plain,(
% 2.09/0.82    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.09/0.82    inference(superposition,[],[f48,f34])).
% 2.09/0.82  fof(f48,plain,(
% 2.09/0.82    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.09/0.82    inference(cnf_transformation,[],[f7])).
% 2.09/0.82  fof(f7,axiom,(
% 2.09/0.82    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.09/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.09/0.82  fof(f601,plain,(
% 2.09/0.82    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 2.09/0.82    inference(superposition,[],[f118,f576])).
% 2.09/0.82  fof(f576,plain,(
% 2.09/0.82    sK2 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.09/0.82    inference(unit_resulting_resolution,[],[f69,f575,f46])).
% 2.09/0.82  fof(f46,plain,(
% 2.09/0.82    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.09/0.82    inference(cnf_transformation,[],[f29])).
% 2.09/0.82  fof(f29,plain,(
% 2.09/0.82    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.09/0.82    inference(flattening,[],[f28])).
% 2.09/0.82  fof(f28,plain,(
% 2.09/0.82    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.09/0.82    inference(nnf_transformation,[],[f4])).
% 2.09/0.82  fof(f4,axiom,(
% 2.09/0.82    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.09/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.09/0.82  fof(f575,plain,(
% 2.09/0.82    r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 2.09/0.82    inference(forward_demodulation,[],[f528,f157])).
% 2.09/0.82  fof(f157,plain,(
% 2.09/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5)) )),
% 2.09/0.82    inference(superposition,[],[f75,f65])).
% 2.09/0.82  fof(f65,plain,(
% 2.09/0.82    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 2.09/0.82    inference(definition_unfolding,[],[f57,f62,f58,f61])).
% 2.09/0.82  fof(f57,plain,(
% 2.09/0.82    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 2.09/0.82    inference(cnf_transformation,[],[f12])).
% 2.09/0.82  fof(f12,axiom,(
% 2.09/0.82    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 2.09/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 2.09/0.82  fof(f75,plain,(
% 2.09/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X5)))) )),
% 2.09/0.82    inference(definition_unfolding,[],[f56,f55,f62,f58,f64])).
% 2.09/0.82  fof(f64,plain,(
% 2.09/0.82    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 2.09/0.82    inference(definition_unfolding,[],[f35,f61])).
% 2.09/0.82  fof(f35,plain,(
% 2.09/0.82    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.09/0.82    inference(cnf_transformation,[],[f13])).
% 2.09/0.82  fof(f13,axiom,(
% 2.09/0.82    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.09/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.09/0.82  fof(f56,plain,(
% 2.09/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 2.09/0.82    inference(cnf_transformation,[],[f11])).
% 2.09/0.82  fof(f11,axiom,(
% 2.09/0.82    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 2.09/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 2.09/0.82  fof(f528,plain,(
% 2.09/0.82    r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 2.09/0.82    inference(backward_demodulation,[],[f135,f157])).
% 2.09/0.82  fof(f135,plain,(
% 2.09/0.82    r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 2.09/0.82    inference(forward_demodulation,[],[f66,f74])).
% 2.09/0.82  fof(f74,plain,(
% 2.09/0.82    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 2.09/0.82    inference(definition_unfolding,[],[f52,f59,f59])).
% 2.09/0.82  fof(f52,plain,(
% 2.09/0.82    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 2.09/0.82    inference(cnf_transformation,[],[f10])).
% 2.09/0.82  fof(f10,axiom,(
% 2.09/0.82    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 2.09/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 2.09/0.82  fof(f66,plain,(
% 2.09/0.82    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 2.09/0.82    inference(definition_unfolding,[],[f32,f62,f61])).
% 2.09/0.82  fof(f32,plain,(
% 2.09/0.82    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.09/0.82    inference(cnf_transformation,[],[f27])).
% 2.09/0.82  fof(f69,plain,(
% 2.09/0.82    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.09/0.82    inference(definition_unfolding,[],[f38,f62])).
% 2.09/0.82  fof(f38,plain,(
% 2.09/0.82    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.09/0.82    inference(cnf_transformation,[],[f6])).
% 2.09/0.82  fof(f6,axiom,(
% 2.09/0.82    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.09/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.09/0.82  fof(f118,plain,(
% 2.09/0.82    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 2.09/0.82    inference(forward_demodulation,[],[f70,f48])).
% 2.09/0.82  fof(f70,plain,(
% 2.09/0.82    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 2.09/0.82    inference(definition_unfolding,[],[f39,f63])).
% 2.09/0.82  fof(f39,plain,(
% 2.09/0.82    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.09/0.82    inference(cnf_transformation,[],[f5])).
% 2.09/0.82  fof(f5,axiom,(
% 2.09/0.82    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.09/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.09/0.82  % SZS output end Proof for theBenchmark
% 2.09/0.82  % (14152)------------------------------
% 2.09/0.82  % (14152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.82  % (14152)Termination reason: Refutation
% 2.09/0.82  
% 2.09/0.82  % (14152)Memory used [KB]: 2174
% 2.09/0.82  % (14152)Time elapsed: 0.233 s
% 2.09/0.82  % (14152)------------------------------
% 2.09/0.82  % (14152)------------------------------
% 2.09/0.82  % (13989)Success in time 0.47 s
%------------------------------------------------------------------------------
