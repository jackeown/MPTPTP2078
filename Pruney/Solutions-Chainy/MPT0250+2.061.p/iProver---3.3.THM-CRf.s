%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:52 EST 2020

% Result     : Theorem 15.60s
% Output     : CNFRefutation 15.60s
% Verified   : 
% Statistics : Number of formulae       :  108 (4597 expanded)
%              Number of clauses        :   49 ( 250 expanded)
%              Number of leaves         :   19 (1542 expanded)
%              Depth                    :   23
%              Number of atoms          :  136 (4709 expanded)
%              Number of equality atoms :   89 (4528 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f33,f52,f52])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f54,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f32,f55,f52,f52])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f34,f55,f51,f52])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f35,f55,f50,f53,f56])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(definition_unfolding,[],[f36,f55,f43,f57])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f48,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f48,f55,f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f55])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f46,f54])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_5,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_0,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_745,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X7,X6,X5,X4) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_8563,plain,
    ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X0,X1,X2,X3,X7,X6,X5,X4) ),
    inference(superposition,[status(thm)],[c_745,c_0])).

cnf(c_6,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_923,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_22280,plain,
    ( k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(superposition,[status(thm)],[c_923,c_0])).

cnf(c_7,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_866,plain,
    ( k6_enumset1(X0,X1,X2,X3,X4,X4,X4,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_738,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) = k6_enumset1(X3,X2,X1,X0,X4,X5,X6,X7) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_6488,plain,
    ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X3,X2,X1,X0,X4,X5,X6,X7) ),
    inference(superposition,[status(thm)],[c_738,c_0])).

cnf(c_1556,plain,
    ( k6_enumset1(X0,X0,X1,X2,X3,X3,X3,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(superposition,[status(thm)],[c_866,c_5])).

cnf(c_2013,plain,
    ( k6_enumset1(X0,X1,X1,X1,X1,X1,X1,X1) = k6_enumset1(X1,X1,X1,X1,X1,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_1556,c_866])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_258,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_264,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_377,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_258,c_264])).

cnf(c_718,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(demodulation,[status(thm)],[c_5,c_377])).

cnf(c_3153,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(demodulation,[status(thm)],[c_2013,c_718])).

cnf(c_6799,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)),sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)) ),
    inference(demodulation,[status(thm)],[c_6488,c_3153])).

cnf(c_7824,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_866,c_6799])).

cnf(c_719,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5,c_258])).

cnf(c_3154,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2013,c_719])).

cnf(c_6800,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6488,c_3154])).

cnf(c_7587,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_6800])).

cnf(c_7598,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_7587,c_264])).

cnf(c_8254,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_7824,c_7598])).

cnf(c_22864,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(demodulation,[status(thm)],[c_22280,c_8254])).

cnf(c_25148,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_8563,c_22864])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_263,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1555,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X1,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_263])).

cnf(c_1714,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X1,X1,X1,X1,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_1555])).

cnf(c_6879,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X0,X1,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6488,c_1714])).

cnf(c_18472,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8254,c_6879])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_261,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_18630,plain,
    ( r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18472,c_261])).

cnf(c_25257,plain,
    ( r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_25148,c_18630])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8018,plain,
    ( k3_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_1,c_7598])).

cnf(c_25259,plain,
    ( k3_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(demodulation,[status(thm)],[c_25148,c_8018])).

cnf(c_594,plain,
    ( k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_263,c_264])).

cnf(c_25267,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_25259,c_594])).

cnf(c_25278,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25257,c_25267])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_14,plain,
    ( r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25278,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:20:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.60/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.60/2.51  
% 15.60/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.60/2.51  
% 15.60/2.51  ------  iProver source info
% 15.60/2.51  
% 15.60/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.60/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.60/2.51  git: non_committed_changes: false
% 15.60/2.51  git: last_make_outside_of_git: false
% 15.60/2.51  
% 15.60/2.51  ------ 
% 15.60/2.51  
% 15.60/2.51  ------ Input Options
% 15.60/2.51  
% 15.60/2.51  --out_options                           all
% 15.60/2.51  --tptp_safe_out                         true
% 15.60/2.51  --problem_path                          ""
% 15.60/2.51  --include_path                          ""
% 15.60/2.51  --clausifier                            res/vclausify_rel
% 15.60/2.51  --clausifier_options                    --mode clausify
% 15.60/2.51  --stdin                                 false
% 15.60/2.51  --stats_out                             all
% 15.60/2.51  
% 15.60/2.51  ------ General Options
% 15.60/2.51  
% 15.60/2.51  --fof                                   false
% 15.60/2.51  --time_out_real                         305.
% 15.60/2.51  --time_out_virtual                      -1.
% 15.60/2.51  --symbol_type_check                     false
% 15.60/2.51  --clausify_out                          false
% 15.60/2.51  --sig_cnt_out                           false
% 15.60/2.51  --trig_cnt_out                          false
% 15.60/2.51  --trig_cnt_out_tolerance                1.
% 15.60/2.51  --trig_cnt_out_sk_spl                   false
% 15.60/2.51  --abstr_cl_out                          false
% 15.60/2.51  
% 15.60/2.51  ------ Global Options
% 15.60/2.51  
% 15.60/2.51  --schedule                              default
% 15.60/2.51  --add_important_lit                     false
% 15.60/2.51  --prop_solver_per_cl                    1000
% 15.60/2.51  --min_unsat_core                        false
% 15.60/2.51  --soft_assumptions                      false
% 15.60/2.51  --soft_lemma_size                       3
% 15.60/2.51  --prop_impl_unit_size                   0
% 15.60/2.51  --prop_impl_unit                        []
% 15.60/2.51  --share_sel_clauses                     true
% 15.60/2.51  --reset_solvers                         false
% 15.60/2.51  --bc_imp_inh                            [conj_cone]
% 15.60/2.51  --conj_cone_tolerance                   3.
% 15.60/2.51  --extra_neg_conj                        none
% 15.60/2.51  --large_theory_mode                     true
% 15.60/2.51  --prolific_symb_bound                   200
% 15.60/2.51  --lt_threshold                          2000
% 15.60/2.51  --clause_weak_htbl                      true
% 15.60/2.51  --gc_record_bc_elim                     false
% 15.60/2.51  
% 15.60/2.51  ------ Preprocessing Options
% 15.60/2.51  
% 15.60/2.51  --preprocessing_flag                    true
% 15.60/2.51  --time_out_prep_mult                    0.1
% 15.60/2.51  --splitting_mode                        input
% 15.60/2.51  --splitting_grd                         true
% 15.60/2.51  --splitting_cvd                         false
% 15.60/2.51  --splitting_cvd_svl                     false
% 15.60/2.51  --splitting_nvd                         32
% 15.60/2.51  --sub_typing                            true
% 15.60/2.51  --prep_gs_sim                           true
% 15.60/2.51  --prep_unflatten                        true
% 15.60/2.51  --prep_res_sim                          true
% 15.60/2.51  --prep_upred                            true
% 15.60/2.51  --prep_sem_filter                       exhaustive
% 15.60/2.51  --prep_sem_filter_out                   false
% 15.60/2.51  --pred_elim                             true
% 15.60/2.51  --res_sim_input                         true
% 15.60/2.51  --eq_ax_congr_red                       true
% 15.60/2.51  --pure_diseq_elim                       true
% 15.60/2.51  --brand_transform                       false
% 15.60/2.51  --non_eq_to_eq                          false
% 15.60/2.51  --prep_def_merge                        true
% 15.60/2.51  --prep_def_merge_prop_impl              false
% 15.60/2.51  --prep_def_merge_mbd                    true
% 15.60/2.51  --prep_def_merge_tr_red                 false
% 15.60/2.51  --prep_def_merge_tr_cl                  false
% 15.60/2.51  --smt_preprocessing                     true
% 15.60/2.51  --smt_ac_axioms                         fast
% 15.60/2.51  --preprocessed_out                      false
% 15.60/2.51  --preprocessed_stats                    false
% 15.60/2.51  
% 15.60/2.51  ------ Abstraction refinement Options
% 15.60/2.51  
% 15.60/2.51  --abstr_ref                             []
% 15.60/2.51  --abstr_ref_prep                        false
% 15.60/2.51  --abstr_ref_until_sat                   false
% 15.60/2.51  --abstr_ref_sig_restrict                funpre
% 15.60/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.60/2.51  --abstr_ref_under                       []
% 15.60/2.51  
% 15.60/2.51  ------ SAT Options
% 15.60/2.51  
% 15.60/2.51  --sat_mode                              false
% 15.60/2.51  --sat_fm_restart_options                ""
% 15.60/2.51  --sat_gr_def                            false
% 15.60/2.51  --sat_epr_types                         true
% 15.60/2.51  --sat_non_cyclic_types                  false
% 15.60/2.51  --sat_finite_models                     false
% 15.60/2.51  --sat_fm_lemmas                         false
% 15.60/2.51  --sat_fm_prep                           false
% 15.60/2.51  --sat_fm_uc_incr                        true
% 15.60/2.51  --sat_out_model                         small
% 15.60/2.51  --sat_out_clauses                       false
% 15.60/2.51  
% 15.60/2.51  ------ QBF Options
% 15.60/2.51  
% 15.60/2.51  --qbf_mode                              false
% 15.60/2.51  --qbf_elim_univ                         false
% 15.60/2.51  --qbf_dom_inst                          none
% 15.60/2.51  --qbf_dom_pre_inst                      false
% 15.60/2.51  --qbf_sk_in                             false
% 15.60/2.51  --qbf_pred_elim                         true
% 15.60/2.51  --qbf_split                             512
% 15.60/2.51  
% 15.60/2.51  ------ BMC1 Options
% 15.60/2.51  
% 15.60/2.51  --bmc1_incremental                      false
% 15.60/2.51  --bmc1_axioms                           reachable_all
% 15.60/2.51  --bmc1_min_bound                        0
% 15.60/2.51  --bmc1_max_bound                        -1
% 15.60/2.51  --bmc1_max_bound_default                -1
% 15.60/2.51  --bmc1_symbol_reachability              true
% 15.60/2.51  --bmc1_property_lemmas                  false
% 15.60/2.51  --bmc1_k_induction                      false
% 15.60/2.51  --bmc1_non_equiv_states                 false
% 15.60/2.51  --bmc1_deadlock                         false
% 15.60/2.51  --bmc1_ucm                              false
% 15.60/2.51  --bmc1_add_unsat_core                   none
% 15.60/2.51  --bmc1_unsat_core_children              false
% 15.60/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.60/2.51  --bmc1_out_stat                         full
% 15.60/2.51  --bmc1_ground_init                      false
% 15.60/2.51  --bmc1_pre_inst_next_state              false
% 15.60/2.51  --bmc1_pre_inst_state                   false
% 15.60/2.51  --bmc1_pre_inst_reach_state             false
% 15.60/2.51  --bmc1_out_unsat_core                   false
% 15.60/2.51  --bmc1_aig_witness_out                  false
% 15.60/2.51  --bmc1_verbose                          false
% 15.60/2.51  --bmc1_dump_clauses_tptp                false
% 15.60/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.60/2.51  --bmc1_dump_file                        -
% 15.60/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.60/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.60/2.51  --bmc1_ucm_extend_mode                  1
% 15.60/2.51  --bmc1_ucm_init_mode                    2
% 15.60/2.51  --bmc1_ucm_cone_mode                    none
% 15.60/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.60/2.51  --bmc1_ucm_relax_model                  4
% 15.60/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.60/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.60/2.51  --bmc1_ucm_layered_model                none
% 15.60/2.51  --bmc1_ucm_max_lemma_size               10
% 15.60/2.51  
% 15.60/2.51  ------ AIG Options
% 15.60/2.51  
% 15.60/2.51  --aig_mode                              false
% 15.60/2.51  
% 15.60/2.51  ------ Instantiation Options
% 15.60/2.51  
% 15.60/2.51  --instantiation_flag                    true
% 15.60/2.51  --inst_sos_flag                         false
% 15.60/2.51  --inst_sos_phase                        true
% 15.60/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.60/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.60/2.51  --inst_lit_sel_side                     num_symb
% 15.60/2.51  --inst_solver_per_active                1400
% 15.60/2.51  --inst_solver_calls_frac                1.
% 15.60/2.51  --inst_passive_queue_type               priority_queues
% 15.60/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.60/2.51  --inst_passive_queues_freq              [25;2]
% 15.60/2.51  --inst_dismatching                      true
% 15.60/2.51  --inst_eager_unprocessed_to_passive     true
% 15.60/2.51  --inst_prop_sim_given                   true
% 15.60/2.51  --inst_prop_sim_new                     false
% 15.60/2.51  --inst_subs_new                         false
% 15.60/2.51  --inst_eq_res_simp                      false
% 15.60/2.51  --inst_subs_given                       false
% 15.60/2.51  --inst_orphan_elimination               true
% 15.60/2.51  --inst_learning_loop_flag               true
% 15.60/2.51  --inst_learning_start                   3000
% 15.60/2.51  --inst_learning_factor                  2
% 15.60/2.51  --inst_start_prop_sim_after_learn       3
% 15.60/2.51  --inst_sel_renew                        solver
% 15.60/2.51  --inst_lit_activity_flag                true
% 15.60/2.51  --inst_restr_to_given                   false
% 15.60/2.51  --inst_activity_threshold               500
% 15.60/2.51  --inst_out_proof                        true
% 15.60/2.51  
% 15.60/2.51  ------ Resolution Options
% 15.60/2.51  
% 15.60/2.51  --resolution_flag                       true
% 15.60/2.51  --res_lit_sel                           adaptive
% 15.60/2.51  --res_lit_sel_side                      none
% 15.60/2.51  --res_ordering                          kbo
% 15.60/2.51  --res_to_prop_solver                    active
% 15.60/2.51  --res_prop_simpl_new                    false
% 15.60/2.51  --res_prop_simpl_given                  true
% 15.60/2.51  --res_passive_queue_type                priority_queues
% 15.60/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.60/2.51  --res_passive_queues_freq               [15;5]
% 15.60/2.51  --res_forward_subs                      full
% 15.60/2.51  --res_backward_subs                     full
% 15.60/2.51  --res_forward_subs_resolution           true
% 15.60/2.51  --res_backward_subs_resolution          true
% 15.60/2.51  --res_orphan_elimination                true
% 15.60/2.51  --res_time_limit                        2.
% 15.60/2.51  --res_out_proof                         true
% 15.60/2.51  
% 15.60/2.51  ------ Superposition Options
% 15.60/2.51  
% 15.60/2.51  --superposition_flag                    true
% 15.60/2.51  --sup_passive_queue_type                priority_queues
% 15.60/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.60/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.60/2.51  --demod_completeness_check              fast
% 15.60/2.51  --demod_use_ground                      true
% 15.60/2.51  --sup_to_prop_solver                    passive
% 15.60/2.51  --sup_prop_simpl_new                    true
% 15.60/2.51  --sup_prop_simpl_given                  true
% 15.60/2.51  --sup_fun_splitting                     false
% 15.60/2.51  --sup_smt_interval                      50000
% 15.60/2.51  
% 15.60/2.51  ------ Superposition Simplification Setup
% 15.60/2.51  
% 15.60/2.51  --sup_indices_passive                   []
% 15.60/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.60/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.60/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.60/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.60/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.60/2.51  --sup_full_bw                           [BwDemod]
% 15.60/2.51  --sup_immed_triv                        [TrivRules]
% 15.60/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.60/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.60/2.51  --sup_immed_bw_main                     []
% 15.60/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.60/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.60/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.60/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.60/2.51  
% 15.60/2.51  ------ Combination Options
% 15.60/2.51  
% 15.60/2.51  --comb_res_mult                         3
% 15.60/2.51  --comb_sup_mult                         2
% 15.60/2.51  --comb_inst_mult                        10
% 15.60/2.51  
% 15.60/2.51  ------ Debug Options
% 15.60/2.51  
% 15.60/2.51  --dbg_backtrace                         false
% 15.60/2.51  --dbg_dump_prop_clauses                 false
% 15.60/2.51  --dbg_dump_prop_clauses_file            -
% 15.60/2.51  --dbg_out_stat                          false
% 15.60/2.51  ------ Parsing...
% 15.60/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.60/2.51  
% 15.60/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.60/2.51  
% 15.60/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.60/2.51  
% 15.60/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.60/2.51  ------ Proving...
% 15.60/2.51  ------ Problem Properties 
% 15.60/2.51  
% 15.60/2.51  
% 15.60/2.51  clauses                                 13
% 15.60/2.51  conjectures                             2
% 15.60/2.51  EPR                                     1
% 15.60/2.51  Horn                                    13
% 15.60/2.51  unary                                   8
% 15.60/2.51  binary                                  4
% 15.60/2.51  lits                                    19
% 15.60/2.51  lits eq                                 6
% 15.60/2.51  fd_pure                                 0
% 15.60/2.51  fd_pseudo                               0
% 15.60/2.51  fd_cond                                 0
% 15.60/2.51  fd_pseudo_cond                          0
% 15.60/2.51  AC symbols                              0
% 15.60/2.51  
% 15.60/2.51  ------ Schedule dynamic 5 is on 
% 15.60/2.51  
% 15.60/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.60/2.51  
% 15.60/2.51  
% 15.60/2.51  ------ 
% 15.60/2.51  Current options:
% 15.60/2.51  ------ 
% 15.60/2.51  
% 15.60/2.51  ------ Input Options
% 15.60/2.51  
% 15.60/2.51  --out_options                           all
% 15.60/2.51  --tptp_safe_out                         true
% 15.60/2.51  --problem_path                          ""
% 15.60/2.51  --include_path                          ""
% 15.60/2.51  --clausifier                            res/vclausify_rel
% 15.60/2.51  --clausifier_options                    --mode clausify
% 15.60/2.51  --stdin                                 false
% 15.60/2.51  --stats_out                             all
% 15.60/2.51  
% 15.60/2.51  ------ General Options
% 15.60/2.51  
% 15.60/2.51  --fof                                   false
% 15.60/2.51  --time_out_real                         305.
% 15.60/2.51  --time_out_virtual                      -1.
% 15.60/2.51  --symbol_type_check                     false
% 15.60/2.51  --clausify_out                          false
% 15.60/2.51  --sig_cnt_out                           false
% 15.60/2.51  --trig_cnt_out                          false
% 15.60/2.51  --trig_cnt_out_tolerance                1.
% 15.60/2.51  --trig_cnt_out_sk_spl                   false
% 15.60/2.51  --abstr_cl_out                          false
% 15.60/2.51  
% 15.60/2.51  ------ Global Options
% 15.60/2.51  
% 15.60/2.51  --schedule                              default
% 15.60/2.51  --add_important_lit                     false
% 15.60/2.51  --prop_solver_per_cl                    1000
% 15.60/2.51  --min_unsat_core                        false
% 15.60/2.51  --soft_assumptions                      false
% 15.60/2.51  --soft_lemma_size                       3
% 15.60/2.51  --prop_impl_unit_size                   0
% 15.60/2.51  --prop_impl_unit                        []
% 15.60/2.51  --share_sel_clauses                     true
% 15.60/2.51  --reset_solvers                         false
% 15.60/2.51  --bc_imp_inh                            [conj_cone]
% 15.60/2.51  --conj_cone_tolerance                   3.
% 15.60/2.51  --extra_neg_conj                        none
% 15.60/2.51  --large_theory_mode                     true
% 15.60/2.51  --prolific_symb_bound                   200
% 15.60/2.51  --lt_threshold                          2000
% 15.60/2.51  --clause_weak_htbl                      true
% 15.60/2.51  --gc_record_bc_elim                     false
% 15.60/2.51  
% 15.60/2.51  ------ Preprocessing Options
% 15.60/2.51  
% 15.60/2.51  --preprocessing_flag                    true
% 15.60/2.51  --time_out_prep_mult                    0.1
% 15.60/2.51  --splitting_mode                        input
% 15.60/2.51  --splitting_grd                         true
% 15.60/2.51  --splitting_cvd                         false
% 15.60/2.51  --splitting_cvd_svl                     false
% 15.60/2.51  --splitting_nvd                         32
% 15.60/2.51  --sub_typing                            true
% 15.60/2.51  --prep_gs_sim                           true
% 15.60/2.51  --prep_unflatten                        true
% 15.60/2.51  --prep_res_sim                          true
% 15.60/2.51  --prep_upred                            true
% 15.60/2.51  --prep_sem_filter                       exhaustive
% 15.60/2.51  --prep_sem_filter_out                   false
% 15.60/2.51  --pred_elim                             true
% 15.60/2.51  --res_sim_input                         true
% 15.60/2.51  --eq_ax_congr_red                       true
% 15.60/2.51  --pure_diseq_elim                       true
% 15.60/2.51  --brand_transform                       false
% 15.60/2.51  --non_eq_to_eq                          false
% 15.60/2.51  --prep_def_merge                        true
% 15.60/2.51  --prep_def_merge_prop_impl              false
% 15.60/2.51  --prep_def_merge_mbd                    true
% 15.60/2.51  --prep_def_merge_tr_red                 false
% 15.60/2.51  --prep_def_merge_tr_cl                  false
% 15.60/2.51  --smt_preprocessing                     true
% 15.60/2.51  --smt_ac_axioms                         fast
% 15.60/2.51  --preprocessed_out                      false
% 15.60/2.51  --preprocessed_stats                    false
% 15.60/2.51  
% 15.60/2.51  ------ Abstraction refinement Options
% 15.60/2.51  
% 15.60/2.51  --abstr_ref                             []
% 15.60/2.51  --abstr_ref_prep                        false
% 15.60/2.51  --abstr_ref_until_sat                   false
% 15.60/2.51  --abstr_ref_sig_restrict                funpre
% 15.60/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.60/2.51  --abstr_ref_under                       []
% 15.60/2.51  
% 15.60/2.51  ------ SAT Options
% 15.60/2.51  
% 15.60/2.51  --sat_mode                              false
% 15.60/2.51  --sat_fm_restart_options                ""
% 15.60/2.51  --sat_gr_def                            false
% 15.60/2.51  --sat_epr_types                         true
% 15.60/2.51  --sat_non_cyclic_types                  false
% 15.60/2.51  --sat_finite_models                     false
% 15.60/2.51  --sat_fm_lemmas                         false
% 15.60/2.51  --sat_fm_prep                           false
% 15.60/2.51  --sat_fm_uc_incr                        true
% 15.60/2.51  --sat_out_model                         small
% 15.60/2.51  --sat_out_clauses                       false
% 15.60/2.51  
% 15.60/2.51  ------ QBF Options
% 15.60/2.51  
% 15.60/2.51  --qbf_mode                              false
% 15.60/2.51  --qbf_elim_univ                         false
% 15.60/2.51  --qbf_dom_inst                          none
% 15.60/2.51  --qbf_dom_pre_inst                      false
% 15.60/2.51  --qbf_sk_in                             false
% 15.60/2.51  --qbf_pred_elim                         true
% 15.60/2.51  --qbf_split                             512
% 15.60/2.51  
% 15.60/2.51  ------ BMC1 Options
% 15.60/2.51  
% 15.60/2.51  --bmc1_incremental                      false
% 15.60/2.51  --bmc1_axioms                           reachable_all
% 15.60/2.51  --bmc1_min_bound                        0
% 15.60/2.51  --bmc1_max_bound                        -1
% 15.60/2.51  --bmc1_max_bound_default                -1
% 15.60/2.51  --bmc1_symbol_reachability              true
% 15.60/2.51  --bmc1_property_lemmas                  false
% 15.60/2.51  --bmc1_k_induction                      false
% 15.60/2.51  --bmc1_non_equiv_states                 false
% 15.60/2.51  --bmc1_deadlock                         false
% 15.60/2.51  --bmc1_ucm                              false
% 15.60/2.51  --bmc1_add_unsat_core                   none
% 15.60/2.51  --bmc1_unsat_core_children              false
% 15.60/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.60/2.51  --bmc1_out_stat                         full
% 15.60/2.51  --bmc1_ground_init                      false
% 15.60/2.51  --bmc1_pre_inst_next_state              false
% 15.60/2.51  --bmc1_pre_inst_state                   false
% 15.60/2.51  --bmc1_pre_inst_reach_state             false
% 15.60/2.51  --bmc1_out_unsat_core                   false
% 15.60/2.51  --bmc1_aig_witness_out                  false
% 15.60/2.51  --bmc1_verbose                          false
% 15.60/2.51  --bmc1_dump_clauses_tptp                false
% 15.60/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.60/2.51  --bmc1_dump_file                        -
% 15.60/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.60/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.60/2.51  --bmc1_ucm_extend_mode                  1
% 15.60/2.51  --bmc1_ucm_init_mode                    2
% 15.60/2.51  --bmc1_ucm_cone_mode                    none
% 15.60/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.60/2.51  --bmc1_ucm_relax_model                  4
% 15.60/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.60/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.60/2.51  --bmc1_ucm_layered_model                none
% 15.60/2.51  --bmc1_ucm_max_lemma_size               10
% 15.60/2.51  
% 15.60/2.51  ------ AIG Options
% 15.60/2.51  
% 15.60/2.51  --aig_mode                              false
% 15.60/2.51  
% 15.60/2.51  ------ Instantiation Options
% 15.60/2.51  
% 15.60/2.51  --instantiation_flag                    true
% 15.60/2.51  --inst_sos_flag                         false
% 15.60/2.51  --inst_sos_phase                        true
% 15.60/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.60/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.60/2.51  --inst_lit_sel_side                     none
% 15.60/2.51  --inst_solver_per_active                1400
% 15.60/2.51  --inst_solver_calls_frac                1.
% 15.60/2.51  --inst_passive_queue_type               priority_queues
% 15.60/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.60/2.51  --inst_passive_queues_freq              [25;2]
% 15.60/2.51  --inst_dismatching                      true
% 15.60/2.51  --inst_eager_unprocessed_to_passive     true
% 15.60/2.51  --inst_prop_sim_given                   true
% 15.60/2.51  --inst_prop_sim_new                     false
% 15.60/2.51  --inst_subs_new                         false
% 15.60/2.51  --inst_eq_res_simp                      false
% 15.60/2.51  --inst_subs_given                       false
% 15.60/2.51  --inst_orphan_elimination               true
% 15.60/2.51  --inst_learning_loop_flag               true
% 15.60/2.51  --inst_learning_start                   3000
% 15.60/2.51  --inst_learning_factor                  2
% 15.60/2.51  --inst_start_prop_sim_after_learn       3
% 15.60/2.51  --inst_sel_renew                        solver
% 15.60/2.51  --inst_lit_activity_flag                true
% 15.60/2.51  --inst_restr_to_given                   false
% 15.60/2.51  --inst_activity_threshold               500
% 15.60/2.51  --inst_out_proof                        true
% 15.60/2.51  
% 15.60/2.51  ------ Resolution Options
% 15.60/2.51  
% 15.60/2.51  --resolution_flag                       false
% 15.60/2.51  --res_lit_sel                           adaptive
% 15.60/2.51  --res_lit_sel_side                      none
% 15.60/2.51  --res_ordering                          kbo
% 15.60/2.51  --res_to_prop_solver                    active
% 15.60/2.51  --res_prop_simpl_new                    false
% 15.60/2.51  --res_prop_simpl_given                  true
% 15.60/2.51  --res_passive_queue_type                priority_queues
% 15.60/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.60/2.51  --res_passive_queues_freq               [15;5]
% 15.60/2.51  --res_forward_subs                      full
% 15.60/2.51  --res_backward_subs                     full
% 15.60/2.51  --res_forward_subs_resolution           true
% 15.60/2.51  --res_backward_subs_resolution          true
% 15.60/2.51  --res_orphan_elimination                true
% 15.60/2.51  --res_time_limit                        2.
% 15.60/2.51  --res_out_proof                         true
% 15.60/2.51  
% 15.60/2.51  ------ Superposition Options
% 15.60/2.51  
% 15.60/2.51  --superposition_flag                    true
% 15.60/2.51  --sup_passive_queue_type                priority_queues
% 15.60/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.60/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.60/2.51  --demod_completeness_check              fast
% 15.60/2.51  --demod_use_ground                      true
% 15.60/2.51  --sup_to_prop_solver                    passive
% 15.60/2.51  --sup_prop_simpl_new                    true
% 15.60/2.51  --sup_prop_simpl_given                  true
% 15.60/2.51  --sup_fun_splitting                     false
% 15.60/2.51  --sup_smt_interval                      50000
% 15.60/2.51  
% 15.60/2.51  ------ Superposition Simplification Setup
% 15.60/2.51  
% 15.60/2.51  --sup_indices_passive                   []
% 15.60/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.60/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.60/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.60/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.60/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.60/2.51  --sup_full_bw                           [BwDemod]
% 15.60/2.51  --sup_immed_triv                        [TrivRules]
% 15.60/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.60/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.60/2.51  --sup_immed_bw_main                     []
% 15.60/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.60/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.60/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.60/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.60/2.51  
% 15.60/2.51  ------ Combination Options
% 15.60/2.51  
% 15.60/2.51  --comb_res_mult                         3
% 15.60/2.51  --comb_sup_mult                         2
% 15.60/2.51  --comb_inst_mult                        10
% 15.60/2.51  
% 15.60/2.51  ------ Debug Options
% 15.60/2.51  
% 15.60/2.51  --dbg_backtrace                         false
% 15.60/2.51  --dbg_dump_prop_clauses                 false
% 15.60/2.51  --dbg_dump_prop_clauses_file            -
% 15.60/2.51  --dbg_out_stat                          false
% 15.60/2.51  
% 15.60/2.51  
% 15.60/2.51  
% 15.60/2.51  
% 15.60/2.51  ------ Proving...
% 15.60/2.51  
% 15.60/2.51  
% 15.60/2.51  % SZS status Theorem for theBenchmark.p
% 15.60/2.51  
% 15.60/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.60/2.51  
% 15.60/2.51  fof(f6,axiom,(
% 15.60/2.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f33,plain,(
% 15.60/2.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f6])).
% 15.60/2.51  
% 15.60/2.51  fof(f13,axiom,(
% 15.60/2.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f40,plain,(
% 15.60/2.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f13])).
% 15.60/2.51  
% 15.60/2.51  fof(f14,axiom,(
% 15.60/2.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f41,plain,(
% 15.60/2.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f14])).
% 15.60/2.51  
% 15.60/2.51  fof(f15,axiom,(
% 15.60/2.51    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f42,plain,(
% 15.60/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f15])).
% 15.60/2.51  
% 15.60/2.51  fof(f16,axiom,(
% 15.60/2.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f43,plain,(
% 15.60/2.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f16])).
% 15.60/2.51  
% 15.60/2.51  fof(f50,plain,(
% 15.60/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.60/2.51    inference(definition_unfolding,[],[f42,f43])).
% 15.60/2.51  
% 15.60/2.51  fof(f51,plain,(
% 15.60/2.51    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 15.60/2.51    inference(definition_unfolding,[],[f41,f50])).
% 15.60/2.51  
% 15.60/2.51  fof(f52,plain,(
% 15.60/2.51    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.60/2.51    inference(definition_unfolding,[],[f40,f51])).
% 15.60/2.51  
% 15.60/2.51  fof(f61,plain,(
% 15.60/2.51    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 15.60/2.51    inference(definition_unfolding,[],[f33,f52,f52])).
% 15.60/2.51  
% 15.60/2.51  fof(f5,axiom,(
% 15.60/2.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f32,plain,(
% 15.60/2.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f5])).
% 15.60/2.51  
% 15.60/2.51  fof(f17,axiom,(
% 15.60/2.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f44,plain,(
% 15.60/2.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.60/2.51    inference(cnf_transformation,[],[f17])).
% 15.60/2.51  
% 15.60/2.51  fof(f11,axiom,(
% 15.60/2.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f38,plain,(
% 15.60/2.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f11])).
% 15.60/2.51  
% 15.60/2.51  fof(f12,axiom,(
% 15.60/2.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f39,plain,(
% 15.60/2.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f12])).
% 15.60/2.51  
% 15.60/2.51  fof(f53,plain,(
% 15.60/2.51    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.60/2.51    inference(definition_unfolding,[],[f39,f52])).
% 15.60/2.51  
% 15.60/2.51  fof(f54,plain,(
% 15.60/2.51    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.60/2.51    inference(definition_unfolding,[],[f38,f53])).
% 15.60/2.51  
% 15.60/2.51  fof(f55,plain,(
% 15.60/2.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 15.60/2.51    inference(definition_unfolding,[],[f44,f54])).
% 15.60/2.51  
% 15.60/2.51  fof(f58,plain,(
% 15.60/2.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7)))) )),
% 15.60/2.51    inference(definition_unfolding,[],[f32,f55,f52,f52])).
% 15.60/2.51  
% 15.60/2.51  fof(f8,axiom,(
% 15.60/2.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f35,plain,(
% 15.60/2.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f8])).
% 15.60/2.51  
% 15.60/2.51  fof(f7,axiom,(
% 15.60/2.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f34,plain,(
% 15.60/2.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f7])).
% 15.60/2.51  
% 15.60/2.51  fof(f56,plain,(
% 15.60/2.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))) )),
% 15.60/2.51    inference(definition_unfolding,[],[f34,f55,f51,f52])).
% 15.60/2.51  
% 15.60/2.51  fof(f62,plain,(
% 15.60/2.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)))) )),
% 15.60/2.51    inference(definition_unfolding,[],[f35,f55,f50,f53,f56])).
% 15.60/2.51  
% 15.60/2.51  fof(f9,axiom,(
% 15.60/2.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f36,plain,(
% 15.60/2.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f9])).
% 15.60/2.51  
% 15.60/2.51  fof(f10,axiom,(
% 15.60/2.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f37,plain,(
% 15.60/2.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f10])).
% 15.60/2.51  
% 15.60/2.51  fof(f57,plain,(
% 15.60/2.51    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 15.60/2.51    inference(definition_unfolding,[],[f37,f54])).
% 15.60/2.51  
% 15.60/2.51  fof(f63,plain,(
% 15.60/2.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) )),
% 15.60/2.51    inference(definition_unfolding,[],[f36,f55,f43,f57])).
% 15.60/2.51  
% 15.60/2.51  fof(f19,conjecture,(
% 15.60/2.51    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f20,negated_conjecture,(
% 15.60/2.51    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 15.60/2.51    inference(negated_conjecture,[],[f19])).
% 15.60/2.51  
% 15.60/2.51  fof(f23,plain,(
% 15.60/2.51    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 15.60/2.51    inference(ennf_transformation,[],[f20])).
% 15.60/2.51  
% 15.60/2.51  fof(f26,plain,(
% 15.60/2.51    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 15.60/2.51    introduced(choice_axiom,[])).
% 15.60/2.51  
% 15.60/2.51  fof(f27,plain,(
% 15.60/2.51    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 15.60/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).
% 15.60/2.51  
% 15.60/2.51  fof(f48,plain,(
% 15.60/2.51    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 15.60/2.51    inference(cnf_transformation,[],[f27])).
% 15.60/2.51  
% 15.60/2.51  fof(f67,plain,(
% 15.60/2.51    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 15.60/2.51    inference(definition_unfolding,[],[f48,f55,f57])).
% 15.60/2.51  
% 15.60/2.51  fof(f3,axiom,(
% 15.60/2.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f22,plain,(
% 15.60/2.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.60/2.51    inference(ennf_transformation,[],[f3])).
% 15.60/2.51  
% 15.60/2.51  fof(f30,plain,(
% 15.60/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f22])).
% 15.60/2.51  
% 15.60/2.51  fof(f4,axiom,(
% 15.60/2.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f31,plain,(
% 15.60/2.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.60/2.51    inference(cnf_transformation,[],[f4])).
% 15.60/2.51  
% 15.60/2.51  fof(f60,plain,(
% 15.60/2.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 15.60/2.51    inference(definition_unfolding,[],[f31,f55])).
% 15.60/2.51  
% 15.60/2.51  fof(f18,axiom,(
% 15.60/2.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f24,plain,(
% 15.60/2.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.60/2.51    inference(nnf_transformation,[],[f18])).
% 15.60/2.51  
% 15.60/2.51  fof(f25,plain,(
% 15.60/2.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.60/2.51    inference(flattening,[],[f24])).
% 15.60/2.51  
% 15.60/2.51  fof(f46,plain,(
% 15.60/2.51    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f25])).
% 15.60/2.51  
% 15.60/2.51  fof(f65,plain,(
% 15.60/2.51    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 15.60/2.51    inference(definition_unfolding,[],[f46,f54])).
% 15.60/2.51  
% 15.60/2.51  fof(f1,axiom,(
% 15.60/2.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.60/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.60/2.51  
% 15.60/2.51  fof(f28,plain,(
% 15.60/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.60/2.51    inference(cnf_transformation,[],[f1])).
% 15.60/2.51  
% 15.60/2.51  fof(f49,plain,(
% 15.60/2.51    ~r2_hidden(sK0,sK1)),
% 15.60/2.51    inference(cnf_transformation,[],[f27])).
% 15.60/2.51  
% 15.60/2.51  cnf(c_5,plain,
% 15.60/2.51      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
% 15.60/2.51      inference(cnf_transformation,[],[f61]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_0,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 15.60/2.51      inference(cnf_transformation,[],[f58]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_745,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X7,X6,X5,X4) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_8563,plain,
% 15.60/2.51      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X0,X1,X2,X3,X7,X6,X5,X4) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_745,c_0]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_6,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
% 15.60/2.51      inference(cnf_transformation,[],[f62]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_923,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_22280,plain,
% 15.60/2.51      ( k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_923,c_0]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_7,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 15.60/2.51      inference(cnf_transformation,[],[f63]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_866,plain,
% 15.60/2.51      ( k6_enumset1(X0,X1,X2,X3,X4,X4,X4,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_738,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) = k6_enumset1(X3,X2,X1,X0,X4,X5,X6,X7) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_6488,plain,
% 15.60/2.51      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X3,X2,X1,X0,X4,X5,X6,X7) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_738,c_0]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_1556,plain,
% 15.60/2.51      ( k6_enumset1(X0,X0,X1,X2,X3,X3,X3,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_866,c_5]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_2013,plain,
% 15.60/2.51      ( k6_enumset1(X0,X1,X1,X1,X1,X1,X1,X1) = k6_enumset1(X1,X1,X1,X1,X1,X0,X0,X0) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_1556,c_866]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_12,negated_conjecture,
% 15.60/2.51      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
% 15.60/2.51      inference(cnf_transformation,[],[f67]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_258,plain,
% 15.60/2.51      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = iProver_top ),
% 15.60/2.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_3,plain,
% 15.60/2.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.60/2.51      inference(cnf_transformation,[],[f30]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_264,plain,
% 15.60/2.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.60/2.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_377,plain,
% 15.60/2.51      ( k3_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_258,c_264]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_718,plain,
% 15.60/2.51      ( k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_5,c_377]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_3153,plain,
% 15.60/2.51      ( k3_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_2013,c_718]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_6799,plain,
% 15.60/2.51      ( k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)),sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)) ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_6488,c_3153]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_7824,plain,
% 15.60/2.51      ( k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_866,c_6799]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_719,plain,
% 15.60/2.51      ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_5,c_258]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_3154,plain,
% 15.60/2.51      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = iProver_top ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_2013,c_719]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_6800,plain,
% 15.60/2.51      ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)),sK1) = iProver_top ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_6488,c_3154]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_7587,plain,
% 15.60/2.51      ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = iProver_top ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_866,c_6800]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_7598,plain,
% 15.60/2.51      ( k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_7587,c_264]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_8254,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1)) ),
% 15.60/2.51      inference(light_normalisation,[status(thm)],[c_7824,c_7598]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_22864,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_22280,c_8254]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_25148,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_8563,c_22864]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_4,plain,
% 15.60/2.51      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 15.60/2.51      inference(cnf_transformation,[],[f60]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_263,plain,
% 15.60/2.51      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 15.60/2.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_1555,plain,
% 15.60/2.51      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X1,X1,X1,X1))) = iProver_top ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_866,c_263]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_1714,plain,
% 15.60/2.51      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X1,X1,X1,X1,X1,X1,X1))) = iProver_top ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_866,c_1555]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_6879,plain,
% 15.60/2.51      ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X0,X1,X1,X1,X1))) = iProver_top ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_6488,c_1714]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_18472,plain,
% 15.60/2.51      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_8254,c_6879]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_9,plain,
% 15.60/2.51      ( r2_hidden(X0,X1)
% 15.60/2.51      | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 15.60/2.51      inference(cnf_transformation,[],[f65]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_261,plain,
% 15.60/2.51      ( r2_hidden(X0,X1) = iProver_top
% 15.60/2.51      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) != iProver_top ),
% 15.60/2.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_18630,plain,
% 15.60/2.51      ( r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_18472,c_261]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_25257,plain,
% 15.60/2.51      ( r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_25148,c_18630]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_1,plain,
% 15.60/2.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.60/2.51      inference(cnf_transformation,[],[f28]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_8018,plain,
% 15.60/2.51      ( k3_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_1,c_7598]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_25259,plain,
% 15.60/2.51      ( k3_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_25148,c_8018]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_594,plain,
% 15.60/2.51      ( k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
% 15.60/2.51      inference(superposition,[status(thm)],[c_263,c_264]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_25267,plain,
% 15.60/2.51      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 15.60/2.51      inference(demodulation,[status(thm)],[c_25259,c_594]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_25278,plain,
% 15.60/2.51      ( r2_hidden(sK0,sK1) = iProver_top ),
% 15.60/2.51      inference(light_normalisation,[status(thm)],[c_25257,c_25267]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_11,negated_conjecture,
% 15.60/2.51      ( ~ r2_hidden(sK0,sK1) ),
% 15.60/2.51      inference(cnf_transformation,[],[f49]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(c_14,plain,
% 15.60/2.51      ( r2_hidden(sK0,sK1) != iProver_top ),
% 15.60/2.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.60/2.51  
% 15.60/2.51  cnf(contradiction,plain,
% 15.60/2.51      ( $false ),
% 15.60/2.51      inference(minisat,[status(thm)],[c_25278,c_14]) ).
% 15.60/2.51  
% 15.60/2.51  
% 15.60/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.60/2.51  
% 15.60/2.51  ------                               Statistics
% 15.60/2.51  
% 15.60/2.51  ------ General
% 15.60/2.51  
% 15.60/2.51  abstr_ref_over_cycles:                  0
% 15.60/2.51  abstr_ref_under_cycles:                 0
% 15.60/2.51  gc_basic_clause_elim:                   0
% 15.60/2.51  forced_gc_time:                         0
% 15.60/2.51  parsing_time:                           0.013
% 15.60/2.51  unif_index_cands_time:                  0.
% 15.60/2.51  unif_index_add_time:                    0.
% 15.60/2.51  orderings_time:                         0.
% 15.60/2.51  out_proof_time:                         0.011
% 15.60/2.51  total_time:                             1.923
% 15.60/2.51  num_of_symbols:                         38
% 15.60/2.51  num_of_terms:                           33976
% 15.60/2.51  
% 15.60/2.51  ------ Preprocessing
% 15.60/2.51  
% 15.60/2.51  num_of_splits:                          0
% 15.60/2.51  num_of_split_atoms:                     0
% 15.60/2.51  num_of_reused_defs:                     0
% 15.60/2.51  num_eq_ax_congr_red:                    4
% 15.60/2.51  num_of_sem_filtered_clauses:            1
% 15.60/2.51  num_of_subtypes:                        0
% 15.60/2.51  monotx_restored_types:                  0
% 15.60/2.51  sat_num_of_epr_types:                   0
% 15.60/2.51  sat_num_of_non_cyclic_types:            0
% 15.60/2.51  sat_guarded_non_collapsed_types:        0
% 15.60/2.51  num_pure_diseq_elim:                    0
% 15.60/2.51  simp_replaced_by:                       0
% 15.60/2.51  res_preprocessed:                       52
% 15.60/2.51  prep_upred:                             0
% 15.60/2.51  prep_unflattend:                        0
% 15.60/2.51  smt_new_axioms:                         0
% 15.60/2.51  pred_elim_cands:                        2
% 15.60/2.51  pred_elim:                              0
% 15.60/2.51  pred_elim_cl:                           0
% 15.60/2.51  pred_elim_cycles:                       1
% 15.60/2.51  merged_defs:                            0
% 15.60/2.51  merged_defs_ncl:                        0
% 15.60/2.51  bin_hyper_res:                          0
% 15.60/2.51  prep_cycles:                            3
% 15.60/2.51  pred_elim_time:                         0.
% 15.60/2.51  splitting_time:                         0.
% 15.60/2.51  sem_filter_time:                        0.
% 15.60/2.51  monotx_time:                            0.
% 15.60/2.51  subtype_inf_time:                       0.
% 15.60/2.51  
% 15.60/2.51  ------ Problem properties
% 15.60/2.51  
% 15.60/2.51  clauses:                                13
% 15.60/2.51  conjectures:                            2
% 15.60/2.51  epr:                                    1
% 15.60/2.51  horn:                                   13
% 15.60/2.51  ground:                                 2
% 15.60/2.51  unary:                                  8
% 15.60/2.51  binary:                                 4
% 15.60/2.51  lits:                                   19
% 15.60/2.51  lits_eq:                                6
% 15.60/2.51  fd_pure:                                0
% 15.60/2.51  fd_pseudo:                              0
% 15.60/2.51  fd_cond:                                0
% 15.60/2.51  fd_pseudo_cond:                         0
% 15.60/2.51  ac_symbols:                             0
% 15.60/2.51  
% 15.60/2.51  ------ Propositional Solver
% 15.60/2.51  
% 15.60/2.51  prop_solver_calls:                      25
% 15.60/2.51  prop_fast_solver_calls:                 384
% 15.60/2.51  smt_solver_calls:                       0
% 15.60/2.51  smt_fast_solver_calls:                  0
% 15.60/2.51  prop_num_of_clauses:                    8099
% 15.60/2.51  prop_preprocess_simplified:             17163
% 15.60/2.51  prop_fo_subsumed:                       0
% 15.60/2.51  prop_solver_time:                       0.
% 15.60/2.51  smt_solver_time:                        0.
% 15.60/2.51  smt_fast_solver_time:                   0.
% 15.60/2.51  prop_fast_solver_time:                  0.
% 15.60/2.51  prop_unsat_core_time:                   0.001
% 15.60/2.51  
% 15.60/2.51  ------ QBF
% 15.60/2.51  
% 15.60/2.51  qbf_q_res:                              0
% 15.60/2.51  qbf_num_tautologies:                    0
% 15.60/2.51  qbf_prep_cycles:                        0
% 15.60/2.51  
% 15.60/2.51  ------ BMC1
% 15.60/2.51  
% 15.60/2.51  bmc1_current_bound:                     -1
% 15.60/2.51  bmc1_last_solved_bound:                 -1
% 15.60/2.51  bmc1_unsat_core_size:                   -1
% 15.60/2.51  bmc1_unsat_core_parents_size:           -1
% 15.60/2.51  bmc1_merge_next_fun:                    0
% 15.60/2.51  bmc1_unsat_core_clauses_time:           0.
% 15.60/2.51  
% 15.60/2.51  ------ Instantiation
% 15.60/2.51  
% 15.60/2.51  inst_num_of_clauses:                    2252
% 15.60/2.51  inst_num_in_passive:                    942
% 15.60/2.51  inst_num_in_active:                     669
% 15.60/2.51  inst_num_in_unprocessed:                641
% 15.60/2.51  inst_num_of_loops:                      700
% 15.60/2.51  inst_num_of_learning_restarts:          0
% 15.60/2.51  inst_num_moves_active_passive:          29
% 15.60/2.51  inst_lit_activity:                      0
% 15.60/2.51  inst_lit_activity_moves:                0
% 15.60/2.51  inst_num_tautologies:                   0
% 15.60/2.51  inst_num_prop_implied:                  0
% 15.60/2.51  inst_num_existing_simplified:           0
% 15.60/2.51  inst_num_eq_res_simplified:             0
% 15.60/2.51  inst_num_child_elim:                    0
% 15.60/2.51  inst_num_of_dismatching_blockings:      1754
% 15.60/2.51  inst_num_of_non_proper_insts:           2894
% 15.60/2.51  inst_num_of_duplicates:                 0
% 15.60/2.51  inst_inst_num_from_inst_to_res:         0
% 15.60/2.51  inst_dismatching_checking_time:         0.
% 15.60/2.51  
% 15.60/2.51  ------ Resolution
% 15.60/2.51  
% 15.60/2.51  res_num_of_clauses:                     0
% 15.60/2.51  res_num_in_passive:                     0
% 15.60/2.51  res_num_in_active:                      0
% 15.60/2.51  res_num_of_loops:                       55
% 15.60/2.51  res_forward_subset_subsumed:            151
% 15.60/2.51  res_backward_subset_subsumed:           0
% 15.60/2.51  res_forward_subsumed:                   0
% 15.60/2.51  res_backward_subsumed:                  0
% 15.60/2.51  res_forward_subsumption_resolution:     0
% 15.60/2.51  res_backward_subsumption_resolution:    0
% 15.60/2.51  res_clause_to_clause_subsumption:       32346
% 15.60/2.51  res_orphan_elimination:                 0
% 15.60/2.51  res_tautology_del:                      262
% 15.60/2.51  res_num_eq_res_simplified:              0
% 15.60/2.51  res_num_sel_changes:                    0
% 15.60/2.51  res_moves_from_active_to_pass:          0
% 15.60/2.51  
% 15.60/2.51  ------ Superposition
% 15.60/2.51  
% 15.60/2.51  sup_time_total:                         0.
% 15.60/2.51  sup_time_generating:                    0.
% 15.60/2.51  sup_time_sim_full:                      0.
% 15.60/2.51  sup_time_sim_immed:                     0.
% 15.60/2.51  
% 15.60/2.51  sup_num_of_clauses:                     1339
% 15.60/2.51  sup_num_in_active:                      114
% 15.60/2.51  sup_num_in_passive:                     1225
% 15.60/2.51  sup_num_of_loops:                       138
% 15.60/2.51  sup_fw_superposition:                   2839
% 15.60/2.51  sup_bw_superposition:                   2842
% 15.60/2.51  sup_immediate_simplified:               556
% 15.60/2.51  sup_given_eliminated:                   2
% 15.60/2.51  comparisons_done:                       0
% 15.60/2.51  comparisons_avoided:                    0
% 15.60/2.51  
% 15.60/2.51  ------ Simplifications
% 15.60/2.51  
% 15.60/2.51  
% 15.60/2.51  sim_fw_subset_subsumed:                 0
% 15.60/2.51  sim_bw_subset_subsumed:                 0
% 15.60/2.51  sim_fw_subsumed:                        201
% 15.60/2.51  sim_bw_subsumed:                        15
% 15.60/2.51  sim_fw_subsumption_res:                 0
% 15.60/2.51  sim_bw_subsumption_res:                 0
% 15.60/2.51  sim_tautology_del:                      9
% 15.60/2.51  sim_eq_tautology_del:                   4
% 15.60/2.51  sim_eq_res_simp:                        0
% 15.60/2.51  sim_fw_demodulated:                     233
% 15.60/2.51  sim_bw_demodulated:                     62
% 15.60/2.51  sim_light_normalised:                   100
% 15.60/2.51  sim_joinable_taut:                      0
% 15.60/2.51  sim_joinable_simp:                      0
% 15.60/2.51  sim_ac_normalised:                      0
% 15.60/2.51  sim_smt_subsumption:                    0
% 15.60/2.51  
%------------------------------------------------------------------------------
