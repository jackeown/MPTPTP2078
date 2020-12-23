%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:27 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 681 expanded)
%              Number of clauses        :   33 (  51 expanded)
%              Number of leaves         :   16 ( 225 expanded)
%              Depth                    :   19
%              Number of atoms          :  127 ( 730 expanded)
%              Number of equality atoms :   70 ( 657 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f47,f65,f65])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f67,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f46,f68,f65,f65])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f50,f68,f56,f72])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f68])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).

fof(f62,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f62,f68,f67])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f63,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_13,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X4,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4181,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X4,X5,X6))) = k5_enumset1(X0,X1,X2,X6,X5,X4,X3) ),
    inference(superposition,[status(thm)],[c_11,c_13])).

cnf(c_9406,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X6,X5,X4,X3) ),
    inference(superposition,[status(thm)],[c_4181,c_13])).

cnf(c_9702,plain,
    ( k5_enumset1(X0,X0,X0,X1,X2,X3,X0) = k5_enumset1(X1,X1,X1,X1,X2,X3,X0) ),
    inference(superposition,[status(thm)],[c_9406,c_11])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4142,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X4,X4))) = k5_enumset1(X3,X3,X3,X2,X1,X0,X4) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_5996,plain,
    ( k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X3,X3,X3,X2,X1,X0,X4) ),
    inference(superposition,[status(thm)],[c_4142,c_0])).

cnf(c_4183,plain,
    ( k5_enumset1(X0,X1,X2,X3,X3,X3,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_4368,plain,
    ( k5_enumset1(X0,X1,X2,X3,X3,X3,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(superposition,[status(thm)],[c_4183,c_11])).

cnf(c_5948,plain,
    ( k5_enumset1(X0,X0,X0,X1,X2,X2,X3) = k5_enumset1(X2,X1,X0,X3,X3,X3,X3) ),
    inference(superposition,[status(thm)],[c_13,c_4142])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4052,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4367,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X1,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4183,c_4052])).

cnf(c_6129,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X0,X1,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5948,c_4367])).

cnf(c_7808,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4368,c_6129])).

cnf(c_8007,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X0,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5996,c_7808])).

cnf(c_10046,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9702,c_8007])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4047,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4127,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11,c_4047])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4054,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4307,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4127,c_4054])).

cnf(c_11858,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_10046,c_4307])).

cnf(c_4129,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_4052])).

cnf(c_11892,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_11858,c_4129])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4049,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11906,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_11892,c_4049])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11906,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.61/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.99  
% 3.61/0.99  ------  iProver source info
% 3.61/0.99  
% 3.61/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.99  git: non_committed_changes: false
% 3.61/0.99  git: last_make_outside_of_git: false
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  ------ Parsing...
% 3.61/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.99  ------ Proving...
% 3.61/0.99  ------ Problem Properties 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  clauses                                 18
% 3.61/0.99  conjectures                             2
% 3.61/0.99  EPR                                     3
% 3.61/0.99  Horn                                    18
% 3.61/0.99  unary                                   14
% 3.61/0.99  binary                                  2
% 3.61/0.99  lits                                    24
% 3.61/0.99  lits eq                                 10
% 3.61/1.00  fd_pure                                 0
% 3.61/1.00  fd_pseudo                               0
% 3.61/1.00  fd_cond                                 0
% 3.61/1.00  fd_pseudo_cond                          1
% 3.61/1.00  AC symbols                              1
% 3.61/1.00  
% 3.61/1.00  ------ Input Options Time Limit: Unbounded
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing...
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.61/1.00  Current options:
% 3.61/1.00  ------ 
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  % SZS status Theorem for theBenchmark.p
% 3.61/1.00  
% 3.61/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/1.00  
% 3.61/1.00  fof(f11,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f47,plain,(
% 3.61/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f11])).
% 3.61/1.00  
% 3.61/1.00  fof(f18,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f54,plain,(
% 3.61/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f18])).
% 3.61/1.00  
% 3.61/1.00  fof(f19,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f55,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f19])).
% 3.61/1.00  
% 3.61/1.00  fof(f20,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f56,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f20])).
% 3.61/1.00  
% 3.61/1.00  fof(f64,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f55,f56])).
% 3.61/1.00  
% 3.61/1.00  fof(f65,plain,(
% 3.61/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f54,f64])).
% 3.61/1.00  
% 3.61/1.00  fof(f78,plain,(
% 3.61/1.00    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f47,f65,f65])).
% 3.61/1.00  
% 3.61/1.00  fof(f21,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f57,plain,(
% 3.61/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f21])).
% 3.61/1.00  
% 3.61/1.00  fof(f10,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f46,plain,(
% 3.61/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f10])).
% 3.61/1.00  
% 3.61/1.00  fof(f22,axiom,(
% 3.61/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f58,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.61/1.00    inference(cnf_transformation,[],[f22])).
% 3.61/1.00  
% 3.61/1.00  fof(f16,axiom,(
% 3.61/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f52,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f16])).
% 3.61/1.00  
% 3.61/1.00  fof(f17,axiom,(
% 3.61/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f53,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f17])).
% 3.61/1.00  
% 3.61/1.00  fof(f66,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f53,f65])).
% 3.61/1.00  
% 3.61/1.00  fof(f67,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f52,f66])).
% 3.61/1.00  
% 3.61/1.00  fof(f68,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.61/1.00    inference(definition_unfolding,[],[f58,f67])).
% 3.61/1.00  
% 3.61/1.00  fof(f70,plain,(
% 3.61/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X5,X6,X7)))) )),
% 3.61/1.00    inference(definition_unfolding,[],[f46,f68,f65,f65])).
% 3.61/1.00  
% 3.61/1.00  fof(f80,plain,(
% 3.61/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X4,X5,X6)))) )),
% 3.61/1.00    inference(definition_unfolding,[],[f57,f70])).
% 3.61/1.00  
% 3.61/1.00  fof(f14,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f50,plain,(
% 3.61/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f14])).
% 3.61/1.00  
% 3.61/1.00  fof(f15,axiom,(
% 3.61/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f51,plain,(
% 3.61/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f15])).
% 3.61/1.00  
% 3.61/1.00  fof(f72,plain,(
% 3.61/1.00    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f51,f67])).
% 3.61/1.00  
% 3.61/1.00  fof(f73,plain,(
% 3.61/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 3.61/1.00    inference(definition_unfolding,[],[f50,f68,f56,f72])).
% 3.61/1.00  
% 3.61/1.00  fof(f6,axiom,(
% 3.61/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f42,plain,(
% 3.61/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.61/1.00    inference(cnf_transformation,[],[f6])).
% 3.61/1.00  
% 3.61/1.00  fof(f77,plain,(
% 3.61/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.61/1.00    inference(definition_unfolding,[],[f42,f68])).
% 3.61/1.00  
% 3.61/1.00  fof(f24,conjecture,(
% 3.61/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f25,negated_conjecture,(
% 3.61/1.00    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.61/1.00    inference(negated_conjecture,[],[f24])).
% 3.61/1.00  
% 3.61/1.00  fof(f28,plain,(
% 3.61/1.00    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.61/1.00    inference(ennf_transformation,[],[f25])).
% 3.61/1.00  
% 3.61/1.00  fof(f33,plain,(
% 3.61/1.00    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.61/1.00    introduced(choice_axiom,[])).
% 3.61/1.00  
% 3.61/1.00  fof(f34,plain,(
% 3.61/1.00    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.61/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).
% 3.61/1.00  
% 3.61/1.00  fof(f62,plain,(
% 3.61/1.00    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.61/1.00    inference(cnf_transformation,[],[f34])).
% 3.61/1.00  
% 3.61/1.00  fof(f84,plain,(
% 3.61/1.00    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 3.61/1.00    inference(definition_unfolding,[],[f62,f68,f67])).
% 3.61/1.00  
% 3.61/1.00  fof(f4,axiom,(
% 3.61/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f29,plain,(
% 3.61/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/1.00    inference(nnf_transformation,[],[f4])).
% 3.61/1.00  
% 3.61/1.00  fof(f30,plain,(
% 3.61/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/1.00    inference(flattening,[],[f29])).
% 3.61/1.00  
% 3.61/1.00  fof(f40,plain,(
% 3.61/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f30])).
% 3.61/1.00  
% 3.61/1.00  fof(f23,axiom,(
% 3.61/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f31,plain,(
% 3.61/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.61/1.00    inference(nnf_transformation,[],[f23])).
% 3.61/1.00  
% 3.61/1.00  fof(f32,plain,(
% 3.61/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.61/1.00    inference(flattening,[],[f31])).
% 3.61/1.00  
% 3.61/1.00  fof(f59,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f32])).
% 3.61/1.00  
% 3.61/1.00  fof(f83,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f59,f67])).
% 3.61/1.00  
% 3.61/1.00  fof(f63,plain,(
% 3.61/1.00    ~r2_hidden(sK0,sK2)),
% 3.61/1.00    inference(cnf_transformation,[],[f34])).
% 3.61/1.00  
% 3.61/1.00  cnf(c_11,plain,
% 3.61/1.00      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
% 3.61/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_13,plain,
% 3.61/1.00      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X4,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.61/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4181,plain,
% 3.61/1.00      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X4,X5,X6))) = k5_enumset1(X0,X1,X2,X6,X5,X4,X3) ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_11,c_13]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_9406,plain,
% 3.61/1.00      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X6,X5,X4,X3) ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_4181,c_13]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_9702,plain,
% 3.61/1.00      ( k5_enumset1(X0,X0,X0,X1,X2,X3,X0) = k5_enumset1(X1,X1,X1,X1,X2,X3,X0) ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_9406,c_11]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_0,plain,
% 3.61/1.00      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.61/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4142,plain,
% 3.61/1.00      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X4,X4))) = k5_enumset1(X3,X3,X3,X2,X1,X0,X4) ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_5996,plain,
% 3.61/1.00      ( k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X3,X3,X3,X2,X1,X0,X4) ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_4142,c_0]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4183,plain,
% 3.61/1.00      ( k5_enumset1(X0,X1,X2,X3,X3,X3,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4368,plain,
% 3.61/1.00      ( k5_enumset1(X0,X1,X2,X3,X3,X3,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_4183,c_11]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_5948,plain,
% 3.61/1.00      ( k5_enumset1(X0,X0,X0,X1,X2,X2,X3) = k5_enumset1(X2,X1,X0,X3,X3,X3,X3) ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_13,c_4142]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_8,plain,
% 3.61/1.00      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 3.61/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4052,plain,
% 3.61/1.00      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.61/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4367,plain,
% 3.61/1.00      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X1,X1,X1,X1))) = iProver_top ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_4183,c_4052]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_6129,plain,
% 3.61/1.00      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X0,X1,X1,X1,X1))) = iProver_top ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_5948,c_4367]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_7808,plain,
% 3.61/1.00      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X1,X1))) = iProver_top ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_4368,c_6129]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_8007,plain,
% 3.61/1.00      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X0,X1,X1,X1))) = iProver_top ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_5996,c_7808]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_10046,plain,
% 3.61/1.00      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X1,X1))) = iProver_top ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_9702,c_8007]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_18,negated_conjecture,
% 3.61/1.00      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 3.61/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4047,plain,
% 3.61/1.00      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 3.61/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4127,plain,
% 3.61/1.00      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.61/1.00      inference(demodulation,[status(thm)],[c_11,c_4047]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4,plain,
% 3.61/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.61/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4054,plain,
% 3.61/1.00      ( X0 = X1
% 3.61/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.61/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.61/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4307,plain,
% 3.61/1.00      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.61/1.00      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_4127,c_4054]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_11858,plain,
% 3.61/1.00      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_10046,c_4307]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4129,plain,
% 3.61/1.00      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_11,c_4052]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_11892,plain,
% 3.61/1.00      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_11858,c_4129]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_16,plain,
% 3.61/1.00      ( r2_hidden(X0,X1)
% 3.61/1.00      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
% 3.61/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4049,plain,
% 3.61/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.61/1.00      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.61/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_11906,plain,
% 3.61/1.00      ( r2_hidden(sK0,sK2) = iProver_top ),
% 3.61/1.00      inference(superposition,[status(thm)],[c_11892,c_4049]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_17,negated_conjecture,
% 3.61/1.00      ( ~ r2_hidden(sK0,sK2) ),
% 3.61/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_20,plain,
% 3.61/1.00      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.61/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(contradiction,plain,
% 3.61/1.00      ( $false ),
% 3.61/1.00      inference(minisat,[status(thm)],[c_11906,c_20]) ).
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/1.00  
% 3.61/1.00  ------                               Statistics
% 3.61/1.00  
% 3.61/1.00  ------ Selected
% 3.61/1.00  
% 3.61/1.00  total_time:                             0.471
% 3.61/1.00  
%------------------------------------------------------------------------------
