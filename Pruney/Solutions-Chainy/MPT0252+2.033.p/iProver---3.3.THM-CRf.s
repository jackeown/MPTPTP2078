%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:26 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 557 expanded)
%              Number of clauses        :   29 (  43 expanded)
%              Number of leaves         :   17 ( 183 expanded)
%              Depth                    :   18
%              Number of atoms          :  126 ( 606 expanded)
%              Number of equality atoms :   69 ( 533 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f65,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f48,f66,f54,f65])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f49,f65])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f47,f66,f54,f68])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X2,X0,X3) ),
    inference(definition_unfolding,[],[f45,f63,f63])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f46,f63,f63])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f32])).

fof(f60,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f60,f66,f65])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f66])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f61,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4214,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_11,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X2,X2,X2,X2,X0,X1,X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_12,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4030,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4117,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12,c_4030])).

cnf(c_4142,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_4117])).

cnf(c_4854,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4214,c_4142])).

cnf(c_5140,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4214,c_4854])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4037,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5154,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5140,c_4037])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4035,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5171,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5154,c_4035])).

cnf(c_4939,plain,
    ( k5_enumset1(X0,X0,X0,X1,X2,X3,X3) = k5_enumset1(X1,X1,X1,X1,X2,X0,X3) ),
    inference(superposition,[status(thm)],[c_4214,c_11])).

cnf(c_4126,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_4035])).

cnf(c_4245,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_4126])).

cnf(c_4921,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4214,c_4245])).

cnf(c_11576,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4939,c_4921])).

cnf(c_14054,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5171,c_11576])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4032,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14132,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_14054,c_4032])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14132,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 16:35:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.74/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/1.51  
% 7.74/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.51  
% 7.74/1.51  ------  iProver source info
% 7.74/1.51  
% 7.74/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.51  git: non_committed_changes: false
% 7.74/1.51  git: last_make_outside_of_git: false
% 7.74/1.51  
% 7.74/1.51  ------ 
% 7.74/1.51  ------ Parsing...
% 7.74/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  ------ Proving...
% 7.74/1.51  ------ Problem Properties 
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  clauses                                 18
% 7.74/1.51  conjectures                             2
% 7.74/1.51  EPR                                     3
% 7.74/1.51  Horn                                    18
% 7.74/1.51  unary                                   14
% 7.74/1.51  binary                                  2
% 7.74/1.51  lits                                    24
% 7.74/1.51  lits eq                                 10
% 7.74/1.51  fd_pure                                 0
% 7.74/1.51  fd_pseudo                               0
% 7.74/1.51  fd_cond                                 0
% 7.74/1.51  fd_pseudo_cond                          1
% 7.74/1.51  AC symbols                              1
% 7.74/1.51  
% 7.74/1.51  ------ Input Options Time Limit: Unbounded
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing...
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.74/1.51  Current options:
% 7.74/1.51  ------ 
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  % SZS status Theorem for theBenchmark.p
% 7.74/1.51  
% 7.74/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.51  
% 7.74/1.51  fof(f20,axiom,(
% 7.74/1.51    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f55,plain,(
% 7.74/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f20])).
% 7.74/1.51  
% 7.74/1.51  fof(f13,axiom,(
% 7.74/1.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f48,plain,(
% 7.74/1.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f13])).
% 7.74/1.51  
% 7.74/1.51  fof(f21,axiom,(
% 7.74/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f56,plain,(
% 7.74/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.74/1.51    inference(cnf_transformation,[],[f21])).
% 7.74/1.51  
% 7.74/1.51  fof(f66,plain,(
% 7.74/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 7.74/1.51    inference(definition_unfolding,[],[f56,f65])).
% 7.74/1.51  
% 7.74/1.51  fof(f15,axiom,(
% 7.74/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f50,plain,(
% 7.74/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f15])).
% 7.74/1.51  
% 7.74/1.51  fof(f16,axiom,(
% 7.74/1.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f51,plain,(
% 7.74/1.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f16])).
% 7.74/1.51  
% 7.74/1.51  fof(f17,axiom,(
% 7.74/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f52,plain,(
% 7.74/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f17])).
% 7.74/1.51  
% 7.74/1.51  fof(f18,axiom,(
% 7.74/1.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f53,plain,(
% 7.74/1.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f18])).
% 7.74/1.51  
% 7.74/1.51  fof(f19,axiom,(
% 7.74/1.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f54,plain,(
% 7.74/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f19])).
% 7.74/1.51  
% 7.74/1.51  fof(f62,plain,(
% 7.74/1.51    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.74/1.51    inference(definition_unfolding,[],[f53,f54])).
% 7.74/1.51  
% 7.74/1.51  fof(f63,plain,(
% 7.74/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 7.74/1.51    inference(definition_unfolding,[],[f52,f62])).
% 7.74/1.51  
% 7.74/1.51  fof(f64,plain,(
% 7.74/1.51    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.74/1.51    inference(definition_unfolding,[],[f51,f63])).
% 7.74/1.51  
% 7.74/1.51  fof(f65,plain,(
% 7.74/1.51    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.74/1.51    inference(definition_unfolding,[],[f50,f64])).
% 7.74/1.51  
% 7.74/1.51  fof(f69,plain,(
% 7.74/1.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) )),
% 7.74/1.51    inference(definition_unfolding,[],[f48,f66,f54,f65])).
% 7.74/1.51  
% 7.74/1.51  fof(f77,plain,(
% 7.74/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 7.74/1.51    inference(definition_unfolding,[],[f55,f69])).
% 7.74/1.51  
% 7.74/1.51  fof(f12,axiom,(
% 7.74/1.51    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f47,plain,(
% 7.74/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f12])).
% 7.74/1.51  
% 7.74/1.51  fof(f14,axiom,(
% 7.74/1.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f49,plain,(
% 7.74/1.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f14])).
% 7.74/1.51  
% 7.74/1.51  fof(f68,plain,(
% 7.74/1.51    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 7.74/1.51    inference(definition_unfolding,[],[f49,f65])).
% 7.74/1.51  
% 7.74/1.51  fof(f70,plain,(
% 7.74/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 7.74/1.51    inference(definition_unfolding,[],[f47,f66,f54,f68])).
% 7.74/1.51  
% 7.74/1.51  fof(f10,axiom,(
% 7.74/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f45,plain,(
% 7.74/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f10])).
% 7.74/1.51  
% 7.74/1.51  fof(f75,plain,(
% 7.74/1.51    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X2,X0,X3)) )),
% 7.74/1.51    inference(definition_unfolding,[],[f45,f63,f63])).
% 7.74/1.51  
% 7.74/1.51  fof(f11,axiom,(
% 7.74/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f46,plain,(
% 7.74/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f11])).
% 7.74/1.51  
% 7.74/1.51  fof(f76,plain,(
% 7.74/1.51    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1)) )),
% 7.74/1.51    inference(definition_unfolding,[],[f46,f63,f63])).
% 7.74/1.51  
% 7.74/1.51  fof(f23,conjecture,(
% 7.74/1.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f24,negated_conjecture,(
% 7.74/1.51    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 7.74/1.51    inference(negated_conjecture,[],[f23])).
% 7.74/1.51  
% 7.74/1.51  fof(f27,plain,(
% 7.74/1.51    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 7.74/1.51    inference(ennf_transformation,[],[f24])).
% 7.74/1.51  
% 7.74/1.51  fof(f32,plain,(
% 7.74/1.51    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 7.74/1.51    introduced(choice_axiom,[])).
% 7.74/1.51  
% 7.74/1.51  fof(f33,plain,(
% 7.74/1.51    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 7.74/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f32])).
% 7.74/1.51  
% 7.74/1.51  fof(f60,plain,(
% 7.74/1.51    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 7.74/1.51    inference(cnf_transformation,[],[f33])).
% 7.74/1.51  
% 7.74/1.51  fof(f81,plain,(
% 7.74/1.51    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 7.74/1.51    inference(definition_unfolding,[],[f60,f66,f65])).
% 7.74/1.51  
% 7.74/1.51  fof(f4,axiom,(
% 7.74/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f28,plain,(
% 7.74/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.74/1.51    inference(nnf_transformation,[],[f4])).
% 7.74/1.51  
% 7.74/1.51  fof(f29,plain,(
% 7.74/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.74/1.51    inference(flattening,[],[f28])).
% 7.74/1.51  
% 7.74/1.51  fof(f39,plain,(
% 7.74/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f29])).
% 7.74/1.51  
% 7.74/1.51  fof(f6,axiom,(
% 7.74/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f41,plain,(
% 7.74/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.74/1.51    inference(cnf_transformation,[],[f6])).
% 7.74/1.51  
% 7.74/1.51  fof(f74,plain,(
% 7.74/1.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.74/1.51    inference(definition_unfolding,[],[f41,f66])).
% 7.74/1.51  
% 7.74/1.51  fof(f22,axiom,(
% 7.74/1.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f30,plain,(
% 7.74/1.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.74/1.51    inference(nnf_transformation,[],[f22])).
% 7.74/1.51  
% 7.74/1.51  fof(f31,plain,(
% 7.74/1.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.74/1.51    inference(flattening,[],[f30])).
% 7.74/1.51  
% 7.74/1.51  fof(f57,plain,(
% 7.74/1.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f31])).
% 7.74/1.51  
% 7.74/1.51  fof(f80,plain,(
% 7.74/1.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 7.74/1.51    inference(definition_unfolding,[],[f57,f65])).
% 7.74/1.51  
% 7.74/1.51  fof(f61,plain,(
% 7.74/1.51    ~r2_hidden(sK0,sK2)),
% 7.74/1.51    inference(cnf_transformation,[],[f33])).
% 7.74/1.51  
% 7.74/1.51  cnf(c_13,plain,
% 7.74/1.51      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 7.74/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_0,plain,
% 7.74/1.51      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 7.74/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4214,plain,
% 7.74/1.51      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_11,plain,
% 7.74/1.51      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X2,X2,X2,X2,X0,X1,X3) ),
% 7.74/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_12,plain,
% 7.74/1.51      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1) ),
% 7.74/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_18,negated_conjecture,
% 7.74/1.51      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 7.74/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4030,plain,
% 7.74/1.51      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4117,plain,
% 7.74/1.51      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 7.74/1.51      inference(demodulation,[status(thm)],[c_12,c_4030]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4142,plain,
% 7.74/1.51      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_11,c_4117]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4854,plain,
% 7.74/1.51      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 7.74/1.51      inference(demodulation,[status(thm)],[c_4214,c_4142]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5140,plain,
% 7.74/1.51      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_4214,c_4854]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4,plain,
% 7.74/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.74/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4037,plain,
% 7.74/1.51      ( X0 = X1
% 7.74/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.74/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5154,plain,
% 7.74/1.51      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 7.74/1.51      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_5140,c_4037]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_8,plain,
% 7.74/1.51      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 7.74/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4035,plain,
% 7.74/1.51      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5171,plain,
% 7.74/1.51      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 7.74/1.51      inference(forward_subsumption_resolution,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_5154,c_4035]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4939,plain,
% 7.74/1.51      ( k5_enumset1(X0,X0,X0,X1,X2,X3,X3) = k5_enumset1(X1,X1,X1,X1,X2,X0,X3) ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_4214,c_11]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4126,plain,
% 7.74/1.51      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X0,X0))) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_12,c_4035]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4245,plain,
% 7.74/1.51      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_11,c_4126]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4921,plain,
% 7.74/1.51      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X0,X0))) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_4214,c_4245]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_11576,plain,
% 7.74/1.51      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_4939,c_4921]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_14054,plain,
% 7.74/1.51      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_5171,c_11576]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_16,plain,
% 7.74/1.51      ( r2_hidden(X0,X1)
% 7.74/1.51      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
% 7.74/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4032,plain,
% 7.74/1.51      ( r2_hidden(X0,X1) = iProver_top
% 7.74/1.51      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_14132,plain,
% 7.74/1.51      ( r2_hidden(sK0,sK2) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_14054,c_4032]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_17,negated_conjecture,
% 7.74/1.51      ( ~ r2_hidden(sK0,sK2) ),
% 7.74/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_20,plain,
% 7.74/1.51      ( r2_hidden(sK0,sK2) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(contradiction,plain,
% 7.74/1.51      ( $false ),
% 7.74/1.51      inference(minisat,[status(thm)],[c_14132,c_20]) ).
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.51  
% 7.74/1.51  ------                               Statistics
% 7.74/1.51  
% 7.74/1.51  ------ Selected
% 7.74/1.51  
% 7.74/1.51  total_time:                             0.652
% 7.74/1.51  
%------------------------------------------------------------------------------
