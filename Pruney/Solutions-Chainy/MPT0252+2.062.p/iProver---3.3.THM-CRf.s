%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:30 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 342 expanded)
%              Number of clauses        :   23 (  29 expanded)
%              Number of leaves         :   16 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  118 ( 392 expanded)
%              Number of equality atoms :   61 ( 319 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f64,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f46,f65,f52,f64])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f45,f65,f52,f67])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f43,f63,f63])).

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

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).

fof(f59,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f59,f65,f64])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f60,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4196,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_10,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3994,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4074,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10,c_3994])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4001,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4247,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4074,c_4001])).

cnf(c_4483,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4196,c_4247])).

cnf(c_7,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3999,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4621,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4483,c_3999])).

cnf(c_4078,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_3999])).

cnf(c_4532,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4196,c_4078])).

cnf(c_4632,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4621,c_4532])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3996,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5109,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4632,c_3996])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5109,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:15:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.50/0.92  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/0.92  
% 3.50/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.92  
% 3.50/0.92  ------  iProver source info
% 3.50/0.92  
% 3.50/0.92  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.92  git: non_committed_changes: false
% 3.50/0.92  git: last_make_outside_of_git: false
% 3.50/0.92  
% 3.50/0.92  ------ 
% 3.50/0.92  ------ Parsing...
% 3.50/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  ------ Proving...
% 3.50/0.92  ------ Problem Properties 
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  clauses                                 18
% 3.50/0.92  conjectures                             2
% 3.50/0.92  EPR                                     3
% 3.50/0.92  Horn                                    18
% 3.50/0.92  unary                                   14
% 3.50/0.92  binary                                  2
% 3.50/0.92  lits                                    24
% 3.50/0.92  lits eq                                 10
% 3.50/0.92  fd_pure                                 0
% 3.50/0.92  fd_pseudo                               0
% 3.50/0.92  fd_cond                                 0
% 3.50/0.92  fd_pseudo_cond                          1
% 3.50/0.92  AC symbols                              1
% 3.50/0.92  
% 3.50/0.92  ------ Input Options Time Limit: Unbounded
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing...
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.50/0.92  Current options:
% 3.50/0.92  ------ 
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/0.92  
% 3.50/0.92  ------ Proving...
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  % SZS status Theorem for theBenchmark.p
% 3.50/0.92  
% 3.50/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.92  
% 3.50/0.92  fof(f19,axiom,(
% 3.50/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f53,plain,(
% 3.50/0.92    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f19])).
% 3.50/0.92  
% 3.50/0.92  fof(f12,axiom,(
% 3.50/0.92    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f46,plain,(
% 3.50/0.92    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f12])).
% 3.50/0.92  
% 3.50/0.92  fof(f20,axiom,(
% 3.50/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f54,plain,(
% 3.50/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.50/0.92    inference(cnf_transformation,[],[f20])).
% 3.50/0.92  
% 3.50/0.92  fof(f65,plain,(
% 3.50/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.50/0.92    inference(definition_unfolding,[],[f54,f64])).
% 3.50/0.92  
% 3.50/0.92  fof(f14,axiom,(
% 3.50/0.92    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f48,plain,(
% 3.50/0.92    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f14])).
% 3.50/0.92  
% 3.50/0.92  fof(f15,axiom,(
% 3.50/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f49,plain,(
% 3.50/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f15])).
% 3.50/0.92  
% 3.50/0.92  fof(f16,axiom,(
% 3.50/0.92    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f50,plain,(
% 3.50/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f16])).
% 3.50/0.92  
% 3.50/0.92  fof(f17,axiom,(
% 3.50/0.92    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f51,plain,(
% 3.50/0.92    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f17])).
% 3.50/0.92  
% 3.50/0.92  fof(f18,axiom,(
% 3.50/0.92    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f52,plain,(
% 3.50/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f18])).
% 3.50/0.92  
% 3.50/0.92  fof(f61,plain,(
% 3.50/0.92    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.50/0.92    inference(definition_unfolding,[],[f51,f52])).
% 3.50/0.92  
% 3.50/0.92  fof(f62,plain,(
% 3.50/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.50/0.92    inference(definition_unfolding,[],[f50,f61])).
% 3.50/0.92  
% 3.50/0.92  fof(f63,plain,(
% 3.50/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.50/0.92    inference(definition_unfolding,[],[f49,f62])).
% 3.50/0.92  
% 3.50/0.92  fof(f64,plain,(
% 3.50/0.92    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.50/0.92    inference(definition_unfolding,[],[f48,f63])).
% 3.50/0.92  
% 3.50/0.92  fof(f68,plain,(
% 3.50/0.92    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) )),
% 3.50/0.92    inference(definition_unfolding,[],[f46,f65,f52,f64])).
% 3.50/0.92  
% 3.50/0.92  fof(f75,plain,(
% 3.50/0.92    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 3.50/0.92    inference(definition_unfolding,[],[f53,f68])).
% 3.50/0.92  
% 3.50/0.92  fof(f11,axiom,(
% 3.50/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f45,plain,(
% 3.50/0.92    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f11])).
% 3.50/0.92  
% 3.50/0.92  fof(f13,axiom,(
% 3.50/0.92    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f47,plain,(
% 3.50/0.92    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f13])).
% 3.50/0.92  
% 3.50/0.92  fof(f67,plain,(
% 3.50/0.92    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.50/0.92    inference(definition_unfolding,[],[f47,f64])).
% 3.50/0.92  
% 3.50/0.92  fof(f69,plain,(
% 3.50/0.92    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 3.50/0.92    inference(definition_unfolding,[],[f45,f65,f52,f67])).
% 3.50/0.92  
% 3.50/0.92  fof(f9,axiom,(
% 3.50/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f43,plain,(
% 3.50/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f9])).
% 3.50/0.92  
% 3.50/0.92  fof(f73,plain,(
% 3.50/0.92    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) )),
% 3.50/0.92    inference(definition_unfolding,[],[f43,f63,f63])).
% 3.50/0.92  
% 3.50/0.92  fof(f23,conjecture,(
% 3.50/0.92    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f24,negated_conjecture,(
% 3.50/0.92    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.50/0.92    inference(negated_conjecture,[],[f23])).
% 3.50/0.92  
% 3.50/0.92  fof(f26,plain,(
% 3.50/0.92    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.50/0.92    inference(ennf_transformation,[],[f24])).
% 3.50/0.92  
% 3.50/0.92  fof(f31,plain,(
% 3.50/0.92    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.50/0.92    introduced(choice_axiom,[])).
% 3.50/0.92  
% 3.50/0.92  fof(f32,plain,(
% 3.50/0.92    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.50/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).
% 3.50/0.92  
% 3.50/0.92  fof(f59,plain,(
% 3.50/0.92    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.50/0.92    inference(cnf_transformation,[],[f32])).
% 3.50/0.92  
% 3.50/0.92  fof(f80,plain,(
% 3.50/0.92    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 3.50/0.92    inference(definition_unfolding,[],[f59,f65,f64])).
% 3.50/0.92  
% 3.50/0.92  fof(f3,axiom,(
% 3.50/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f27,plain,(
% 3.50/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.92    inference(nnf_transformation,[],[f3])).
% 3.50/0.92  
% 3.50/0.92  fof(f28,plain,(
% 3.50/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.92    inference(flattening,[],[f27])).
% 3.50/0.92  
% 3.50/0.92  fof(f37,plain,(
% 3.50/0.92    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f28])).
% 3.50/0.92  
% 3.50/0.92  fof(f5,axiom,(
% 3.50/0.92    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f39,plain,(
% 3.50/0.92    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.50/0.92    inference(cnf_transformation,[],[f5])).
% 3.50/0.92  
% 3.50/0.92  fof(f72,plain,(
% 3.50/0.92    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.50/0.92    inference(definition_unfolding,[],[f39,f65])).
% 3.50/0.92  
% 3.50/0.92  fof(f22,axiom,(
% 3.50/0.92    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.50/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.92  
% 3.50/0.92  fof(f29,plain,(
% 3.50/0.92    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.50/0.92    inference(nnf_transformation,[],[f22])).
% 3.50/0.92  
% 3.50/0.92  fof(f30,plain,(
% 3.50/0.92    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.50/0.92    inference(flattening,[],[f29])).
% 3.50/0.92  
% 3.50/0.92  fof(f56,plain,(
% 3.50/0.92    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.50/0.92    inference(cnf_transformation,[],[f30])).
% 3.50/0.92  
% 3.50/0.92  fof(f79,plain,(
% 3.50/0.92    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 3.50/0.92    inference(definition_unfolding,[],[f56,f64])).
% 3.50/0.92  
% 3.50/0.92  fof(f60,plain,(
% 3.50/0.92    ~r2_hidden(sK0,sK2)),
% 3.50/0.92    inference(cnf_transformation,[],[f32])).
% 3.50/0.92  
% 3.50/0.92  cnf(c_12,plain,
% 3.50/0.92      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.50/0.92      inference(cnf_transformation,[],[f75]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_0,plain,
% 3.50/0.92      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.50/0.92      inference(cnf_transformation,[],[f69]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_4196,plain,
% 3.50/0.92      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
% 3.50/0.92      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_10,plain,
% 3.50/0.92      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
% 3.50/0.92      inference(cnf_transformation,[],[f73]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_18,negated_conjecture,
% 3.50/0.92      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 3.50/0.92      inference(cnf_transformation,[],[f80]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_3994,plain,
% 3.50/0.92      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 3.50/0.92      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_4074,plain,
% 3.50/0.92      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.50/0.92      inference(demodulation,[status(thm)],[c_10,c_3994]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_3,plain,
% 3.50/0.92      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.50/0.92      inference(cnf_transformation,[],[f37]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_4001,plain,
% 3.50/0.92      ( X0 = X1
% 3.50/0.92      | r1_tarski(X0,X1) != iProver_top
% 3.50/0.92      | r1_tarski(X1,X0) != iProver_top ),
% 3.50/0.92      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_4247,plain,
% 3.50/0.92      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.50/0.92      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.50/0.92      inference(superposition,[status(thm)],[c_4074,c_4001]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_4483,plain,
% 3.50/0.92      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.50/0.92      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.50/0.92      inference(demodulation,[status(thm)],[c_4196,c_4247]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_7,plain,
% 3.50/0.92      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 3.50/0.92      inference(cnf_transformation,[],[f72]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_3999,plain,
% 3.50/0.92      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.50/0.92      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_4621,plain,
% 3.50/0.92      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 3.50/0.92      inference(forward_subsumption_resolution,
% 3.50/0.92                [status(thm)],
% 3.50/0.92                [c_4483,c_3999]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_4078,plain,
% 3.50/0.92      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X0,X0))) = iProver_top ),
% 3.50/0.92      inference(superposition,[status(thm)],[c_10,c_3999]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_4532,plain,
% 3.50/0.92      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 3.50/0.92      inference(superposition,[status(thm)],[c_4196,c_4078]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_4632,plain,
% 3.50/0.92      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 3.50/0.92      inference(superposition,[status(thm)],[c_4621,c_4532]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_16,plain,
% 3.50/0.92      ( r2_hidden(X0,X1)
% 3.50/0.92      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
% 3.50/0.92      inference(cnf_transformation,[],[f79]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_3996,plain,
% 3.50/0.92      ( r2_hidden(X0,X1) = iProver_top
% 3.50/0.92      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.50/0.92      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_5109,plain,
% 3.50/0.92      ( r2_hidden(sK0,sK2) = iProver_top ),
% 3.50/0.92      inference(superposition,[status(thm)],[c_4632,c_3996]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_17,negated_conjecture,
% 3.50/0.92      ( ~ r2_hidden(sK0,sK2) ),
% 3.50/0.92      inference(cnf_transformation,[],[f60]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(c_20,plain,
% 3.50/0.92      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.50/0.92      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.50/0.92  
% 3.50/0.92  cnf(contradiction,plain,
% 3.50/0.92      ( $false ),
% 3.50/0.92      inference(minisat,[status(thm)],[c_5109,c_20]) ).
% 3.50/0.92  
% 3.50/0.92  
% 3.50/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/0.92  
% 3.50/0.92  ------                               Statistics
% 3.50/0.92  
% 3.50/0.92  ------ Selected
% 3.50/0.92  
% 3.50/0.92  total_time:                             0.178
% 3.50/0.92  
%------------------------------------------------------------------------------
