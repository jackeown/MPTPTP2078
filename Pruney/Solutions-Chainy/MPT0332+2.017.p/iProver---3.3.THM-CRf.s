%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:20 EST 2020

% Result     : Theorem 35.23s
% Output     : CNFRefutation 35.23s
% Verified   : 
% Statistics : Number of formulae       :   97 (1771 expanded)
%              Number of clauses        :   50 ( 420 expanded)
%              Number of leaves         :   16 ( 499 expanded)
%              Depth                    :   24
%              Number of atoms          :  123 (2642 expanded)
%              Number of equality atoms :   96 (1793 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k2_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f34,f38,f43])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f36,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f37,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != sK2 ),
    inference(definition_unfolding,[],[f37,f38,f43,f43])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k2_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_115,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k2_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_114,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_342,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)),k2_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))) = sK2
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_115,c_114])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_113,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_579,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) = sK2 ),
    inference(superposition,[status(thm)],[c_342,c_113])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_640,plain,
    ( k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_579,c_0])).

cnf(c_1137,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))) = k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_640,c_0])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1143,plain,
    ( k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_1137,c_2,c_4])).

cnf(c_408,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))))) = k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),X1) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_17562,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))))) = k2_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1143,c_408])).

cnf(c_17710,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))))) = k2_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_17562,c_640,c_1143])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_256,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_553,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_256])).

cnf(c_571,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_553,c_2])).

cnf(c_572,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_571,c_256])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_360,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k5_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_3974,plain,
    ( k5_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_360])).

cnf(c_4058,plain,
    ( k5_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k5_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3974,c_2])).

cnf(c_14615,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_640,c_4058])).

cnf(c_3986,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),k5_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_640,c_360])).

cnf(c_4048,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_3986,c_572])).

cnf(c_7408,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_4048])).

cnf(c_7476,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = sK2 ),
    inference(demodulation,[status(thm)],[c_7408,c_2])).

cnf(c_14715,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_14615,c_640,c_7476])).

cnf(c_16256,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),X0)) = k5_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_14715,c_3])).

cnf(c_17711,plain,
    ( k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_17710,c_2,c_4,c_572,c_1143,c_16256])).

cnf(c_17712,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_17711,c_2,c_4,c_640])).

cnf(c_400,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_417,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_400,c_4])).

cnf(c_418,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_417,c_2])).

cnf(c_1138,plain,
    ( k2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_640,c_418])).

cnf(c_1142,plain,
    ( k2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_1138,c_640])).

cnf(c_20647,plain,
    ( k2_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_17712,c_1142])).

cnf(c_6,negated_conjecture,
    ( k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != sK2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_252,plain,
    ( k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != sK2 ),
    inference(demodulation,[status(thm)],[c_3,c_6])).

cnf(c_287,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != sK2 ),
    inference(demodulation,[status(thm)],[c_252,c_256])).

cnf(c_1003,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != sK2 ),
    inference(demodulation,[status(thm)],[c_571,c_287])).

cnf(c_2293,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != sK2 ),
    inference(light_normalisation,[status(thm)],[c_1003,c_1143])).

cnf(c_97526,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != sK2 ),
    inference(demodulation,[status(thm)],[c_20647,c_2293])).

cnf(c_20641,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_17712,c_14715])).

cnf(c_97527,plain,
    ( sK2 != sK2 ),
    inference(light_normalisation,[status(thm)],[c_97526,c_20641])).

cnf(c_97528,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_97527])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.23/4.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.23/4.98  
% 35.23/4.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.23/4.98  
% 35.23/4.98  ------  iProver source info
% 35.23/4.98  
% 35.23/4.98  git: date: 2020-06-30 10:37:57 +0100
% 35.23/4.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.23/4.98  git: non_committed_changes: false
% 35.23/4.98  git: last_make_outside_of_git: false
% 35.23/4.98  
% 35.23/4.98  ------ 
% 35.23/4.98  
% 35.23/4.98  ------ Input Options
% 35.23/4.98  
% 35.23/4.98  --out_options                           all
% 35.23/4.98  --tptp_safe_out                         true
% 35.23/4.98  --problem_path                          ""
% 35.23/4.98  --include_path                          ""
% 35.23/4.98  --clausifier                            res/vclausify_rel
% 35.23/4.98  --clausifier_options                    ""
% 35.23/4.98  --stdin                                 false
% 35.23/4.98  --stats_out                             all
% 35.23/4.98  
% 35.23/4.98  ------ General Options
% 35.23/4.98  
% 35.23/4.98  --fof                                   false
% 35.23/4.98  --time_out_real                         305.
% 35.23/4.98  --time_out_virtual                      -1.
% 35.23/4.98  --symbol_type_check                     false
% 35.23/4.98  --clausify_out                          false
% 35.23/4.98  --sig_cnt_out                           false
% 35.23/4.98  --trig_cnt_out                          false
% 35.23/4.98  --trig_cnt_out_tolerance                1.
% 35.23/4.98  --trig_cnt_out_sk_spl                   false
% 35.23/4.98  --abstr_cl_out                          false
% 35.23/4.98  
% 35.23/4.98  ------ Global Options
% 35.23/4.98  
% 35.23/4.98  --schedule                              default
% 35.23/4.98  --add_important_lit                     false
% 35.23/4.98  --prop_solver_per_cl                    1000
% 35.23/4.98  --min_unsat_core                        false
% 35.23/4.98  --soft_assumptions                      false
% 35.23/4.98  --soft_lemma_size                       3
% 35.23/4.98  --prop_impl_unit_size                   0
% 35.23/4.98  --prop_impl_unit                        []
% 35.23/4.98  --share_sel_clauses                     true
% 35.23/4.98  --reset_solvers                         false
% 35.23/4.98  --bc_imp_inh                            [conj_cone]
% 35.23/4.98  --conj_cone_tolerance                   3.
% 35.23/4.98  --extra_neg_conj                        none
% 35.23/4.98  --large_theory_mode                     true
% 35.23/4.98  --prolific_symb_bound                   200
% 35.23/4.98  --lt_threshold                          2000
% 35.23/4.98  --clause_weak_htbl                      true
% 35.23/4.98  --gc_record_bc_elim                     false
% 35.23/4.98  
% 35.23/4.98  ------ Preprocessing Options
% 35.23/4.98  
% 35.23/4.98  --preprocessing_flag                    true
% 35.23/4.98  --time_out_prep_mult                    0.1
% 35.23/4.98  --splitting_mode                        input
% 35.23/4.98  --splitting_grd                         true
% 35.23/4.98  --splitting_cvd                         false
% 35.23/4.98  --splitting_cvd_svl                     false
% 35.23/4.98  --splitting_nvd                         32
% 35.23/4.98  --sub_typing                            true
% 35.23/4.98  --prep_gs_sim                           true
% 35.23/4.98  --prep_unflatten                        true
% 35.23/4.98  --prep_res_sim                          true
% 35.23/4.98  --prep_upred                            true
% 35.23/4.98  --prep_sem_filter                       exhaustive
% 35.23/4.98  --prep_sem_filter_out                   false
% 35.23/4.98  --pred_elim                             true
% 35.23/4.98  --res_sim_input                         true
% 35.23/4.98  --eq_ax_congr_red                       true
% 35.23/4.98  --pure_diseq_elim                       true
% 35.23/4.98  --brand_transform                       false
% 35.23/4.98  --non_eq_to_eq                          false
% 35.23/4.98  --prep_def_merge                        true
% 35.23/4.98  --prep_def_merge_prop_impl              false
% 35.23/4.98  --prep_def_merge_mbd                    true
% 35.23/4.98  --prep_def_merge_tr_red                 false
% 35.23/4.98  --prep_def_merge_tr_cl                  false
% 35.23/4.98  --smt_preprocessing                     true
% 35.23/4.98  --smt_ac_axioms                         fast
% 35.23/4.98  --preprocessed_out                      false
% 35.23/4.98  --preprocessed_stats                    false
% 35.23/4.98  
% 35.23/4.98  ------ Abstraction refinement Options
% 35.23/4.98  
% 35.23/4.98  --abstr_ref                             []
% 35.23/4.98  --abstr_ref_prep                        false
% 35.23/4.98  --abstr_ref_until_sat                   false
% 35.23/4.98  --abstr_ref_sig_restrict                funpre
% 35.23/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.23/4.98  --abstr_ref_under                       []
% 35.23/4.98  
% 35.23/4.98  ------ SAT Options
% 35.23/4.98  
% 35.23/4.98  --sat_mode                              false
% 35.23/4.98  --sat_fm_restart_options                ""
% 35.23/4.98  --sat_gr_def                            false
% 35.23/4.98  --sat_epr_types                         true
% 35.23/4.98  --sat_non_cyclic_types                  false
% 35.23/4.98  --sat_finite_models                     false
% 35.23/4.98  --sat_fm_lemmas                         false
% 35.23/4.98  --sat_fm_prep                           false
% 35.23/4.98  --sat_fm_uc_incr                        true
% 35.23/4.98  --sat_out_model                         small
% 35.23/4.98  --sat_out_clauses                       false
% 35.23/4.98  
% 35.23/4.98  ------ QBF Options
% 35.23/4.98  
% 35.23/4.98  --qbf_mode                              false
% 35.23/4.98  --qbf_elim_univ                         false
% 35.23/4.98  --qbf_dom_inst                          none
% 35.23/4.98  --qbf_dom_pre_inst                      false
% 35.23/4.98  --qbf_sk_in                             false
% 35.23/4.98  --qbf_pred_elim                         true
% 35.23/4.98  --qbf_split                             512
% 35.23/4.98  
% 35.23/4.98  ------ BMC1 Options
% 35.23/4.98  
% 35.23/4.98  --bmc1_incremental                      false
% 35.23/4.98  --bmc1_axioms                           reachable_all
% 35.23/4.98  --bmc1_min_bound                        0
% 35.23/4.98  --bmc1_max_bound                        -1
% 35.23/4.98  --bmc1_max_bound_default                -1
% 35.23/4.98  --bmc1_symbol_reachability              true
% 35.23/4.98  --bmc1_property_lemmas                  false
% 35.23/4.98  --bmc1_k_induction                      false
% 35.23/4.98  --bmc1_non_equiv_states                 false
% 35.23/4.98  --bmc1_deadlock                         false
% 35.23/4.98  --bmc1_ucm                              false
% 35.23/4.98  --bmc1_add_unsat_core                   none
% 35.23/4.98  --bmc1_unsat_core_children              false
% 35.23/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.23/4.98  --bmc1_out_stat                         full
% 35.23/4.98  --bmc1_ground_init                      false
% 35.23/4.98  --bmc1_pre_inst_next_state              false
% 35.23/4.98  --bmc1_pre_inst_state                   false
% 35.23/4.98  --bmc1_pre_inst_reach_state             false
% 35.23/4.98  --bmc1_out_unsat_core                   false
% 35.23/4.98  --bmc1_aig_witness_out                  false
% 35.23/4.98  --bmc1_verbose                          false
% 35.23/4.98  --bmc1_dump_clauses_tptp                false
% 35.23/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.23/4.98  --bmc1_dump_file                        -
% 35.23/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.23/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.23/4.98  --bmc1_ucm_extend_mode                  1
% 35.23/4.98  --bmc1_ucm_init_mode                    2
% 35.23/4.98  --bmc1_ucm_cone_mode                    none
% 35.23/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.23/4.98  --bmc1_ucm_relax_model                  4
% 35.23/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.23/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.23/4.98  --bmc1_ucm_layered_model                none
% 35.23/4.98  --bmc1_ucm_max_lemma_size               10
% 35.23/4.98  
% 35.23/4.98  ------ AIG Options
% 35.23/4.98  
% 35.23/4.98  --aig_mode                              false
% 35.23/4.98  
% 35.23/4.98  ------ Instantiation Options
% 35.23/4.98  
% 35.23/4.98  --instantiation_flag                    true
% 35.23/4.98  --inst_sos_flag                         true
% 35.23/4.98  --inst_sos_phase                        true
% 35.23/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.23/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.23/4.98  --inst_lit_sel_side                     num_symb
% 35.23/4.98  --inst_solver_per_active                1400
% 35.23/4.98  --inst_solver_calls_frac                1.
% 35.23/4.98  --inst_passive_queue_type               priority_queues
% 35.23/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.23/4.98  --inst_passive_queues_freq              [25;2]
% 35.23/4.98  --inst_dismatching                      true
% 35.23/4.98  --inst_eager_unprocessed_to_passive     true
% 35.23/4.98  --inst_prop_sim_given                   true
% 35.23/4.98  --inst_prop_sim_new                     false
% 35.23/4.98  --inst_subs_new                         false
% 35.23/4.98  --inst_eq_res_simp                      false
% 35.23/4.98  --inst_subs_given                       false
% 35.23/4.98  --inst_orphan_elimination               true
% 35.23/4.98  --inst_learning_loop_flag               true
% 35.23/4.98  --inst_learning_start                   3000
% 35.23/4.98  --inst_learning_factor                  2
% 35.23/4.98  --inst_start_prop_sim_after_learn       3
% 35.23/4.98  --inst_sel_renew                        solver
% 35.23/4.98  --inst_lit_activity_flag                true
% 35.23/4.98  --inst_restr_to_given                   false
% 35.23/4.98  --inst_activity_threshold               500
% 35.23/4.98  --inst_out_proof                        true
% 35.23/4.98  
% 35.23/4.98  ------ Resolution Options
% 35.23/4.98  
% 35.23/4.98  --resolution_flag                       true
% 35.23/4.98  --res_lit_sel                           adaptive
% 35.23/4.98  --res_lit_sel_side                      none
% 35.23/4.98  --res_ordering                          kbo
% 35.23/4.98  --res_to_prop_solver                    active
% 35.23/4.98  --res_prop_simpl_new                    false
% 35.23/4.98  --res_prop_simpl_given                  true
% 35.23/4.98  --res_passive_queue_type                priority_queues
% 35.23/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.23/4.98  --res_passive_queues_freq               [15;5]
% 35.23/4.98  --res_forward_subs                      full
% 35.23/4.98  --res_backward_subs                     full
% 35.23/4.98  --res_forward_subs_resolution           true
% 35.23/4.98  --res_backward_subs_resolution          true
% 35.23/4.98  --res_orphan_elimination                true
% 35.23/4.98  --res_time_limit                        2.
% 35.23/4.98  --res_out_proof                         true
% 35.23/4.98  
% 35.23/4.98  ------ Superposition Options
% 35.23/4.98  
% 35.23/4.98  --superposition_flag                    true
% 35.23/4.98  --sup_passive_queue_type                priority_queues
% 35.23/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.23/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.23/4.98  --demod_completeness_check              fast
% 35.23/4.98  --demod_use_ground                      true
% 35.23/4.98  --sup_to_prop_solver                    passive
% 35.23/4.98  --sup_prop_simpl_new                    true
% 35.23/4.98  --sup_prop_simpl_given                  true
% 35.23/4.98  --sup_fun_splitting                     true
% 35.23/4.98  --sup_smt_interval                      50000
% 35.23/4.98  
% 35.23/4.98  ------ Superposition Simplification Setup
% 35.23/4.98  
% 35.23/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.23/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.23/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.23/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.23/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.23/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.23/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.23/4.98  --sup_immed_triv                        [TrivRules]
% 35.23/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.23/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.23/4.98  --sup_immed_bw_main                     []
% 35.23/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.23/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.23/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.23/4.98  --sup_input_bw                          []
% 35.23/4.98  
% 35.23/4.98  ------ Combination Options
% 35.23/4.98  
% 35.23/4.98  --comb_res_mult                         3
% 35.23/4.98  --comb_sup_mult                         2
% 35.23/4.98  --comb_inst_mult                        10
% 35.23/4.98  
% 35.23/4.98  ------ Debug Options
% 35.23/4.98  
% 35.23/4.98  --dbg_backtrace                         false
% 35.23/4.98  --dbg_dump_prop_clauses                 false
% 35.23/4.98  --dbg_dump_prop_clauses_file            -
% 35.23/4.98  --dbg_out_stat                          false
% 35.23/4.98  ------ Parsing...
% 35.23/4.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.23/4.98  
% 35.23/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.23/4.98  
% 35.23/4.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.23/4.98  
% 35.23/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.23/4.98  ------ Proving...
% 35.23/4.98  ------ Problem Properties 
% 35.23/4.98  
% 35.23/4.98  
% 35.23/4.98  clauses                                 9
% 35.23/4.98  conjectures                             3
% 35.23/4.98  EPR                                     2
% 35.23/4.98  Horn                                    8
% 35.23/4.98  unary                                   8
% 35.23/4.98  binary                                  0
% 35.23/4.98  lits                                    11
% 35.23/4.98  lits eq                                 7
% 35.23/4.98  fd_pure                                 0
% 35.23/4.98  fd_pseudo                               0
% 35.23/4.98  fd_cond                                 0
% 35.23/4.98  fd_pseudo_cond                          0
% 35.23/4.98  AC symbols                              0
% 35.23/4.98  
% 35.23/4.98  ------ Schedule dynamic 5 is on 
% 35.23/4.98  
% 35.23/4.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.23/4.98  
% 35.23/4.98  
% 35.23/4.98  ------ 
% 35.23/4.98  Current options:
% 35.23/4.98  ------ 
% 35.23/4.98  
% 35.23/4.98  ------ Input Options
% 35.23/4.98  
% 35.23/4.98  --out_options                           all
% 35.23/4.98  --tptp_safe_out                         true
% 35.23/4.98  --problem_path                          ""
% 35.23/4.98  --include_path                          ""
% 35.23/4.98  --clausifier                            res/vclausify_rel
% 35.23/4.98  --clausifier_options                    ""
% 35.23/4.98  --stdin                                 false
% 35.23/4.98  --stats_out                             all
% 35.23/4.98  
% 35.23/4.98  ------ General Options
% 35.23/4.98  
% 35.23/4.98  --fof                                   false
% 35.23/4.98  --time_out_real                         305.
% 35.23/4.98  --time_out_virtual                      -1.
% 35.23/4.98  --symbol_type_check                     false
% 35.23/4.98  --clausify_out                          false
% 35.23/4.98  --sig_cnt_out                           false
% 35.23/4.98  --trig_cnt_out                          false
% 35.23/4.98  --trig_cnt_out_tolerance                1.
% 35.23/4.98  --trig_cnt_out_sk_spl                   false
% 35.23/4.98  --abstr_cl_out                          false
% 35.23/4.98  
% 35.23/4.98  ------ Global Options
% 35.23/4.98  
% 35.23/4.98  --schedule                              default
% 35.23/4.98  --add_important_lit                     false
% 35.23/4.98  --prop_solver_per_cl                    1000
% 35.23/4.98  --min_unsat_core                        false
% 35.23/4.98  --soft_assumptions                      false
% 35.23/4.98  --soft_lemma_size                       3
% 35.23/4.98  --prop_impl_unit_size                   0
% 35.23/4.98  --prop_impl_unit                        []
% 35.23/4.98  --share_sel_clauses                     true
% 35.23/4.98  --reset_solvers                         false
% 35.23/4.98  --bc_imp_inh                            [conj_cone]
% 35.23/4.98  --conj_cone_tolerance                   3.
% 35.23/4.98  --extra_neg_conj                        none
% 35.23/4.98  --large_theory_mode                     true
% 35.23/4.98  --prolific_symb_bound                   200
% 35.23/4.98  --lt_threshold                          2000
% 35.23/4.98  --clause_weak_htbl                      true
% 35.23/4.98  --gc_record_bc_elim                     false
% 35.23/4.98  
% 35.23/4.98  ------ Preprocessing Options
% 35.23/4.98  
% 35.23/4.98  --preprocessing_flag                    true
% 35.23/4.98  --time_out_prep_mult                    0.1
% 35.23/4.98  --splitting_mode                        input
% 35.23/4.98  --splitting_grd                         true
% 35.23/4.98  --splitting_cvd                         false
% 35.23/4.98  --splitting_cvd_svl                     false
% 35.23/4.98  --splitting_nvd                         32
% 35.23/4.98  --sub_typing                            true
% 35.23/4.98  --prep_gs_sim                           true
% 35.23/4.98  --prep_unflatten                        true
% 35.23/4.98  --prep_res_sim                          true
% 35.23/4.98  --prep_upred                            true
% 35.23/4.98  --prep_sem_filter                       exhaustive
% 35.23/4.98  --prep_sem_filter_out                   false
% 35.23/4.98  --pred_elim                             true
% 35.23/4.98  --res_sim_input                         true
% 35.23/4.98  --eq_ax_congr_red                       true
% 35.23/4.98  --pure_diseq_elim                       true
% 35.23/4.98  --brand_transform                       false
% 35.23/4.98  --non_eq_to_eq                          false
% 35.23/4.98  --prep_def_merge                        true
% 35.23/4.98  --prep_def_merge_prop_impl              false
% 35.23/4.98  --prep_def_merge_mbd                    true
% 35.23/4.98  --prep_def_merge_tr_red                 false
% 35.23/4.98  --prep_def_merge_tr_cl                  false
% 35.23/4.98  --smt_preprocessing                     true
% 35.23/4.98  --smt_ac_axioms                         fast
% 35.23/4.98  --preprocessed_out                      false
% 35.23/4.98  --preprocessed_stats                    false
% 35.23/4.98  
% 35.23/4.98  ------ Abstraction refinement Options
% 35.23/4.98  
% 35.23/4.98  --abstr_ref                             []
% 35.23/4.98  --abstr_ref_prep                        false
% 35.23/4.98  --abstr_ref_until_sat                   false
% 35.23/4.98  --abstr_ref_sig_restrict                funpre
% 35.23/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.23/4.98  --abstr_ref_under                       []
% 35.23/4.98  
% 35.23/4.98  ------ SAT Options
% 35.23/4.98  
% 35.23/4.98  --sat_mode                              false
% 35.23/4.98  --sat_fm_restart_options                ""
% 35.23/4.98  --sat_gr_def                            false
% 35.23/4.98  --sat_epr_types                         true
% 35.23/4.98  --sat_non_cyclic_types                  false
% 35.23/4.98  --sat_finite_models                     false
% 35.23/4.98  --sat_fm_lemmas                         false
% 35.23/4.98  --sat_fm_prep                           false
% 35.23/4.98  --sat_fm_uc_incr                        true
% 35.23/4.98  --sat_out_model                         small
% 35.23/4.98  --sat_out_clauses                       false
% 35.23/4.98  
% 35.23/4.98  ------ QBF Options
% 35.23/4.98  
% 35.23/4.98  --qbf_mode                              false
% 35.23/4.98  --qbf_elim_univ                         false
% 35.23/4.98  --qbf_dom_inst                          none
% 35.23/4.98  --qbf_dom_pre_inst                      false
% 35.23/4.98  --qbf_sk_in                             false
% 35.23/4.98  --qbf_pred_elim                         true
% 35.23/4.98  --qbf_split                             512
% 35.23/4.98  
% 35.23/4.98  ------ BMC1 Options
% 35.23/4.98  
% 35.23/4.98  --bmc1_incremental                      false
% 35.23/4.98  --bmc1_axioms                           reachable_all
% 35.23/4.98  --bmc1_min_bound                        0
% 35.23/4.98  --bmc1_max_bound                        -1
% 35.23/4.98  --bmc1_max_bound_default                -1
% 35.23/4.98  --bmc1_symbol_reachability              true
% 35.23/4.98  --bmc1_property_lemmas                  false
% 35.23/4.98  --bmc1_k_induction                      false
% 35.23/4.98  --bmc1_non_equiv_states                 false
% 35.23/4.98  --bmc1_deadlock                         false
% 35.23/4.98  --bmc1_ucm                              false
% 35.23/4.98  --bmc1_add_unsat_core                   none
% 35.23/4.98  --bmc1_unsat_core_children              false
% 35.23/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.23/4.98  --bmc1_out_stat                         full
% 35.23/4.98  --bmc1_ground_init                      false
% 35.23/4.98  --bmc1_pre_inst_next_state              false
% 35.23/4.98  --bmc1_pre_inst_state                   false
% 35.23/4.98  --bmc1_pre_inst_reach_state             false
% 35.23/4.98  --bmc1_out_unsat_core                   false
% 35.23/4.98  --bmc1_aig_witness_out                  false
% 35.23/4.98  --bmc1_verbose                          false
% 35.23/4.98  --bmc1_dump_clauses_tptp                false
% 35.23/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.23/4.98  --bmc1_dump_file                        -
% 35.23/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.23/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.23/4.98  --bmc1_ucm_extend_mode                  1
% 35.23/4.98  --bmc1_ucm_init_mode                    2
% 35.23/4.98  --bmc1_ucm_cone_mode                    none
% 35.23/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.23/4.98  --bmc1_ucm_relax_model                  4
% 35.23/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.23/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.23/4.98  --bmc1_ucm_layered_model                none
% 35.23/4.98  --bmc1_ucm_max_lemma_size               10
% 35.23/4.98  
% 35.23/4.98  ------ AIG Options
% 35.23/4.98  
% 35.23/4.98  --aig_mode                              false
% 35.23/4.98  
% 35.23/4.98  ------ Instantiation Options
% 35.23/4.98  
% 35.23/4.98  --instantiation_flag                    true
% 35.23/4.98  --inst_sos_flag                         true
% 35.23/4.98  --inst_sos_phase                        true
% 35.23/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.23/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.23/4.98  --inst_lit_sel_side                     none
% 35.23/4.98  --inst_solver_per_active                1400
% 35.23/4.98  --inst_solver_calls_frac                1.
% 35.23/4.98  --inst_passive_queue_type               priority_queues
% 35.23/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.23/4.98  --inst_passive_queues_freq              [25;2]
% 35.23/4.98  --inst_dismatching                      true
% 35.23/4.98  --inst_eager_unprocessed_to_passive     true
% 35.23/4.98  --inst_prop_sim_given                   true
% 35.23/4.98  --inst_prop_sim_new                     false
% 35.23/4.98  --inst_subs_new                         false
% 35.23/4.98  --inst_eq_res_simp                      false
% 35.23/4.98  --inst_subs_given                       false
% 35.23/4.98  --inst_orphan_elimination               true
% 35.23/4.98  --inst_learning_loop_flag               true
% 35.23/4.98  --inst_learning_start                   3000
% 35.23/4.98  --inst_learning_factor                  2
% 35.23/4.98  --inst_start_prop_sim_after_learn       3
% 35.23/4.98  --inst_sel_renew                        solver
% 35.23/4.98  --inst_lit_activity_flag                true
% 35.23/4.98  --inst_restr_to_given                   false
% 35.23/4.98  --inst_activity_threshold               500
% 35.23/4.98  --inst_out_proof                        true
% 35.23/4.98  
% 35.23/4.98  ------ Resolution Options
% 35.23/4.98  
% 35.23/4.98  --resolution_flag                       false
% 35.23/4.98  --res_lit_sel                           adaptive
% 35.23/4.98  --res_lit_sel_side                      none
% 35.23/4.98  --res_ordering                          kbo
% 35.23/4.98  --res_to_prop_solver                    active
% 35.23/4.98  --res_prop_simpl_new                    false
% 35.23/4.98  --res_prop_simpl_given                  true
% 35.23/4.98  --res_passive_queue_type                priority_queues
% 35.23/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.23/4.98  --res_passive_queues_freq               [15;5]
% 35.23/4.98  --res_forward_subs                      full
% 35.23/4.98  --res_backward_subs                     full
% 35.23/4.98  --res_forward_subs_resolution           true
% 35.23/4.98  --res_backward_subs_resolution          true
% 35.23/4.98  --res_orphan_elimination                true
% 35.23/4.98  --res_time_limit                        2.
% 35.23/4.98  --res_out_proof                         true
% 35.23/4.98  
% 35.23/4.98  ------ Superposition Options
% 35.23/4.98  
% 35.23/4.98  --superposition_flag                    true
% 35.23/4.98  --sup_passive_queue_type                priority_queues
% 35.23/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.23/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.23/4.98  --demod_completeness_check              fast
% 35.23/4.98  --demod_use_ground                      true
% 35.23/4.98  --sup_to_prop_solver                    passive
% 35.23/4.98  --sup_prop_simpl_new                    true
% 35.23/4.98  --sup_prop_simpl_given                  true
% 35.23/4.98  --sup_fun_splitting                     true
% 35.23/4.98  --sup_smt_interval                      50000
% 35.23/4.98  
% 35.23/4.98  ------ Superposition Simplification Setup
% 35.23/4.98  
% 35.23/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.23/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.23/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.23/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.23/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.23/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.23/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.23/4.98  --sup_immed_triv                        [TrivRules]
% 35.23/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.23/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.23/4.98  --sup_immed_bw_main                     []
% 35.23/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.23/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.23/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.23/4.98  --sup_input_bw                          []
% 35.23/4.98  
% 35.23/4.98  ------ Combination Options
% 35.23/4.98  
% 35.23/4.98  --comb_res_mult                         3
% 35.23/4.98  --comb_sup_mult                         2
% 35.23/4.98  --comb_inst_mult                        10
% 35.23/4.98  
% 35.23/4.98  ------ Debug Options
% 35.23/4.98  
% 35.23/4.98  --dbg_backtrace                         false
% 35.23/4.98  --dbg_dump_prop_clauses                 false
% 35.23/4.98  --dbg_dump_prop_clauses_file            -
% 35.23/4.98  --dbg_out_stat                          false
% 35.23/4.98  
% 35.23/4.98  
% 35.23/4.98  
% 35.23/4.98  
% 35.23/4.98  ------ Proving...
% 35.23/4.98  
% 35.23/4.98  
% 35.23/4.98  % SZS status Theorem for theBenchmark.p
% 35.23/4.98  
% 35.23/4.98   Resolution empty clause
% 35.23/4.98  
% 35.23/4.98  % SZS output start CNFRefutation for theBenchmark.p
% 35.23/4.98  
% 35.23/4.98  fof(f14,axiom,(
% 35.23/4.98    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f17,plain,(
% 35.23/4.98    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 35.23/4.98    inference(ennf_transformation,[],[f14])).
% 35.23/4.98  
% 35.23/4.98  fof(f34,plain,(
% 35.23/4.98    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 35.23/4.98    inference(cnf_transformation,[],[f17])).
% 35.23/4.98  
% 35.23/4.98  fof(f1,axiom,(
% 35.23/4.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f21,plain,(
% 35.23/4.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.23/4.98    inference(cnf_transformation,[],[f1])).
% 35.23/4.98  
% 35.23/4.98  fof(f6,axiom,(
% 35.23/4.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f26,plain,(
% 35.23/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 35.23/4.98    inference(cnf_transformation,[],[f6])).
% 35.23/4.98  
% 35.23/4.98  fof(f38,plain,(
% 35.23/4.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 35.23/4.98    inference(definition_unfolding,[],[f21,f26])).
% 35.23/4.98  
% 35.23/4.98  fof(f8,axiom,(
% 35.23/4.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f28,plain,(
% 35.23/4.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 35.23/4.98    inference(cnf_transformation,[],[f8])).
% 35.23/4.98  
% 35.23/4.98  fof(f9,axiom,(
% 35.23/4.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f29,plain,(
% 35.23/4.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.23/4.98    inference(cnf_transformation,[],[f9])).
% 35.23/4.98  
% 35.23/4.98  fof(f10,axiom,(
% 35.23/4.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f30,plain,(
% 35.23/4.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.23/4.98    inference(cnf_transformation,[],[f10])).
% 35.23/4.98  
% 35.23/4.98  fof(f11,axiom,(
% 35.23/4.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f31,plain,(
% 35.23/4.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 35.23/4.98    inference(cnf_transformation,[],[f11])).
% 35.23/4.98  
% 35.23/4.98  fof(f12,axiom,(
% 35.23/4.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f32,plain,(
% 35.23/4.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 35.23/4.98    inference(cnf_transformation,[],[f12])).
% 35.23/4.98  
% 35.23/4.98  fof(f13,axiom,(
% 35.23/4.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f33,plain,(
% 35.23/4.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 35.23/4.98    inference(cnf_transformation,[],[f13])).
% 35.23/4.98  
% 35.23/4.98  fof(f39,plain,(
% 35.23/4.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 35.23/4.98    inference(definition_unfolding,[],[f32,f33])).
% 35.23/4.98  
% 35.23/4.98  fof(f40,plain,(
% 35.23/4.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 35.23/4.98    inference(definition_unfolding,[],[f31,f39])).
% 35.23/4.98  
% 35.23/4.98  fof(f41,plain,(
% 35.23/4.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 35.23/4.98    inference(definition_unfolding,[],[f30,f40])).
% 35.23/4.98  
% 35.23/4.98  fof(f42,plain,(
% 35.23/4.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 35.23/4.98    inference(definition_unfolding,[],[f29,f41])).
% 35.23/4.98  
% 35.23/4.98  fof(f43,plain,(
% 35.23/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 35.23/4.98    inference(definition_unfolding,[],[f28,f42])).
% 35.23/4.98  
% 35.23/4.98  fof(f46,plain,(
% 35.23/4.98    ( ! [X2,X0,X1] : (k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k2_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 35.23/4.98    inference(definition_unfolding,[],[f34,f38,f43])).
% 35.23/4.98  
% 35.23/4.98  fof(f15,conjecture,(
% 35.23/4.98    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 35.23/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.98  
% 35.23/4.98  fof(f16,negated_conjecture,(
% 35.23/4.98    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 35.23/4.98    inference(negated_conjecture,[],[f15])).
% 35.23/4.98  
% 35.23/4.98  fof(f18,plain,(
% 35.23/4.98    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 35.23/4.98    inference(ennf_transformation,[],[f16])).
% 35.23/4.98  
% 35.23/4.98  fof(f19,plain,(
% 35.23/4.98    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 35.23/4.98    introduced(choice_axiom,[])).
% 35.23/4.98  
% 35.23/4.98  fof(f20,plain,(
% 35.23/4.98    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 35.23/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 35.23/4.98  
% 35.23/4.98  fof(f36,plain,(
% 35.23/4.98    ~r2_hidden(sK1,sK2)),
% 35.23/4.99    inference(cnf_transformation,[],[f20])).
% 35.23/4.99  
% 35.23/4.99  fof(f35,plain,(
% 35.23/4.99    ~r2_hidden(sK0,sK2)),
% 35.23/4.99    inference(cnf_transformation,[],[f20])).
% 35.23/4.99  
% 35.23/4.99  fof(f7,axiom,(
% 35.23/4.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 35.23/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.99  
% 35.23/4.99  fof(f27,plain,(
% 35.23/4.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 35.23/4.99    inference(cnf_transformation,[],[f7])).
% 35.23/4.99  
% 35.23/4.99  fof(f44,plain,(
% 35.23/4.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 35.23/4.99    inference(definition_unfolding,[],[f27,f38])).
% 35.23/4.99  
% 35.23/4.99  fof(f3,axiom,(
% 35.23/4.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 35.23/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.99  
% 35.23/4.99  fof(f23,plain,(
% 35.23/4.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.23/4.99    inference(cnf_transformation,[],[f3])).
% 35.23/4.99  
% 35.23/4.99  fof(f5,axiom,(
% 35.23/4.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 35.23/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.99  
% 35.23/4.99  fof(f25,plain,(
% 35.23/4.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 35.23/4.99    inference(cnf_transformation,[],[f5])).
% 35.23/4.99  
% 35.23/4.99  fof(f4,axiom,(
% 35.23/4.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 35.23/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.99  
% 35.23/4.99  fof(f24,plain,(
% 35.23/4.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 35.23/4.99    inference(cnf_transformation,[],[f4])).
% 35.23/4.99  
% 35.23/4.99  fof(f2,axiom,(
% 35.23/4.99    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 35.23/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/4.99  
% 35.23/4.99  fof(f22,plain,(
% 35.23/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 35.23/4.99    inference(cnf_transformation,[],[f2])).
% 35.23/4.99  
% 35.23/4.99  fof(f45,plain,(
% 35.23/4.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 35.23/4.99    inference(definition_unfolding,[],[f22,f26])).
% 35.23/4.99  
% 35.23/4.99  fof(f37,plain,(
% 35.23/4.99    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2),
% 35.23/4.99    inference(cnf_transformation,[],[f20])).
% 35.23/4.99  
% 35.23/4.99  fof(f47,plain,(
% 35.23/4.99    k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != sK2),
% 35.23/4.99    inference(definition_unfolding,[],[f37,f38,f43,f43])).
% 35.23/4.99  
% 35.23/4.99  cnf(c_5,plain,
% 35.23/4.99      ( r2_hidden(X0,X1)
% 35.23/4.99      | r2_hidden(X2,X1)
% 35.23/4.99      | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k2_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))) = X1 ),
% 35.23/4.99      inference(cnf_transformation,[],[f46]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_115,plain,
% 35.23/4.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k2_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = X0
% 35.23/4.99      | r2_hidden(X1,X0) = iProver_top
% 35.23/4.99      | r2_hidden(X2,X0) = iProver_top ),
% 35.23/4.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_7,negated_conjecture,
% 35.23/4.99      ( ~ r2_hidden(sK1,sK2) ),
% 35.23/4.99      inference(cnf_transformation,[],[f36]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_114,plain,
% 35.23/4.99      ( r2_hidden(sK1,sK2) != iProver_top ),
% 35.23/4.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_342,plain,
% 35.23/4.99      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)),k2_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))) = sK2
% 35.23/4.99      | r2_hidden(X0,sK2) = iProver_top ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_115,c_114]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_8,negated_conjecture,
% 35.23/4.99      ( ~ r2_hidden(sK0,sK2) ),
% 35.23/4.99      inference(cnf_transformation,[],[f35]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_113,plain,
% 35.23/4.99      ( r2_hidden(sK0,sK2) != iProver_top ),
% 35.23/4.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_579,plain,
% 35.23/4.99      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) = sK2 ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_342,c_113]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_0,plain,
% 35.23/4.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
% 35.23/4.99      inference(cnf_transformation,[],[f44]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_640,plain,
% 35.23/4.99      ( k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_579,c_0]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_1137,plain,
% 35.23/4.99      ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))) = k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_640,c_0]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_2,plain,
% 35.23/4.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.23/4.99      inference(cnf_transformation,[],[f23]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_4,plain,
% 35.23/4.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 35.23/4.99      inference(cnf_transformation,[],[f25]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_1143,plain,
% 35.23/4.99      ( k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_1137,c_2,c_4]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_408,plain,
% 35.23/4.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))))) = k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),X1) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_17562,plain,
% 35.23/4.99      ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))))) = k2_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_1143,c_408]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_17710,plain,
% 35.23/4.99      ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))))) = k2_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 35.23/4.99      inference(light_normalisation,[status(thm)],[c_17562,c_640,c_1143]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_3,plain,
% 35.23/4.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.23/4.99      inference(cnf_transformation,[],[f24]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_256,plain,
% 35.23/4.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_553,plain,
% 35.23/4.99      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_4,c_256]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_571,plain,
% 35.23/4.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 35.23/4.99      inference(light_normalisation,[status(thm)],[c_553,c_2]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_572,plain,
% 35.23/4.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_571,c_256]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_1,plain,
% 35.23/4.99      ( k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 35.23/4.99      inference(cnf_transformation,[],[f45]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_360,plain,
% 35.23/4.99      ( k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k5_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,X2) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_3974,plain,
% 35.23/4.99      ( k5_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_4,c_360]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_4058,plain,
% 35.23/4.99      ( k5_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k5_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_3974,c_2]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_14615,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_640,c_4058]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_3986,plain,
% 35.23/4.99      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),k5_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_640,c_360]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_4048,plain,
% 35.23/4.99      ( k5_xboole_0(sK2,k5_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0) ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_3986,c_572]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_7408,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = k5_xboole_0(sK2,k1_xboole_0) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_4,c_4048]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_7476,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = sK2 ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_7408,c_2]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_14715,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) = sK2 ),
% 35.23/4.99      inference(light_normalisation,[status(thm)],[c_14615,c_640,c_7476]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_16256,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),X0)) = k5_xboole_0(sK2,X0) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_14715,c_3]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_17711,plain,
% 35.23/4.99      ( k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 35.23/4.99      inference(demodulation,
% 35.23/4.99                [status(thm)],
% 35.23/4.99                [c_17710,c_2,c_4,c_572,c_1143,c_16256]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_17712,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_17711,c_2,c_4,c_640]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_400,plain,
% 35.23/4.99      ( k5_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_417,plain,
% 35.23/4.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 35.23/4.99      inference(light_normalisation,[status(thm)],[c_400,c_4]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_418,plain,
% 35.23/4.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_417,c_2]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_1138,plain,
% 35.23/4.99      ( k2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
% 35.23/4.99      inference(superposition,[status(thm)],[c_640,c_418]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_1142,plain,
% 35.23/4.99      ( k2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_1138,c_640]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_20647,plain,
% 35.23/4.99      ( k2_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_17712,c_1142]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_6,negated_conjecture,
% 35.23/4.99      ( k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != sK2 ),
% 35.23/4.99      inference(cnf_transformation,[],[f47]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_252,plain,
% 35.23/4.99      ( k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != sK2 ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_3,c_6]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_287,plain,
% 35.23/4.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != sK2 ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_252,c_256]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_1003,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != sK2 ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_571,c_287]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_2293,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != sK2 ),
% 35.23/4.99      inference(light_normalisation,[status(thm)],[c_1003,c_1143]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_97526,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != sK2 ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_20647,c_2293]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_20641,plain,
% 35.23/4.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 35.23/4.99      inference(demodulation,[status(thm)],[c_17712,c_14715]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_97527,plain,
% 35.23/4.99      ( sK2 != sK2 ),
% 35.23/4.99      inference(light_normalisation,[status(thm)],[c_97526,c_20641]) ).
% 35.23/4.99  
% 35.23/4.99  cnf(c_97528,plain,
% 35.23/4.99      ( $false ),
% 35.23/4.99      inference(equality_resolution_simp,[status(thm)],[c_97527]) ).
% 35.23/4.99  
% 35.23/4.99  
% 35.23/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.23/4.99  
% 35.23/4.99  ------                               Statistics
% 35.23/4.99  
% 35.23/4.99  ------ General
% 35.23/4.99  
% 35.23/4.99  abstr_ref_over_cycles:                  0
% 35.23/4.99  abstr_ref_under_cycles:                 0
% 35.23/4.99  gc_basic_clause_elim:                   0
% 35.23/4.99  forced_gc_time:                         0
% 35.23/4.99  parsing_time:                           0.008
% 35.23/4.99  unif_index_cands_time:                  0.
% 35.23/4.99  unif_index_add_time:                    0.
% 35.23/4.99  orderings_time:                         0.
% 35.23/4.99  out_proof_time:                         0.012
% 35.23/4.99  total_time:                             4.412
% 35.23/4.99  num_of_symbols:                         41
% 35.23/4.99  num_of_terms:                           200106
% 35.23/4.99  
% 35.23/4.99  ------ Preprocessing
% 35.23/4.99  
% 35.23/4.99  num_of_splits:                          0
% 35.23/4.99  num_of_split_atoms:                     2
% 35.23/4.99  num_of_reused_defs:                     0
% 35.23/4.99  num_eq_ax_congr_red:                    0
% 35.23/4.99  num_of_sem_filtered_clauses:            1
% 35.23/4.99  num_of_subtypes:                        0
% 35.23/4.99  monotx_restored_types:                  0
% 35.23/4.99  sat_num_of_epr_types:                   0
% 35.23/4.99  sat_num_of_non_cyclic_types:            0
% 35.23/4.99  sat_guarded_non_collapsed_types:        0
% 35.23/4.99  num_pure_diseq_elim:                    0
% 35.23/4.99  simp_replaced_by:                       0
% 35.23/4.99  res_preprocessed:                       40
% 35.23/4.99  prep_upred:                             0
% 35.23/4.99  prep_unflattend:                        0
% 35.23/4.99  smt_new_axioms:                         0
% 35.23/4.99  pred_elim_cands:                        1
% 35.23/4.99  pred_elim:                              0
% 35.23/4.99  pred_elim_cl:                           0
% 35.23/4.99  pred_elim_cycles:                       1
% 35.23/4.99  merged_defs:                            0
% 35.23/4.99  merged_defs_ncl:                        0
% 35.23/4.99  bin_hyper_res:                          0
% 35.23/4.99  prep_cycles:                            3
% 35.23/4.99  pred_elim_time:                         0.
% 35.23/4.99  splitting_time:                         0.
% 35.23/4.99  sem_filter_time:                        0.
% 35.23/4.99  monotx_time:                            0.
% 35.23/4.99  subtype_inf_time:                       0.
% 35.23/4.99  
% 35.23/4.99  ------ Problem properties
% 35.23/4.99  
% 35.23/4.99  clauses:                                9
% 35.23/4.99  conjectures:                            3
% 35.23/4.99  epr:                                    2
% 35.23/4.99  horn:                                   8
% 35.23/4.99  ground:                                 3
% 35.23/4.99  unary:                                  8
% 35.23/4.99  binary:                                 0
% 35.23/4.99  lits:                                   11
% 35.23/4.99  lits_eq:                                7
% 35.23/4.99  fd_pure:                                0
% 35.23/4.99  fd_pseudo:                              0
% 35.23/4.99  fd_cond:                                0
% 35.23/4.99  fd_pseudo_cond:                         0
% 35.23/4.99  ac_symbols:                             1
% 35.23/4.99  
% 35.23/4.99  ------ Propositional Solver
% 35.23/4.99  
% 35.23/4.99  prop_solver_calls:                      30
% 35.23/4.99  prop_fast_solver_calls:                 812
% 35.23/4.99  smt_solver_calls:                       0
% 35.23/4.99  smt_fast_solver_calls:                  0
% 35.23/4.99  prop_num_of_clauses:                    21827
% 35.23/4.99  prop_preprocess_simplified:             16614
% 35.23/4.99  prop_fo_subsumed:                       0
% 35.23/4.99  prop_solver_time:                       0.
% 35.23/4.99  smt_solver_time:                        0.
% 35.23/4.99  smt_fast_solver_time:                   0.
% 35.23/4.99  prop_fast_solver_time:                  0.
% 35.23/4.99  prop_unsat_core_time:                   0.
% 35.23/4.99  
% 35.23/4.99  ------ QBF
% 35.23/4.99  
% 35.23/4.99  qbf_q_res:                              0
% 35.23/4.99  qbf_num_tautologies:                    0
% 35.23/4.99  qbf_prep_cycles:                        0
% 35.23/4.99  
% 35.23/4.99  ------ BMC1
% 35.23/4.99  
% 35.23/4.99  bmc1_current_bound:                     -1
% 35.23/4.99  bmc1_last_solved_bound:                 -1
% 35.23/4.99  bmc1_unsat_core_size:                   -1
% 35.23/4.99  bmc1_unsat_core_parents_size:           -1
% 35.23/4.99  bmc1_merge_next_fun:                    0
% 35.23/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.23/4.99  
% 35.23/4.99  ------ Instantiation
% 35.23/4.99  
% 35.23/4.99  inst_num_of_clauses:                    3237
% 35.23/4.99  inst_num_in_passive:                    489
% 35.23/4.99  inst_num_in_active:                     1162
% 35.23/4.99  inst_num_in_unprocessed:                1586
% 35.23/4.99  inst_num_of_loops:                      1280
% 35.23/4.99  inst_num_of_learning_restarts:          0
% 35.23/4.99  inst_num_moves_active_passive:          113
% 35.23/4.99  inst_lit_activity:                      0
% 35.23/4.99  inst_lit_activity_moves:                0
% 35.23/4.99  inst_num_tautologies:                   0
% 35.23/4.99  inst_num_prop_implied:                  0
% 35.23/4.99  inst_num_existing_simplified:           0
% 35.23/4.99  inst_num_eq_res_simplified:             0
% 35.23/4.99  inst_num_child_elim:                    0
% 35.23/4.99  inst_num_of_dismatching_blockings:      2126
% 35.23/4.99  inst_num_of_non_proper_insts:           3701
% 35.23/4.99  inst_num_of_duplicates:                 0
% 35.23/4.99  inst_inst_num_from_inst_to_res:         0
% 35.23/4.99  inst_dismatching_checking_time:         0.
% 35.23/4.99  
% 35.23/4.99  ------ Resolution
% 35.23/4.99  
% 35.23/4.99  res_num_of_clauses:                     0
% 35.23/4.99  res_num_in_passive:                     0
% 35.23/4.99  res_num_in_active:                      0
% 35.23/4.99  res_num_of_loops:                       43
% 35.23/4.99  res_forward_subset_subsumed:            559
% 35.23/4.99  res_backward_subset_subsumed:           2
% 35.23/4.99  res_forward_subsumed:                   0
% 35.23/4.99  res_backward_subsumed:                  0
% 35.23/4.99  res_forward_subsumption_resolution:     0
% 35.23/4.99  res_backward_subsumption_resolution:    0
% 35.23/4.99  res_clause_to_clause_subsumption:       204835
% 35.23/4.99  res_orphan_elimination:                 0
% 35.23/4.99  res_tautology_del:                      121
% 35.23/4.99  res_num_eq_res_simplified:              0
% 35.23/4.99  res_num_sel_changes:                    0
% 35.23/4.99  res_moves_from_active_to_pass:          0
% 35.23/4.99  
% 35.23/4.99  ------ Superposition
% 35.23/4.99  
% 35.23/4.99  sup_time_total:                         0.
% 35.23/4.99  sup_time_generating:                    0.
% 35.23/4.99  sup_time_sim_full:                      0.
% 35.23/4.99  sup_time_sim_immed:                     0.
% 35.23/4.99  
% 35.23/4.99  sup_num_of_clauses:                     7795
% 35.23/4.99  sup_num_in_active:                      168
% 35.23/4.99  sup_num_in_passive:                     7627
% 35.23/4.99  sup_num_of_loops:                       254
% 35.23/4.99  sup_fw_superposition:                   16911
% 35.23/4.99  sup_bw_superposition:                   22695
% 35.23/4.99  sup_immediate_simplified:               25965
% 35.23/4.99  sup_given_eliminated:                   10
% 35.23/4.99  comparisons_done:                       0
% 35.23/4.99  comparisons_avoided:                    0
% 35.23/4.99  
% 35.23/4.99  ------ Simplifications
% 35.23/4.99  
% 35.23/4.99  
% 35.23/4.99  sim_fw_subset_subsumed:                 0
% 35.23/4.99  sim_bw_subset_subsumed:                 0
% 35.23/4.99  sim_fw_subsumed:                        1583
% 35.23/4.99  sim_bw_subsumed:                        210
% 35.23/4.99  sim_fw_subsumption_res:                 0
% 35.23/4.99  sim_bw_subsumption_res:                 0
% 35.23/4.99  sim_tautology_del:                      0
% 35.23/4.99  sim_eq_tautology_del:                   11039
% 35.23/4.99  sim_eq_res_simp:                        1
% 35.23/4.99  sim_fw_demodulated:                     25614
% 35.23/4.99  sim_bw_demodulated:                     517
% 35.23/4.99  sim_light_normalised:                   9339
% 35.23/4.99  sim_joinable_taut:                      207
% 35.23/4.99  sim_joinable_simp:                      0
% 35.23/4.99  sim_ac_normalised:                      0
% 35.23/4.99  sim_smt_subsumption:                    0
% 35.23/4.99  
%------------------------------------------------------------------------------
