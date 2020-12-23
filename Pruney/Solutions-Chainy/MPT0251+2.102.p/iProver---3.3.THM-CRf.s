%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:19 EST 2020

% Result     : Theorem 51.28s
% Output     : CNFRefutation 51.28s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 662 expanded)
%              Number of clauses        :   43 ( 141 expanded)
%              Number of leaves         :   24 ( 197 expanded)
%              Depth                    :   19
%              Number of atoms          :  157 ( 834 expanded)
%              Number of equality atoms :   98 ( 599 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f33])).

fof(f57,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f59,f64])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f43,f39,f59])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f30])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(definition_unfolding,[],[f58,f59,f65])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_510,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_512,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_513,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2980,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_513])).

cnf(c_102997,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_510,c_2980])).

cnf(c_12,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_103363,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_102997,c_12])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_515,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_4])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_514,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_154,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_155,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_154])).

cnf(c_508,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_2278,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_514,c_508])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2459,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_2278,c_6])).

cnf(c_103444,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_103363,c_515,c_2459])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_822,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_809,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_515])).

cnf(c_2466,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2278,c_12])).

cnf(c_820,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_6,c_12])).

cnf(c_1319,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_515,c_809])).

cnf(c_804,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_515,c_9])).

cnf(c_1733,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1319,c_804])).

cnf(c_2476,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2466,c_820,c_1733,c_2459])).

cnf(c_2735,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_2476,c_804])).

cnf(c_2824,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_809,c_2735])).

cnf(c_2836,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2824,c_2459])).

cnf(c_2850,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2836,c_2735])).

cnf(c_2855,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_2850])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5206,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(demodulation,[status(thm)],[c_2855,c_13])).

cnf(c_14771,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != sK3 ),
    inference(demodulation,[status(thm)],[c_822,c_5206])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_103444,c_14771])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:26:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.28/6.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.28/6.99  
% 51.28/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.28/6.99  
% 51.28/6.99  ------  iProver source info
% 51.28/6.99  
% 51.28/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.28/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.28/6.99  git: non_committed_changes: false
% 51.28/6.99  git: last_make_outside_of_git: false
% 51.28/6.99  
% 51.28/6.99  ------ 
% 51.28/6.99  
% 51.28/6.99  ------ Input Options
% 51.28/6.99  
% 51.28/6.99  --out_options                           all
% 51.28/6.99  --tptp_safe_out                         true
% 51.28/6.99  --problem_path                          ""
% 51.28/6.99  --include_path                          ""
% 51.28/6.99  --clausifier                            res/vclausify_rel
% 51.28/6.99  --clausifier_options                    ""
% 51.28/6.99  --stdin                                 false
% 51.28/6.99  --stats_out                             all
% 51.28/6.99  
% 51.28/6.99  ------ General Options
% 51.28/6.99  
% 51.28/6.99  --fof                                   false
% 51.28/6.99  --time_out_real                         305.
% 51.28/6.99  --time_out_virtual                      -1.
% 51.28/6.99  --symbol_type_check                     false
% 51.28/6.99  --clausify_out                          false
% 51.28/6.99  --sig_cnt_out                           false
% 51.28/6.99  --trig_cnt_out                          false
% 51.28/6.99  --trig_cnt_out_tolerance                1.
% 51.28/6.99  --trig_cnt_out_sk_spl                   false
% 51.28/6.99  --abstr_cl_out                          false
% 51.28/6.99  
% 51.28/6.99  ------ Global Options
% 51.28/6.99  
% 51.28/6.99  --schedule                              default
% 51.28/6.99  --add_important_lit                     false
% 51.28/6.99  --prop_solver_per_cl                    1000
% 51.28/6.99  --min_unsat_core                        false
% 51.28/6.99  --soft_assumptions                      false
% 51.28/6.99  --soft_lemma_size                       3
% 51.28/6.99  --prop_impl_unit_size                   0
% 51.28/6.99  --prop_impl_unit                        []
% 51.28/6.99  --share_sel_clauses                     true
% 51.28/6.99  --reset_solvers                         false
% 51.28/6.99  --bc_imp_inh                            [conj_cone]
% 51.28/6.99  --conj_cone_tolerance                   3.
% 51.28/6.99  --extra_neg_conj                        none
% 51.28/6.99  --large_theory_mode                     true
% 51.28/6.99  --prolific_symb_bound                   200
% 51.28/6.99  --lt_threshold                          2000
% 51.28/6.99  --clause_weak_htbl                      true
% 51.28/6.99  --gc_record_bc_elim                     false
% 51.28/6.99  
% 51.28/6.99  ------ Preprocessing Options
% 51.28/6.99  
% 51.28/6.99  --preprocessing_flag                    true
% 51.28/6.99  --time_out_prep_mult                    0.1
% 51.28/6.99  --splitting_mode                        input
% 51.28/6.99  --splitting_grd                         true
% 51.28/6.99  --splitting_cvd                         false
% 51.28/6.99  --splitting_cvd_svl                     false
% 51.28/6.99  --splitting_nvd                         32
% 51.28/6.99  --sub_typing                            true
% 51.28/6.99  --prep_gs_sim                           true
% 51.28/6.99  --prep_unflatten                        true
% 51.28/6.99  --prep_res_sim                          true
% 51.28/6.99  --prep_upred                            true
% 51.28/6.99  --prep_sem_filter                       exhaustive
% 51.28/6.99  --prep_sem_filter_out                   false
% 51.28/6.99  --pred_elim                             true
% 51.28/6.99  --res_sim_input                         true
% 51.28/6.99  --eq_ax_congr_red                       true
% 51.28/6.99  --pure_diseq_elim                       true
% 51.28/6.99  --brand_transform                       false
% 51.28/6.99  --non_eq_to_eq                          false
% 51.28/6.99  --prep_def_merge                        true
% 51.28/6.99  --prep_def_merge_prop_impl              false
% 51.28/6.99  --prep_def_merge_mbd                    true
% 51.28/6.99  --prep_def_merge_tr_red                 false
% 51.28/6.99  --prep_def_merge_tr_cl                  false
% 51.28/6.99  --smt_preprocessing                     true
% 51.28/6.99  --smt_ac_axioms                         fast
% 51.28/6.99  --preprocessed_out                      false
% 51.28/6.99  --preprocessed_stats                    false
% 51.28/6.99  
% 51.28/6.99  ------ Abstraction refinement Options
% 51.28/6.99  
% 51.28/6.99  --abstr_ref                             []
% 51.28/6.99  --abstr_ref_prep                        false
% 51.28/6.99  --abstr_ref_until_sat                   false
% 51.28/6.99  --abstr_ref_sig_restrict                funpre
% 51.28/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.28/6.99  --abstr_ref_under                       []
% 51.28/6.99  
% 51.28/6.99  ------ SAT Options
% 51.28/6.99  
% 51.28/6.99  --sat_mode                              false
% 51.28/6.99  --sat_fm_restart_options                ""
% 51.28/6.99  --sat_gr_def                            false
% 51.28/6.99  --sat_epr_types                         true
% 51.28/6.99  --sat_non_cyclic_types                  false
% 51.28/6.99  --sat_finite_models                     false
% 51.28/6.99  --sat_fm_lemmas                         false
% 51.28/6.99  --sat_fm_prep                           false
% 51.28/6.99  --sat_fm_uc_incr                        true
% 51.28/6.99  --sat_out_model                         small
% 51.28/6.99  --sat_out_clauses                       false
% 51.28/6.99  
% 51.28/6.99  ------ QBF Options
% 51.28/6.99  
% 51.28/6.99  --qbf_mode                              false
% 51.28/6.99  --qbf_elim_univ                         false
% 51.28/6.99  --qbf_dom_inst                          none
% 51.28/6.99  --qbf_dom_pre_inst                      false
% 51.28/6.99  --qbf_sk_in                             false
% 51.28/6.99  --qbf_pred_elim                         true
% 51.28/6.99  --qbf_split                             512
% 51.28/6.99  
% 51.28/6.99  ------ BMC1 Options
% 51.28/6.99  
% 51.28/6.99  --bmc1_incremental                      false
% 51.28/6.99  --bmc1_axioms                           reachable_all
% 51.28/6.99  --bmc1_min_bound                        0
% 51.28/6.99  --bmc1_max_bound                        -1
% 51.28/6.99  --bmc1_max_bound_default                -1
% 51.28/6.99  --bmc1_symbol_reachability              true
% 51.28/6.99  --bmc1_property_lemmas                  false
% 51.28/6.99  --bmc1_k_induction                      false
% 51.28/6.99  --bmc1_non_equiv_states                 false
% 51.28/6.99  --bmc1_deadlock                         false
% 51.28/6.99  --bmc1_ucm                              false
% 51.28/6.99  --bmc1_add_unsat_core                   none
% 51.28/6.99  --bmc1_unsat_core_children              false
% 51.28/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.28/6.99  --bmc1_out_stat                         full
% 51.28/6.99  --bmc1_ground_init                      false
% 51.28/6.99  --bmc1_pre_inst_next_state              false
% 51.28/6.99  --bmc1_pre_inst_state                   false
% 51.28/6.99  --bmc1_pre_inst_reach_state             false
% 51.28/6.99  --bmc1_out_unsat_core                   false
% 51.28/6.99  --bmc1_aig_witness_out                  false
% 51.28/6.99  --bmc1_verbose                          false
% 51.28/6.99  --bmc1_dump_clauses_tptp                false
% 51.28/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.28/6.99  --bmc1_dump_file                        -
% 51.28/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.28/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.28/6.99  --bmc1_ucm_extend_mode                  1
% 51.28/6.99  --bmc1_ucm_init_mode                    2
% 51.28/6.99  --bmc1_ucm_cone_mode                    none
% 51.28/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.28/6.99  --bmc1_ucm_relax_model                  4
% 51.28/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.28/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.28/6.99  --bmc1_ucm_layered_model                none
% 51.28/6.99  --bmc1_ucm_max_lemma_size               10
% 51.28/6.99  
% 51.28/6.99  ------ AIG Options
% 51.28/6.99  
% 51.28/6.99  --aig_mode                              false
% 51.28/6.99  
% 51.28/6.99  ------ Instantiation Options
% 51.28/6.99  
% 51.28/6.99  --instantiation_flag                    true
% 51.28/6.99  --inst_sos_flag                         true
% 51.28/6.99  --inst_sos_phase                        true
% 51.28/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.28/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.28/6.99  --inst_lit_sel_side                     num_symb
% 51.28/6.99  --inst_solver_per_active                1400
% 51.28/6.99  --inst_solver_calls_frac                1.
% 51.28/6.99  --inst_passive_queue_type               priority_queues
% 51.28/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.28/6.99  --inst_passive_queues_freq              [25;2]
% 51.28/6.99  --inst_dismatching                      true
% 51.28/6.99  --inst_eager_unprocessed_to_passive     true
% 51.28/6.99  --inst_prop_sim_given                   true
% 51.28/6.99  --inst_prop_sim_new                     false
% 51.28/6.99  --inst_subs_new                         false
% 51.28/6.99  --inst_eq_res_simp                      false
% 51.28/6.99  --inst_subs_given                       false
% 51.28/6.99  --inst_orphan_elimination               true
% 51.28/6.99  --inst_learning_loop_flag               true
% 51.28/6.99  --inst_learning_start                   3000
% 51.28/6.99  --inst_learning_factor                  2
% 51.28/6.99  --inst_start_prop_sim_after_learn       3
% 51.28/6.99  --inst_sel_renew                        solver
% 51.28/6.99  --inst_lit_activity_flag                true
% 51.28/6.99  --inst_restr_to_given                   false
% 51.28/6.99  --inst_activity_threshold               500
% 51.28/6.99  --inst_out_proof                        true
% 51.28/6.99  
% 51.28/6.99  ------ Resolution Options
% 51.28/6.99  
% 51.28/6.99  --resolution_flag                       true
% 51.28/6.99  --res_lit_sel                           adaptive
% 51.28/6.99  --res_lit_sel_side                      none
% 51.28/6.99  --res_ordering                          kbo
% 51.28/6.99  --res_to_prop_solver                    active
% 51.28/6.99  --res_prop_simpl_new                    false
% 51.28/6.99  --res_prop_simpl_given                  true
% 51.28/6.99  --res_passive_queue_type                priority_queues
% 51.28/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.28/6.99  --res_passive_queues_freq               [15;5]
% 51.28/6.99  --res_forward_subs                      full
% 51.28/6.99  --res_backward_subs                     full
% 51.28/6.99  --res_forward_subs_resolution           true
% 51.28/6.99  --res_backward_subs_resolution          true
% 51.28/6.99  --res_orphan_elimination                true
% 51.28/6.99  --res_time_limit                        2.
% 51.28/6.99  --res_out_proof                         true
% 51.28/6.99  
% 51.28/6.99  ------ Superposition Options
% 51.28/6.99  
% 51.28/6.99  --superposition_flag                    true
% 51.28/6.99  --sup_passive_queue_type                priority_queues
% 51.28/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.28/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.28/6.99  --demod_completeness_check              fast
% 51.28/6.99  --demod_use_ground                      true
% 51.28/6.99  --sup_to_prop_solver                    passive
% 51.28/6.99  --sup_prop_simpl_new                    true
% 51.28/6.99  --sup_prop_simpl_given                  true
% 51.28/6.99  --sup_fun_splitting                     true
% 51.28/6.99  --sup_smt_interval                      50000
% 51.28/6.99  
% 51.28/6.99  ------ Superposition Simplification Setup
% 51.28/6.99  
% 51.28/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.28/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.28/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.28/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.28/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.28/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.28/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.28/6.99  --sup_immed_triv                        [TrivRules]
% 51.28/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.28/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.28/6.99  --sup_immed_bw_main                     []
% 51.28/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.28/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.28/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.28/6.99  --sup_input_bw                          []
% 51.28/6.99  
% 51.28/6.99  ------ Combination Options
% 51.28/6.99  
% 51.28/6.99  --comb_res_mult                         3
% 51.28/6.99  --comb_sup_mult                         2
% 51.28/6.99  --comb_inst_mult                        10
% 51.28/6.99  
% 51.28/6.99  ------ Debug Options
% 51.28/6.99  
% 51.28/6.99  --dbg_backtrace                         false
% 51.28/6.99  --dbg_dump_prop_clauses                 false
% 51.28/6.99  --dbg_dump_prop_clauses_file            -
% 51.28/6.99  --dbg_out_stat                          false
% 51.28/6.99  ------ Parsing...
% 51.28/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.28/6.99  
% 51.28/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.28/6.99  
% 51.28/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.28/6.99  
% 51.28/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.28/6.99  ------ Proving...
% 51.28/6.99  ------ Problem Properties 
% 51.28/6.99  
% 51.28/6.99  
% 51.28/6.99  clauses                                 14
% 51.28/6.99  conjectures                             2
% 51.28/6.99  EPR                                     1
% 51.28/6.99  Horn                                    13
% 51.28/6.99  unary                                   9
% 51.28/6.99  binary                                  5
% 51.28/6.99  lits                                    19
% 51.28/6.99  lits eq                                 9
% 51.28/6.99  fd_pure                                 0
% 51.28/6.99  fd_pseudo                               0
% 51.28/6.99  fd_cond                                 1
% 51.28/6.99  fd_pseudo_cond                          0
% 51.28/6.99  AC symbols                              0
% 51.28/6.99  
% 51.28/6.99  ------ Schedule dynamic 5 is on 
% 51.28/6.99  
% 51.28/6.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.28/6.99  
% 51.28/6.99  
% 51.28/6.99  ------ 
% 51.28/6.99  Current options:
% 51.28/6.99  ------ 
% 51.28/6.99  
% 51.28/6.99  ------ Input Options
% 51.28/6.99  
% 51.28/6.99  --out_options                           all
% 51.28/6.99  --tptp_safe_out                         true
% 51.28/6.99  --problem_path                          ""
% 51.28/6.99  --include_path                          ""
% 51.28/6.99  --clausifier                            res/vclausify_rel
% 51.28/6.99  --clausifier_options                    ""
% 51.28/6.99  --stdin                                 false
% 51.28/6.99  --stats_out                             all
% 51.28/6.99  
% 51.28/6.99  ------ General Options
% 51.28/6.99  
% 51.28/6.99  --fof                                   false
% 51.28/6.99  --time_out_real                         305.
% 51.28/6.99  --time_out_virtual                      -1.
% 51.28/6.99  --symbol_type_check                     false
% 51.28/6.99  --clausify_out                          false
% 51.28/6.99  --sig_cnt_out                           false
% 51.28/6.99  --trig_cnt_out                          false
% 51.28/6.99  --trig_cnt_out_tolerance                1.
% 51.28/6.99  --trig_cnt_out_sk_spl                   false
% 51.28/6.99  --abstr_cl_out                          false
% 51.28/6.99  
% 51.28/6.99  ------ Global Options
% 51.28/6.99  
% 51.28/6.99  --schedule                              default
% 51.28/6.99  --add_important_lit                     false
% 51.28/6.99  --prop_solver_per_cl                    1000
% 51.28/6.99  --min_unsat_core                        false
% 51.28/6.99  --soft_assumptions                      false
% 51.28/6.99  --soft_lemma_size                       3
% 51.28/6.99  --prop_impl_unit_size                   0
% 51.28/6.99  --prop_impl_unit                        []
% 51.28/6.99  --share_sel_clauses                     true
% 51.28/6.99  --reset_solvers                         false
% 51.28/6.99  --bc_imp_inh                            [conj_cone]
% 51.28/6.99  --conj_cone_tolerance                   3.
% 51.28/6.99  --extra_neg_conj                        none
% 51.28/6.99  --large_theory_mode                     true
% 51.28/6.99  --prolific_symb_bound                   200
% 51.28/6.99  --lt_threshold                          2000
% 51.28/6.99  --clause_weak_htbl                      true
% 51.28/6.99  --gc_record_bc_elim                     false
% 51.28/6.99  
% 51.28/6.99  ------ Preprocessing Options
% 51.28/6.99  
% 51.28/6.99  --preprocessing_flag                    true
% 51.28/6.99  --time_out_prep_mult                    0.1
% 51.28/6.99  --splitting_mode                        input
% 51.28/6.99  --splitting_grd                         true
% 51.28/6.99  --splitting_cvd                         false
% 51.28/6.99  --splitting_cvd_svl                     false
% 51.28/6.99  --splitting_nvd                         32
% 51.28/6.99  --sub_typing                            true
% 51.28/6.99  --prep_gs_sim                           true
% 51.28/6.99  --prep_unflatten                        true
% 51.28/6.99  --prep_res_sim                          true
% 51.28/6.99  --prep_upred                            true
% 51.28/6.99  --prep_sem_filter                       exhaustive
% 51.28/6.99  --prep_sem_filter_out                   false
% 51.28/6.99  --pred_elim                             true
% 51.28/6.99  --res_sim_input                         true
% 51.28/6.99  --eq_ax_congr_red                       true
% 51.28/6.99  --pure_diseq_elim                       true
% 51.28/6.99  --brand_transform                       false
% 51.28/6.99  --non_eq_to_eq                          false
% 51.28/6.99  --prep_def_merge                        true
% 51.28/6.99  --prep_def_merge_prop_impl              false
% 51.28/6.99  --prep_def_merge_mbd                    true
% 51.28/6.99  --prep_def_merge_tr_red                 false
% 51.28/6.99  --prep_def_merge_tr_cl                  false
% 51.28/6.99  --smt_preprocessing                     true
% 51.28/6.99  --smt_ac_axioms                         fast
% 51.28/6.99  --preprocessed_out                      false
% 51.28/6.99  --preprocessed_stats                    false
% 51.28/6.99  
% 51.28/6.99  ------ Abstraction refinement Options
% 51.28/6.99  
% 51.28/6.99  --abstr_ref                             []
% 51.28/6.99  --abstr_ref_prep                        false
% 51.28/6.99  --abstr_ref_until_sat                   false
% 51.28/6.99  --abstr_ref_sig_restrict                funpre
% 51.28/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.28/6.99  --abstr_ref_under                       []
% 51.28/6.99  
% 51.28/6.99  ------ SAT Options
% 51.28/6.99  
% 51.28/6.99  --sat_mode                              false
% 51.28/6.99  --sat_fm_restart_options                ""
% 51.28/6.99  --sat_gr_def                            false
% 51.28/6.99  --sat_epr_types                         true
% 51.28/6.99  --sat_non_cyclic_types                  false
% 51.28/6.99  --sat_finite_models                     false
% 51.28/6.99  --sat_fm_lemmas                         false
% 51.28/6.99  --sat_fm_prep                           false
% 51.28/6.99  --sat_fm_uc_incr                        true
% 51.28/6.99  --sat_out_model                         small
% 51.28/6.99  --sat_out_clauses                       false
% 51.28/6.99  
% 51.28/6.99  ------ QBF Options
% 51.28/6.99  
% 51.28/6.99  --qbf_mode                              false
% 51.28/6.99  --qbf_elim_univ                         false
% 51.28/6.99  --qbf_dom_inst                          none
% 51.28/6.99  --qbf_dom_pre_inst                      false
% 51.28/6.99  --qbf_sk_in                             false
% 51.28/6.99  --qbf_pred_elim                         true
% 51.28/6.99  --qbf_split                             512
% 51.28/6.99  
% 51.28/6.99  ------ BMC1 Options
% 51.28/6.99  
% 51.28/6.99  --bmc1_incremental                      false
% 51.28/6.99  --bmc1_axioms                           reachable_all
% 51.28/6.99  --bmc1_min_bound                        0
% 51.28/6.99  --bmc1_max_bound                        -1
% 51.28/6.99  --bmc1_max_bound_default                -1
% 51.28/6.99  --bmc1_symbol_reachability              true
% 51.28/6.99  --bmc1_property_lemmas                  false
% 51.28/6.99  --bmc1_k_induction                      false
% 51.28/6.99  --bmc1_non_equiv_states                 false
% 51.28/6.99  --bmc1_deadlock                         false
% 51.28/6.99  --bmc1_ucm                              false
% 51.28/6.99  --bmc1_add_unsat_core                   none
% 51.28/6.99  --bmc1_unsat_core_children              false
% 51.28/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.28/6.99  --bmc1_out_stat                         full
% 51.28/6.99  --bmc1_ground_init                      false
% 51.28/6.99  --bmc1_pre_inst_next_state              false
% 51.28/6.99  --bmc1_pre_inst_state                   false
% 51.28/6.99  --bmc1_pre_inst_reach_state             false
% 51.28/6.99  --bmc1_out_unsat_core                   false
% 51.28/6.99  --bmc1_aig_witness_out                  false
% 51.28/6.99  --bmc1_verbose                          false
% 51.28/6.99  --bmc1_dump_clauses_tptp                false
% 51.28/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.28/6.99  --bmc1_dump_file                        -
% 51.28/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.28/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.28/6.99  --bmc1_ucm_extend_mode                  1
% 51.28/6.99  --bmc1_ucm_init_mode                    2
% 51.28/6.99  --bmc1_ucm_cone_mode                    none
% 51.28/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.28/6.99  --bmc1_ucm_relax_model                  4
% 51.28/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.28/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.28/6.99  --bmc1_ucm_layered_model                none
% 51.28/6.99  --bmc1_ucm_max_lemma_size               10
% 51.28/6.99  
% 51.28/6.99  ------ AIG Options
% 51.28/6.99  
% 51.28/6.99  --aig_mode                              false
% 51.28/6.99  
% 51.28/6.99  ------ Instantiation Options
% 51.28/6.99  
% 51.28/6.99  --instantiation_flag                    true
% 51.28/6.99  --inst_sos_flag                         true
% 51.28/6.99  --inst_sos_phase                        true
% 51.28/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.28/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.28/6.99  --inst_lit_sel_side                     none
% 51.28/6.99  --inst_solver_per_active                1400
% 51.28/6.99  --inst_solver_calls_frac                1.
% 51.28/6.99  --inst_passive_queue_type               priority_queues
% 51.28/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.28/6.99  --inst_passive_queues_freq              [25;2]
% 51.28/6.99  --inst_dismatching                      true
% 51.28/6.99  --inst_eager_unprocessed_to_passive     true
% 51.28/6.99  --inst_prop_sim_given                   true
% 51.28/6.99  --inst_prop_sim_new                     false
% 51.28/6.99  --inst_subs_new                         false
% 51.28/6.99  --inst_eq_res_simp                      false
% 51.28/6.99  --inst_subs_given                       false
% 51.28/6.99  --inst_orphan_elimination               true
% 51.28/6.99  --inst_learning_loop_flag               true
% 51.28/6.99  --inst_learning_start                   3000
% 51.28/6.99  --inst_learning_factor                  2
% 51.28/6.99  --inst_start_prop_sim_after_learn       3
% 51.28/6.99  --inst_sel_renew                        solver
% 51.28/6.99  --inst_lit_activity_flag                true
% 51.28/6.99  --inst_restr_to_given                   false
% 51.28/6.99  --inst_activity_threshold               500
% 51.28/6.99  --inst_out_proof                        true
% 51.28/6.99  
% 51.28/6.99  ------ Resolution Options
% 51.28/6.99  
% 51.28/6.99  --resolution_flag                       false
% 51.28/6.99  --res_lit_sel                           adaptive
% 51.28/6.99  --res_lit_sel_side                      none
% 51.28/6.99  --res_ordering                          kbo
% 51.28/6.99  --res_to_prop_solver                    active
% 51.28/6.99  --res_prop_simpl_new                    false
% 51.28/6.99  --res_prop_simpl_given                  true
% 51.28/6.99  --res_passive_queue_type                priority_queues
% 51.28/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.28/6.99  --res_passive_queues_freq               [15;5]
% 51.28/6.99  --res_forward_subs                      full
% 51.28/6.99  --res_backward_subs                     full
% 51.28/6.99  --res_forward_subs_resolution           true
% 51.28/6.99  --res_backward_subs_resolution          true
% 51.28/6.99  --res_orphan_elimination                true
% 51.28/6.99  --res_time_limit                        2.
% 51.28/6.99  --res_out_proof                         true
% 51.28/6.99  
% 51.28/6.99  ------ Superposition Options
% 51.28/6.99  
% 51.28/6.99  --superposition_flag                    true
% 51.28/6.99  --sup_passive_queue_type                priority_queues
% 51.28/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.28/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.28/6.99  --demod_completeness_check              fast
% 51.28/6.99  --demod_use_ground                      true
% 51.28/6.99  --sup_to_prop_solver                    passive
% 51.28/6.99  --sup_prop_simpl_new                    true
% 51.28/6.99  --sup_prop_simpl_given                  true
% 51.28/6.99  --sup_fun_splitting                     true
% 51.28/6.99  --sup_smt_interval                      50000
% 51.28/6.99  
% 51.28/6.99  ------ Superposition Simplification Setup
% 51.28/6.99  
% 51.28/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.28/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.28/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.28/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.28/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.28/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.28/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.28/6.99  --sup_immed_triv                        [TrivRules]
% 51.28/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.28/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.28/6.99  --sup_immed_bw_main                     []
% 51.28/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.28/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.28/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.28/6.99  --sup_input_bw                          []
% 51.28/6.99  
% 51.28/6.99  ------ Combination Options
% 51.28/6.99  
% 51.28/6.99  --comb_res_mult                         3
% 51.28/6.99  --comb_sup_mult                         2
% 51.28/6.99  --comb_inst_mult                        10
% 51.28/6.99  
% 51.28/6.99  ------ Debug Options
% 51.28/6.99  
% 51.28/6.99  --dbg_backtrace                         false
% 51.28/6.99  --dbg_dump_prop_clauses                 false
% 51.28/6.99  --dbg_dump_prop_clauses_file            -
% 51.28/6.99  --dbg_out_stat                          false
% 51.28/6.99  
% 51.28/6.99  
% 51.28/6.99  
% 51.28/6.99  
% 51.28/6.99  ------ Proving...
% 51.28/6.99  
% 51.28/6.99  
% 51.28/6.99  % SZS status Theorem for theBenchmark.p
% 51.28/6.99  
% 51.28/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.28/6.99  
% 51.28/6.99  fof(f21,conjecture,(
% 51.28/6.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f22,negated_conjecture,(
% 51.28/6.99    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 51.28/6.99    inference(negated_conjecture,[],[f21])).
% 51.28/6.99  
% 51.28/6.99  fof(f27,plain,(
% 51.28/6.99    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 51.28/6.99    inference(ennf_transformation,[],[f22])).
% 51.28/6.99  
% 51.28/6.99  fof(f33,plain,(
% 51.28/6.99    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3))),
% 51.28/6.99    introduced(choice_axiom,[])).
% 51.28/6.99  
% 51.28/6.99  fof(f34,plain,(
% 51.28/6.99    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3)),
% 51.28/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f33])).
% 51.28/6.99  
% 51.28/6.99  fof(f57,plain,(
% 51.28/6.99    r2_hidden(sK2,sK3)),
% 51.28/6.99    inference(cnf_transformation,[],[f34])).
% 51.28/6.99  
% 51.28/6.99  fof(f19,axiom,(
% 51.28/6.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f32,plain,(
% 51.28/6.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 51.28/6.99    inference(nnf_transformation,[],[f19])).
% 51.28/6.99  
% 51.28/6.99  fof(f55,plain,(
% 51.28/6.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f32])).
% 51.28/6.99  
% 51.28/6.99  fof(f12,axiom,(
% 51.28/6.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f47,plain,(
% 51.28/6.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f12])).
% 51.28/6.99  
% 51.28/6.99  fof(f13,axiom,(
% 51.28/6.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f48,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f13])).
% 51.28/6.99  
% 51.28/6.99  fof(f14,axiom,(
% 51.28/6.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f49,plain,(
% 51.28/6.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f14])).
% 51.28/6.99  
% 51.28/6.99  fof(f15,axiom,(
% 51.28/6.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f50,plain,(
% 51.28/6.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f15])).
% 51.28/6.99  
% 51.28/6.99  fof(f16,axiom,(
% 51.28/6.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f51,plain,(
% 51.28/6.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f16])).
% 51.28/6.99  
% 51.28/6.99  fof(f17,axiom,(
% 51.28/6.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f52,plain,(
% 51.28/6.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f17])).
% 51.28/6.99  
% 51.28/6.99  fof(f18,axiom,(
% 51.28/6.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f53,plain,(
% 51.28/6.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f18])).
% 51.28/6.99  
% 51.28/6.99  fof(f60,plain,(
% 51.28/6.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 51.28/6.99    inference(definition_unfolding,[],[f52,f53])).
% 51.28/6.99  
% 51.28/6.99  fof(f61,plain,(
% 51.28/6.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 51.28/6.99    inference(definition_unfolding,[],[f51,f60])).
% 51.28/6.99  
% 51.28/6.99  fof(f62,plain,(
% 51.28/6.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 51.28/6.99    inference(definition_unfolding,[],[f50,f61])).
% 51.28/6.99  
% 51.28/6.99  fof(f63,plain,(
% 51.28/6.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 51.28/6.99    inference(definition_unfolding,[],[f49,f62])).
% 51.28/6.99  
% 51.28/6.99  fof(f64,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 51.28/6.99    inference(definition_unfolding,[],[f48,f63])).
% 51.28/6.99  
% 51.28/6.99  fof(f65,plain,(
% 51.28/6.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 51.28/6.99    inference(definition_unfolding,[],[f47,f64])).
% 51.28/6.99  
% 51.28/6.99  fof(f69,plain,(
% 51.28/6.99    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 51.28/6.99    inference(definition_unfolding,[],[f55,f65])).
% 51.28/6.99  
% 51.28/6.99  fof(f6,axiom,(
% 51.28/6.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f26,plain,(
% 51.28/6.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.28/6.99    inference(ennf_transformation,[],[f6])).
% 51.28/6.99  
% 51.28/6.99  fof(f41,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f26])).
% 51.28/6.99  
% 51.28/6.99  fof(f20,axiom,(
% 51.28/6.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f56,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 51.28/6.99    inference(cnf_transformation,[],[f20])).
% 51.28/6.99  
% 51.28/6.99  fof(f11,axiom,(
% 51.28/6.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f46,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f11])).
% 51.28/6.99  
% 51.28/6.99  fof(f4,axiom,(
% 51.28/6.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f39,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 51.28/6.99    inference(cnf_transformation,[],[f4])).
% 51.28/6.99  
% 51.28/6.99  fof(f59,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 51.28/6.99    inference(definition_unfolding,[],[f46,f39])).
% 51.28/6.99  
% 51.28/6.99  fof(f71,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 51.28/6.99    inference(definition_unfolding,[],[f56,f59,f64])).
% 51.28/6.99  
% 51.28/6.99  fof(f8,axiom,(
% 51.28/6.99    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f43,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 51.28/6.99    inference(cnf_transformation,[],[f8])).
% 51.28/6.99  
% 51.28/6.99  fof(f68,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 51.28/6.99    inference(definition_unfolding,[],[f43,f39,f59])).
% 51.28/6.99  
% 51.28/6.99  fof(f5,axiom,(
% 51.28/6.99    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f40,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 51.28/6.99    inference(cnf_transformation,[],[f5])).
% 51.28/6.99  
% 51.28/6.99  fof(f66,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 51.28/6.99    inference(definition_unfolding,[],[f40,f59])).
% 51.28/6.99  
% 51.28/6.99  fof(f3,axiom,(
% 51.28/6.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f25,plain,(
% 51.28/6.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 51.28/6.99    inference(ennf_transformation,[],[f3])).
% 51.28/6.99  
% 51.28/6.99  fof(f30,plain,(
% 51.28/6.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 51.28/6.99    introduced(choice_axiom,[])).
% 51.28/6.99  
% 51.28/6.99  fof(f31,plain,(
% 51.28/6.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 51.28/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f30])).
% 51.28/6.99  
% 51.28/6.99  fof(f38,plain,(
% 51.28/6.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 51.28/6.99    inference(cnf_transformation,[],[f31])).
% 51.28/6.99  
% 51.28/6.99  fof(f2,axiom,(
% 51.28/6.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f23,plain,(
% 51.28/6.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 51.28/6.99    inference(rectify,[],[f2])).
% 51.28/6.99  
% 51.28/6.99  fof(f24,plain,(
% 51.28/6.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 51.28/6.99    inference(ennf_transformation,[],[f23])).
% 51.28/6.99  
% 51.28/6.99  fof(f28,plain,(
% 51.28/6.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 51.28/6.99    introduced(choice_axiom,[])).
% 51.28/6.99  
% 51.28/6.99  fof(f29,plain,(
% 51.28/6.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 51.28/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).
% 51.28/6.99  
% 51.28/6.99  fof(f37,plain,(
% 51.28/6.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 51.28/6.99    inference(cnf_transformation,[],[f29])).
% 51.28/6.99  
% 51.28/6.99  fof(f9,axiom,(
% 51.28/6.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f44,plain,(
% 51.28/6.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f9])).
% 51.28/6.99  
% 51.28/6.99  fof(f7,axiom,(
% 51.28/6.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f42,plain,(
% 51.28/6.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.28/6.99    inference(cnf_transformation,[],[f7])).
% 51.28/6.99  
% 51.28/6.99  fof(f67,plain,(
% 51.28/6.99    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 51.28/6.99    inference(definition_unfolding,[],[f42,f39])).
% 51.28/6.99  
% 51.28/6.99  fof(f1,axiom,(
% 51.28/6.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f35,plain,(
% 51.28/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f1])).
% 51.28/6.99  
% 51.28/6.99  fof(f10,axiom,(
% 51.28/6.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 51.28/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.28/6.99  
% 51.28/6.99  fof(f45,plain,(
% 51.28/6.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 51.28/6.99    inference(cnf_transformation,[],[f10])).
% 51.28/6.99  
% 51.28/6.99  fof(f58,plain,(
% 51.28/6.99    k2_xboole_0(k1_tarski(sK2),sK3) != sK3),
% 51.28/6.99    inference(cnf_transformation,[],[f34])).
% 51.28/6.99  
% 51.28/6.99  fof(f72,plain,(
% 51.28/6.99    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3),
% 51.28/6.99    inference(definition_unfolding,[],[f58,f59,f65])).
% 51.28/6.99  
% 51.28/6.99  cnf(c_14,negated_conjecture,
% 51.28/6.99      ( r2_hidden(sK2,sK3) ),
% 51.28/6.99      inference(cnf_transformation,[],[f57]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_510,plain,
% 51.28/6.99      ( r2_hidden(sK2,sK3) = iProver_top ),
% 51.28/6.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_10,plain,
% 51.28/6.99      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 51.28/6.99      | ~ r2_hidden(X0,X1) ),
% 51.28/6.99      inference(cnf_transformation,[],[f69]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_512,plain,
% 51.28/6.99      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 51.28/6.99      | r2_hidden(X0,X1) != iProver_top ),
% 51.28/6.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_5,plain,
% 51.28/6.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.28/6.99      inference(cnf_transformation,[],[f41]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_513,plain,
% 51.28/6.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.28/6.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2980,plain,
% 51.28/6.99      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 51.28/6.99      | r2_hidden(X0,X1) != iProver_top ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_512,c_513]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_102997,plain,
% 51.28/6.99      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_510,c_2980]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_12,plain,
% 51.28/6.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 51.28/6.99      inference(cnf_transformation,[],[f71]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_103363,plain,
% 51.28/6.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_102997,c_12]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_7,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 51.28/6.99      inference(cnf_transformation,[],[f68]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_4,plain,
% 51.28/6.99      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 51.28/6.99      inference(cnf_transformation,[],[f66]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_515,plain,
% 51.28/6.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.28/6.99      inference(light_normalisation,[status(thm)],[c_7,c_4]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_3,plain,
% 51.28/6.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 51.28/6.99      inference(cnf_transformation,[],[f38]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_514,plain,
% 51.28/6.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 51.28/6.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_1,plain,
% 51.28/6.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 51.28/6.99      inference(cnf_transformation,[],[f37]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_8,plain,
% 51.28/6.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 51.28/6.99      inference(cnf_transformation,[],[f44]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_154,plain,
% 51.28/6.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 51.28/6.99      | X3 != X1
% 51.28/6.99      | k1_xboole_0 != X2 ),
% 51.28/6.99      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_155,plain,
% 51.28/6.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 51.28/6.99      inference(unflattening,[status(thm)],[c_154]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_508,plain,
% 51.28/6.99      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 51.28/6.99      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2278,plain,
% 51.28/6.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_514,c_508]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_6,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 51.28/6.99      inference(cnf_transformation,[],[f67]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2459,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.28/6.99      inference(demodulation,[status(thm)],[c_2278,c_6]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_103444,plain,
% 51.28/6.99      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 51.28/6.99      inference(demodulation,[status(thm)],[c_103363,c_515,c_2459]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_0,plain,
% 51.28/6.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 51.28/6.99      inference(cnf_transformation,[],[f35]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_822,plain,
% 51.28/6.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_9,plain,
% 51.28/6.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 51.28/6.99      inference(cnf_transformation,[],[f45]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_809,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_9,c_515]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2466,plain,
% 51.28/6.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_2278,c_12]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_820,plain,
% 51.28/6.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_6,c_12]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_1319,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_515,c_809]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_804,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_515,c_9]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_1733,plain,
% 51.28/6.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_1319,c_804]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2476,plain,
% 51.28/6.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 51.28/6.99      inference(light_normalisation,
% 51.28/6.99                [status(thm)],
% 51.28/6.99                [c_2466,c_820,c_1733,c_2459]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2735,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 51.28/6.99      inference(demodulation,[status(thm)],[c_2476,c_804]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2824,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_809,c_2735]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2836,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 51.28/6.99      inference(demodulation,[status(thm)],[c_2824,c_2459]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2850,plain,
% 51.28/6.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_2836,c_2735]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_2855,plain,
% 51.28/6.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 51.28/6.99      inference(superposition,[status(thm)],[c_9,c_2850]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_13,negated_conjecture,
% 51.28/6.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 51.28/6.99      inference(cnf_transformation,[],[f72]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_5206,plain,
% 51.28/6.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 51.28/6.99      inference(demodulation,[status(thm)],[c_2855,c_13]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(c_14771,plain,
% 51.28/6.99      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != sK3 ),
% 51.28/6.99      inference(demodulation,[status(thm)],[c_822,c_5206]) ).
% 51.28/6.99  
% 51.28/6.99  cnf(contradiction,plain,
% 51.28/6.99      ( $false ),
% 51.28/6.99      inference(minisat,[status(thm)],[c_103444,c_14771]) ).
% 51.28/6.99  
% 51.28/6.99  
% 51.28/6.99  % SZS output end CNFRefutation for theBenchmark.p
% 51.28/6.99  
% 51.28/6.99  ------                               Statistics
% 51.28/6.99  
% 51.28/6.99  ------ General
% 51.28/6.99  
% 51.28/6.99  abstr_ref_over_cycles:                  0
% 51.28/6.99  abstr_ref_under_cycles:                 0
% 51.28/6.99  gc_basic_clause_elim:                   0
% 51.28/6.99  forced_gc_time:                         0
% 51.28/6.99  parsing_time:                           0.011
% 51.28/6.99  unif_index_cands_time:                  0.
% 51.28/6.99  unif_index_add_time:                    0.
% 51.28/6.99  orderings_time:                         0.
% 51.28/6.99  out_proof_time:                         0.017
% 51.28/6.99  total_time:                             6.337
% 51.28/6.99  num_of_symbols:                         43
% 51.28/6.99  num_of_terms:                           495104
% 51.28/6.99  
% 51.28/6.99  ------ Preprocessing
% 51.28/6.99  
% 51.28/6.99  num_of_splits:                          0
% 51.28/6.99  num_of_split_atoms:                     0
% 51.28/6.99  num_of_reused_defs:                     0
% 51.28/6.99  num_eq_ax_congr_red:                    13
% 51.28/6.99  num_of_sem_filtered_clauses:            1
% 51.28/6.99  num_of_subtypes:                        0
% 51.28/6.99  monotx_restored_types:                  0
% 51.28/6.99  sat_num_of_epr_types:                   0
% 51.28/6.99  sat_num_of_non_cyclic_types:            0
% 51.28/6.99  sat_guarded_non_collapsed_types:        0
% 51.28/6.99  num_pure_diseq_elim:                    0
% 51.28/6.99  simp_replaced_by:                       0
% 51.28/6.99  res_preprocessed:                       74
% 51.28/6.99  prep_upred:                             0
% 51.28/6.99  prep_unflattend:                        8
% 51.28/6.99  smt_new_axioms:                         0
% 51.28/6.99  pred_elim_cands:                        2
% 51.28/6.99  pred_elim:                              1
% 51.28/6.99  pred_elim_cl:                           1
% 51.28/6.99  pred_elim_cycles:                       3
% 51.28/6.99  merged_defs:                            8
% 51.28/6.99  merged_defs_ncl:                        0
% 51.28/6.99  bin_hyper_res:                          8
% 51.28/6.99  prep_cycles:                            4
% 51.28/6.99  pred_elim_time:                         0.001
% 51.28/6.99  splitting_time:                         0.
% 51.28/6.99  sem_filter_time:                        0.
% 51.28/6.99  monotx_time:                            0.
% 51.28/6.99  subtype_inf_time:                       0.
% 51.28/6.99  
% 51.28/6.99  ------ Problem properties
% 51.28/6.99  
% 51.28/6.99  clauses:                                14
% 51.28/6.99  conjectures:                            2
% 51.28/6.99  epr:                                    1
% 51.28/6.99  horn:                                   13
% 51.28/6.99  ground:                                 2
% 51.28/6.99  unary:                                  9
% 51.28/6.99  binary:                                 5
% 51.28/6.99  lits:                                   19
% 51.28/6.99  lits_eq:                                9
% 51.28/6.99  fd_pure:                                0
% 51.28/6.99  fd_pseudo:                              0
% 51.28/6.99  fd_cond:                                1
% 51.28/6.99  fd_pseudo_cond:                         0
% 51.28/6.99  ac_symbols:                             1
% 51.28/6.99  
% 51.28/6.99  ------ Propositional Solver
% 51.28/6.99  
% 51.28/6.99  prop_solver_calls:                      41
% 51.28/6.99  prop_fast_solver_calls:                 885
% 51.28/6.99  smt_solver_calls:                       0
% 51.28/6.99  smt_fast_solver_calls:                  0
% 51.28/6.99  prop_num_of_clauses:                    40423
% 51.28/6.99  prop_preprocess_simplified:             24531
% 51.28/6.99  prop_fo_subsumed:                       0
% 51.28/6.99  prop_solver_time:                       0.
% 51.28/6.99  smt_solver_time:                        0.
% 51.28/6.99  smt_fast_solver_time:                   0.
% 51.28/6.99  prop_fast_solver_time:                  0.
% 51.28/6.99  prop_unsat_core_time:                   0.005
% 51.28/6.99  
% 51.28/6.99  ------ QBF
% 51.28/6.99  
% 51.28/6.99  qbf_q_res:                              0
% 51.28/6.99  qbf_num_tautologies:                    0
% 51.28/6.99  qbf_prep_cycles:                        0
% 51.28/6.99  
% 51.28/6.99  ------ BMC1
% 51.28/6.99  
% 51.28/6.99  bmc1_current_bound:                     -1
% 51.28/6.99  bmc1_last_solved_bound:                 -1
% 51.28/6.99  bmc1_unsat_core_size:                   -1
% 51.28/6.99  bmc1_unsat_core_parents_size:           -1
% 51.28/6.99  bmc1_merge_next_fun:                    0
% 51.28/6.99  bmc1_unsat_core_clauses_time:           0.
% 51.28/6.99  
% 51.28/6.99  ------ Instantiation
% 51.28/6.99  
% 51.28/6.99  inst_num_of_clauses:                    4527
% 51.28/6.99  inst_num_in_passive:                    932
% 51.28/6.99  inst_num_in_active:                     1346
% 51.28/6.99  inst_num_in_unprocessed:                2249
% 51.28/6.99  inst_num_of_loops:                      1420
% 51.28/6.99  inst_num_of_learning_restarts:          0
% 51.28/6.99  inst_num_moves_active_passive:          68
% 51.28/6.99  inst_lit_activity:                      0
% 51.28/6.99  inst_lit_activity_moves:                0
% 51.28/6.99  inst_num_tautologies:                   0
% 51.28/6.99  inst_num_prop_implied:                  0
% 51.28/6.99  inst_num_existing_simplified:           0
% 51.28/6.99  inst_num_eq_res_simplified:             0
% 51.28/6.99  inst_num_child_elim:                    0
% 51.28/6.99  inst_num_of_dismatching_blockings:      1861
% 51.28/6.99  inst_num_of_non_proper_insts:           5336
% 51.28/6.99  inst_num_of_duplicates:                 0
% 51.28/6.99  inst_inst_num_from_inst_to_res:         0
% 51.28/6.99  inst_dismatching_checking_time:         0.
% 51.28/6.99  
% 51.28/6.99  ------ Resolution
% 51.28/6.99  
% 51.28/6.99  res_num_of_clauses:                     0
% 51.28/6.99  res_num_in_passive:                     0
% 51.28/6.99  res_num_in_active:                      0
% 51.28/6.99  res_num_of_loops:                       78
% 51.28/6.99  res_forward_subset_subsumed:            779
% 51.28/6.99  res_backward_subset_subsumed:           0
% 51.28/6.99  res_forward_subsumed:                   0
% 51.28/6.99  res_backward_subsumed:                  0
% 51.28/6.99  res_forward_subsumption_resolution:     0
% 51.28/6.99  res_backward_subsumption_resolution:    0
% 51.28/6.99  res_clause_to_clause_subsumption:       204339
% 51.28/6.99  res_orphan_elimination:                 0
% 51.28/6.99  res_tautology_del:                      353
% 51.28/6.99  res_num_eq_res_simplified:              0
% 51.28/6.99  res_num_sel_changes:                    0
% 51.28/6.99  res_moves_from_active_to_pass:          0
% 51.28/6.99  
% 51.28/6.99  ------ Superposition
% 51.28/6.99  
% 51.28/6.99  sup_time_total:                         0.
% 51.28/6.99  sup_time_generating:                    0.
% 51.28/6.99  sup_time_sim_full:                      0.
% 51.28/6.99  sup_time_sim_immed:                     0.
% 51.28/6.99  
% 51.28/6.99  sup_num_of_clauses:                     12158
% 51.28/6.99  sup_num_in_active:                      253
% 51.28/6.99  sup_num_in_passive:                     11905
% 51.28/6.99  sup_num_of_loops:                       283
% 51.28/6.99  sup_fw_superposition:                   21684
% 51.28/6.99  sup_bw_superposition:                   9647
% 51.28/6.99  sup_immediate_simplified:               19717
% 51.28/6.99  sup_given_eliminated:                   3
% 51.28/6.99  comparisons_done:                       0
% 51.28/6.99  comparisons_avoided:                    0
% 51.28/6.99  
% 51.28/6.99  ------ Simplifications
% 51.28/6.99  
% 51.28/6.99  
% 51.28/6.99  sim_fw_subset_subsumed:                 8
% 51.28/6.99  sim_bw_subset_subsumed:                 0
% 51.28/6.99  sim_fw_subsumed:                        591
% 51.28/6.99  sim_bw_subsumed:                        24
% 51.28/6.99  sim_fw_subsumption_res:                 0
% 51.28/6.99  sim_bw_subsumption_res:                 0
% 51.28/6.99  sim_tautology_del:                      1
% 51.28/6.99  sim_eq_tautology_del:                   2023
% 51.28/6.99  sim_eq_res_simp:                        0
% 51.28/6.99  sim_fw_demodulated:                     29772
% 51.28/6.99  sim_bw_demodulated:                     1189
% 51.28/6.99  sim_light_normalised:                   2896
% 51.28/6.99  sim_joinable_taut:                      268
% 51.28/6.99  sim_joinable_simp:                      0
% 51.28/6.99  sim_ac_normalised:                      0
% 51.28/6.99  sim_smt_subsumption:                    0
% 51.28/6.99  
%------------------------------------------------------------------------------
