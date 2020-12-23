%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:15 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 391 expanded)
%              Number of clauses        :   39 (  64 expanded)
%              Number of leaves         :   20 ( 114 expanded)
%              Depth                    :   15
%              Number of atoms          :  194 ( 542 expanded)
%              Number of equality atoms :   87 ( 379 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f36])).

fof(f62,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f51,f66,f66,f48])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f30])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f38,f66,f66])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f52,f48,f48,f66])).

fof(f63,plain,(
    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f75,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
    inference(definition_unfolding,[],[f63,f66,f67])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_546,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_549,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_551,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2229,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_551])).

cnf(c_5612,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,X0),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_546,c_2229])).

cnf(c_5782,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_546,c_5612])).

cnf(c_12,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6607,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_5782,c_12])).

cnf(c_10,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_550,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_558,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_552,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_728,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_552,c_551])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_555,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1639,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_555])).

cnf(c_1720,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_558,c_1639])).

cnf(c_1904,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_550,c_1720])).

cnf(c_2030,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1904,c_551])).

cnf(c_0,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_829,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_13,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_955,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_829,c_13])).

cnf(c_964,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_955,c_728])).

cnf(c_2034,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2030,c_964])).

cnf(c_959,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_829,c_12])).

cnf(c_960,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_959,c_829])).

cnf(c_1003,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_728,c_960])).

cnf(c_2036,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2034,c_1003])).

cnf(c_6609,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_6607,c_10,c_2036])).

cnf(c_18,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_828,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != sK3 ),
    inference(demodulation,[status(thm)],[c_0,c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6609,c_828])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:10:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.03/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.06  
% 3.03/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/1.06  
% 3.03/1.06  ------  iProver source info
% 3.03/1.06  
% 3.03/1.06  git: date: 2020-06-30 10:37:57 +0100
% 3.03/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/1.06  git: non_committed_changes: false
% 3.03/1.06  git: last_make_outside_of_git: false
% 3.03/1.06  
% 3.03/1.06  ------ 
% 3.03/1.06  
% 3.03/1.06  ------ Input Options
% 3.03/1.06  
% 3.03/1.06  --out_options                           all
% 3.03/1.06  --tptp_safe_out                         true
% 3.03/1.06  --problem_path                          ""
% 3.03/1.06  --include_path                          ""
% 3.03/1.06  --clausifier                            res/vclausify_rel
% 3.03/1.06  --clausifier_options                    --mode clausify
% 3.03/1.06  --stdin                                 false
% 3.03/1.06  --stats_out                             all
% 3.03/1.06  
% 3.03/1.06  ------ General Options
% 3.03/1.06  
% 3.03/1.06  --fof                                   false
% 3.03/1.06  --time_out_real                         305.
% 3.03/1.06  --time_out_virtual                      -1.
% 3.03/1.06  --symbol_type_check                     false
% 3.03/1.06  --clausify_out                          false
% 3.03/1.06  --sig_cnt_out                           false
% 3.03/1.06  --trig_cnt_out                          false
% 3.03/1.06  --trig_cnt_out_tolerance                1.
% 3.03/1.06  --trig_cnt_out_sk_spl                   false
% 3.03/1.06  --abstr_cl_out                          false
% 3.03/1.06  
% 3.03/1.06  ------ Global Options
% 3.03/1.06  
% 3.03/1.06  --schedule                              default
% 3.03/1.06  --add_important_lit                     false
% 3.03/1.06  --prop_solver_per_cl                    1000
% 3.03/1.06  --min_unsat_core                        false
% 3.03/1.06  --soft_assumptions                      false
% 3.03/1.06  --soft_lemma_size                       3
% 3.03/1.06  --prop_impl_unit_size                   0
% 3.03/1.06  --prop_impl_unit                        []
% 3.03/1.06  --share_sel_clauses                     true
% 3.03/1.06  --reset_solvers                         false
% 3.03/1.06  --bc_imp_inh                            [conj_cone]
% 3.03/1.06  --conj_cone_tolerance                   3.
% 3.03/1.06  --extra_neg_conj                        none
% 3.03/1.06  --large_theory_mode                     true
% 3.03/1.06  --prolific_symb_bound                   200
% 3.03/1.06  --lt_threshold                          2000
% 3.03/1.06  --clause_weak_htbl                      true
% 3.03/1.06  --gc_record_bc_elim                     false
% 3.03/1.06  
% 3.03/1.06  ------ Preprocessing Options
% 3.03/1.06  
% 3.03/1.06  --preprocessing_flag                    true
% 3.03/1.06  --time_out_prep_mult                    0.1
% 3.03/1.06  --splitting_mode                        input
% 3.03/1.06  --splitting_grd                         true
% 3.03/1.06  --splitting_cvd                         false
% 3.03/1.06  --splitting_cvd_svl                     false
% 3.03/1.06  --splitting_nvd                         32
% 3.03/1.06  --sub_typing                            true
% 3.03/1.06  --prep_gs_sim                           true
% 3.03/1.06  --prep_unflatten                        true
% 3.03/1.06  --prep_res_sim                          true
% 3.03/1.06  --prep_upred                            true
% 3.03/1.06  --prep_sem_filter                       exhaustive
% 3.03/1.06  --prep_sem_filter_out                   false
% 3.03/1.06  --pred_elim                             true
% 3.03/1.06  --res_sim_input                         true
% 3.03/1.06  --eq_ax_congr_red                       true
% 3.03/1.06  --pure_diseq_elim                       true
% 3.03/1.06  --brand_transform                       false
% 3.03/1.06  --non_eq_to_eq                          false
% 3.03/1.06  --prep_def_merge                        true
% 3.03/1.06  --prep_def_merge_prop_impl              false
% 3.03/1.06  --prep_def_merge_mbd                    true
% 3.03/1.06  --prep_def_merge_tr_red                 false
% 3.03/1.06  --prep_def_merge_tr_cl                  false
% 3.03/1.06  --smt_preprocessing                     true
% 3.03/1.06  --smt_ac_axioms                         fast
% 3.03/1.06  --preprocessed_out                      false
% 3.03/1.06  --preprocessed_stats                    false
% 3.03/1.06  
% 3.03/1.06  ------ Abstraction refinement Options
% 3.03/1.06  
% 3.03/1.06  --abstr_ref                             []
% 3.03/1.06  --abstr_ref_prep                        false
% 3.03/1.06  --abstr_ref_until_sat                   false
% 3.03/1.06  --abstr_ref_sig_restrict                funpre
% 3.03/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.06  --abstr_ref_under                       []
% 3.03/1.06  
% 3.03/1.06  ------ SAT Options
% 3.03/1.06  
% 3.03/1.06  --sat_mode                              false
% 3.03/1.06  --sat_fm_restart_options                ""
% 3.03/1.06  --sat_gr_def                            false
% 3.03/1.06  --sat_epr_types                         true
% 3.03/1.06  --sat_non_cyclic_types                  false
% 3.03/1.06  --sat_finite_models                     false
% 3.03/1.06  --sat_fm_lemmas                         false
% 3.03/1.06  --sat_fm_prep                           false
% 3.03/1.06  --sat_fm_uc_incr                        true
% 3.03/1.06  --sat_out_model                         small
% 3.03/1.06  --sat_out_clauses                       false
% 3.03/1.06  
% 3.03/1.06  ------ QBF Options
% 3.03/1.06  
% 3.03/1.06  --qbf_mode                              false
% 3.03/1.06  --qbf_elim_univ                         false
% 3.03/1.06  --qbf_dom_inst                          none
% 3.03/1.06  --qbf_dom_pre_inst                      false
% 3.03/1.06  --qbf_sk_in                             false
% 3.03/1.06  --qbf_pred_elim                         true
% 3.03/1.06  --qbf_split                             512
% 3.03/1.06  
% 3.03/1.06  ------ BMC1 Options
% 3.03/1.06  
% 3.03/1.06  --bmc1_incremental                      false
% 3.03/1.06  --bmc1_axioms                           reachable_all
% 3.03/1.06  --bmc1_min_bound                        0
% 3.03/1.06  --bmc1_max_bound                        -1
% 3.03/1.06  --bmc1_max_bound_default                -1
% 3.03/1.06  --bmc1_symbol_reachability              true
% 3.03/1.06  --bmc1_property_lemmas                  false
% 3.03/1.06  --bmc1_k_induction                      false
% 3.03/1.06  --bmc1_non_equiv_states                 false
% 3.03/1.06  --bmc1_deadlock                         false
% 3.03/1.06  --bmc1_ucm                              false
% 3.03/1.06  --bmc1_add_unsat_core                   none
% 3.03/1.06  --bmc1_unsat_core_children              false
% 3.03/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.06  --bmc1_out_stat                         full
% 3.03/1.06  --bmc1_ground_init                      false
% 3.03/1.06  --bmc1_pre_inst_next_state              false
% 3.03/1.06  --bmc1_pre_inst_state                   false
% 3.03/1.06  --bmc1_pre_inst_reach_state             false
% 3.03/1.06  --bmc1_out_unsat_core                   false
% 3.03/1.06  --bmc1_aig_witness_out                  false
% 3.03/1.06  --bmc1_verbose                          false
% 3.03/1.06  --bmc1_dump_clauses_tptp                false
% 3.03/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.06  --bmc1_dump_file                        -
% 3.03/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.06  --bmc1_ucm_extend_mode                  1
% 3.03/1.06  --bmc1_ucm_init_mode                    2
% 3.03/1.06  --bmc1_ucm_cone_mode                    none
% 3.03/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.06  --bmc1_ucm_relax_model                  4
% 3.03/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.06  --bmc1_ucm_layered_model                none
% 3.03/1.06  --bmc1_ucm_max_lemma_size               10
% 3.03/1.06  
% 3.03/1.06  ------ AIG Options
% 3.03/1.06  
% 3.03/1.06  --aig_mode                              false
% 3.03/1.06  
% 3.03/1.06  ------ Instantiation Options
% 3.03/1.06  
% 3.03/1.06  --instantiation_flag                    true
% 3.03/1.06  --inst_sos_flag                         false
% 3.03/1.06  --inst_sos_phase                        true
% 3.03/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.06  --inst_lit_sel_side                     num_symb
% 3.03/1.06  --inst_solver_per_active                1400
% 3.03/1.06  --inst_solver_calls_frac                1.
% 3.03/1.06  --inst_passive_queue_type               priority_queues
% 3.03/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.06  --inst_passive_queues_freq              [25;2]
% 3.03/1.06  --inst_dismatching                      true
% 3.03/1.06  --inst_eager_unprocessed_to_passive     true
% 3.03/1.06  --inst_prop_sim_given                   true
% 3.03/1.06  --inst_prop_sim_new                     false
% 3.03/1.06  --inst_subs_new                         false
% 3.03/1.06  --inst_eq_res_simp                      false
% 3.03/1.06  --inst_subs_given                       false
% 3.03/1.06  --inst_orphan_elimination               true
% 3.03/1.06  --inst_learning_loop_flag               true
% 3.03/1.06  --inst_learning_start                   3000
% 3.03/1.06  --inst_learning_factor                  2
% 3.03/1.06  --inst_start_prop_sim_after_learn       3
% 3.03/1.06  --inst_sel_renew                        solver
% 3.03/1.06  --inst_lit_activity_flag                true
% 3.03/1.06  --inst_restr_to_given                   false
% 3.03/1.06  --inst_activity_threshold               500
% 3.03/1.06  --inst_out_proof                        true
% 3.03/1.06  
% 3.03/1.06  ------ Resolution Options
% 3.03/1.06  
% 3.03/1.06  --resolution_flag                       true
% 3.03/1.06  --res_lit_sel                           adaptive
% 3.03/1.06  --res_lit_sel_side                      none
% 3.03/1.06  --res_ordering                          kbo
% 3.03/1.06  --res_to_prop_solver                    active
% 3.03/1.06  --res_prop_simpl_new                    false
% 3.03/1.06  --res_prop_simpl_given                  true
% 3.03/1.06  --res_passive_queue_type                priority_queues
% 3.03/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.06  --res_passive_queues_freq               [15;5]
% 3.03/1.06  --res_forward_subs                      full
% 3.03/1.06  --res_backward_subs                     full
% 3.03/1.06  --res_forward_subs_resolution           true
% 3.03/1.06  --res_backward_subs_resolution          true
% 3.03/1.06  --res_orphan_elimination                true
% 3.03/1.06  --res_time_limit                        2.
% 3.03/1.06  --res_out_proof                         true
% 3.03/1.06  
% 3.03/1.06  ------ Superposition Options
% 3.03/1.06  
% 3.03/1.06  --superposition_flag                    true
% 3.03/1.06  --sup_passive_queue_type                priority_queues
% 3.03/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.06  --demod_completeness_check              fast
% 3.03/1.06  --demod_use_ground                      true
% 3.03/1.06  --sup_to_prop_solver                    passive
% 3.03/1.06  --sup_prop_simpl_new                    true
% 3.03/1.06  --sup_prop_simpl_given                  true
% 3.03/1.06  --sup_fun_splitting                     false
% 3.03/1.06  --sup_smt_interval                      50000
% 3.03/1.06  
% 3.03/1.06  ------ Superposition Simplification Setup
% 3.03/1.06  
% 3.03/1.06  --sup_indices_passive                   []
% 3.03/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.06  --sup_full_bw                           [BwDemod]
% 3.03/1.06  --sup_immed_triv                        [TrivRules]
% 3.03/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.06  --sup_immed_bw_main                     []
% 3.03/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.06  
% 3.03/1.06  ------ Combination Options
% 3.03/1.06  
% 3.03/1.06  --comb_res_mult                         3
% 3.03/1.06  --comb_sup_mult                         2
% 3.03/1.06  --comb_inst_mult                        10
% 3.03/1.06  
% 3.03/1.06  ------ Debug Options
% 3.03/1.06  
% 3.03/1.06  --dbg_backtrace                         false
% 3.03/1.06  --dbg_dump_prop_clauses                 false
% 3.03/1.06  --dbg_dump_prop_clauses_file            -
% 3.03/1.06  --dbg_out_stat                          false
% 3.03/1.06  ------ Parsing...
% 3.03/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/1.06  
% 3.03/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.03/1.06  
% 3.03/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/1.06  
% 3.03/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/1.06  ------ Proving...
% 3.03/1.06  ------ Problem Properties 
% 3.03/1.06  
% 3.03/1.06  
% 3.03/1.06  clauses                                 19
% 3.03/1.06  conjectures                             2
% 3.03/1.06  EPR                                     6
% 3.03/1.06  Horn                                    17
% 3.03/1.06  unary                                   8
% 3.03/1.06  binary                                  8
% 3.03/1.06  lits                                    33
% 3.03/1.06  lits eq                                 7
% 3.03/1.06  fd_pure                                 0
% 3.03/1.06  fd_pseudo                               0
% 3.03/1.06  fd_cond                                 0
% 3.03/1.06  fd_pseudo_cond                          1
% 3.03/1.06  AC symbols                              0
% 3.03/1.06  
% 3.03/1.06  ------ Schedule dynamic 5 is on 
% 3.03/1.06  
% 3.03/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/1.06  
% 3.03/1.06  
% 3.03/1.06  ------ 
% 3.03/1.06  Current options:
% 3.03/1.06  ------ 
% 3.03/1.06  
% 3.03/1.06  ------ Input Options
% 3.03/1.06  
% 3.03/1.06  --out_options                           all
% 3.03/1.06  --tptp_safe_out                         true
% 3.03/1.06  --problem_path                          ""
% 3.03/1.06  --include_path                          ""
% 3.03/1.06  --clausifier                            res/vclausify_rel
% 3.03/1.06  --clausifier_options                    --mode clausify
% 3.03/1.06  --stdin                                 false
% 3.03/1.06  --stats_out                             all
% 3.03/1.06  
% 3.03/1.06  ------ General Options
% 3.03/1.06  
% 3.03/1.06  --fof                                   false
% 3.03/1.06  --time_out_real                         305.
% 3.03/1.06  --time_out_virtual                      -1.
% 3.03/1.06  --symbol_type_check                     false
% 3.03/1.06  --clausify_out                          false
% 3.03/1.06  --sig_cnt_out                           false
% 3.03/1.06  --trig_cnt_out                          false
% 3.03/1.06  --trig_cnt_out_tolerance                1.
% 3.03/1.06  --trig_cnt_out_sk_spl                   false
% 3.03/1.06  --abstr_cl_out                          false
% 3.03/1.06  
% 3.03/1.06  ------ Global Options
% 3.03/1.06  
% 3.03/1.06  --schedule                              default
% 3.03/1.06  --add_important_lit                     false
% 3.03/1.06  --prop_solver_per_cl                    1000
% 3.03/1.06  --min_unsat_core                        false
% 3.03/1.06  --soft_assumptions                      false
% 3.03/1.06  --soft_lemma_size                       3
% 3.03/1.06  --prop_impl_unit_size                   0
% 3.03/1.06  --prop_impl_unit                        []
% 3.03/1.06  --share_sel_clauses                     true
% 3.03/1.06  --reset_solvers                         false
% 3.03/1.06  --bc_imp_inh                            [conj_cone]
% 3.03/1.06  --conj_cone_tolerance                   3.
% 3.03/1.06  --extra_neg_conj                        none
% 3.03/1.06  --large_theory_mode                     true
% 3.03/1.06  --prolific_symb_bound                   200
% 3.03/1.06  --lt_threshold                          2000
% 3.03/1.06  --clause_weak_htbl                      true
% 3.03/1.06  --gc_record_bc_elim                     false
% 3.03/1.06  
% 3.03/1.06  ------ Preprocessing Options
% 3.03/1.06  
% 3.03/1.06  --preprocessing_flag                    true
% 3.03/1.06  --time_out_prep_mult                    0.1
% 3.03/1.06  --splitting_mode                        input
% 3.03/1.06  --splitting_grd                         true
% 3.03/1.06  --splitting_cvd                         false
% 3.03/1.06  --splitting_cvd_svl                     false
% 3.03/1.06  --splitting_nvd                         32
% 3.03/1.06  --sub_typing                            true
% 3.03/1.06  --prep_gs_sim                           true
% 3.03/1.06  --prep_unflatten                        true
% 3.03/1.06  --prep_res_sim                          true
% 3.03/1.06  --prep_upred                            true
% 3.03/1.06  --prep_sem_filter                       exhaustive
% 3.03/1.06  --prep_sem_filter_out                   false
% 3.03/1.06  --pred_elim                             true
% 3.03/1.06  --res_sim_input                         true
% 3.03/1.06  --eq_ax_congr_red                       true
% 3.03/1.06  --pure_diseq_elim                       true
% 3.03/1.06  --brand_transform                       false
% 3.03/1.06  --non_eq_to_eq                          false
% 3.03/1.06  --prep_def_merge                        true
% 3.03/1.06  --prep_def_merge_prop_impl              false
% 3.03/1.06  --prep_def_merge_mbd                    true
% 3.03/1.06  --prep_def_merge_tr_red                 false
% 3.03/1.06  --prep_def_merge_tr_cl                  false
% 3.03/1.06  --smt_preprocessing                     true
% 3.03/1.06  --smt_ac_axioms                         fast
% 3.03/1.06  --preprocessed_out                      false
% 3.03/1.06  --preprocessed_stats                    false
% 3.03/1.06  
% 3.03/1.06  ------ Abstraction refinement Options
% 3.03/1.06  
% 3.03/1.06  --abstr_ref                             []
% 3.03/1.06  --abstr_ref_prep                        false
% 3.03/1.06  --abstr_ref_until_sat                   false
% 3.03/1.06  --abstr_ref_sig_restrict                funpre
% 3.03/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.06  --abstr_ref_under                       []
% 3.03/1.06  
% 3.03/1.06  ------ SAT Options
% 3.03/1.06  
% 3.03/1.06  --sat_mode                              false
% 3.03/1.06  --sat_fm_restart_options                ""
% 3.03/1.06  --sat_gr_def                            false
% 3.03/1.06  --sat_epr_types                         true
% 3.03/1.06  --sat_non_cyclic_types                  false
% 3.03/1.06  --sat_finite_models                     false
% 3.03/1.06  --sat_fm_lemmas                         false
% 3.03/1.06  --sat_fm_prep                           false
% 3.03/1.06  --sat_fm_uc_incr                        true
% 3.03/1.06  --sat_out_model                         small
% 3.03/1.06  --sat_out_clauses                       false
% 3.03/1.06  
% 3.03/1.06  ------ QBF Options
% 3.03/1.06  
% 3.03/1.06  --qbf_mode                              false
% 3.03/1.06  --qbf_elim_univ                         false
% 3.03/1.06  --qbf_dom_inst                          none
% 3.03/1.06  --qbf_dom_pre_inst                      false
% 3.03/1.06  --qbf_sk_in                             false
% 3.03/1.06  --qbf_pred_elim                         true
% 3.03/1.06  --qbf_split                             512
% 3.03/1.06  
% 3.03/1.06  ------ BMC1 Options
% 3.03/1.06  
% 3.03/1.06  --bmc1_incremental                      false
% 3.03/1.06  --bmc1_axioms                           reachable_all
% 3.03/1.06  --bmc1_min_bound                        0
% 3.03/1.06  --bmc1_max_bound                        -1
% 3.03/1.06  --bmc1_max_bound_default                -1
% 3.03/1.06  --bmc1_symbol_reachability              true
% 3.03/1.06  --bmc1_property_lemmas                  false
% 3.03/1.06  --bmc1_k_induction                      false
% 3.03/1.06  --bmc1_non_equiv_states                 false
% 3.03/1.06  --bmc1_deadlock                         false
% 3.03/1.06  --bmc1_ucm                              false
% 3.03/1.06  --bmc1_add_unsat_core                   none
% 3.03/1.06  --bmc1_unsat_core_children              false
% 3.03/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.06  --bmc1_out_stat                         full
% 3.03/1.06  --bmc1_ground_init                      false
% 3.03/1.06  --bmc1_pre_inst_next_state              false
% 3.03/1.06  --bmc1_pre_inst_state                   false
% 3.03/1.06  --bmc1_pre_inst_reach_state             false
% 3.03/1.06  --bmc1_out_unsat_core                   false
% 3.03/1.06  --bmc1_aig_witness_out                  false
% 3.03/1.06  --bmc1_verbose                          false
% 3.03/1.06  --bmc1_dump_clauses_tptp                false
% 3.03/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.06  --bmc1_dump_file                        -
% 3.03/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.06  --bmc1_ucm_extend_mode                  1
% 3.03/1.06  --bmc1_ucm_init_mode                    2
% 3.03/1.06  --bmc1_ucm_cone_mode                    none
% 3.03/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.06  --bmc1_ucm_relax_model                  4
% 3.03/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.06  --bmc1_ucm_layered_model                none
% 3.03/1.06  --bmc1_ucm_max_lemma_size               10
% 3.03/1.06  
% 3.03/1.06  ------ AIG Options
% 3.03/1.06  
% 3.03/1.06  --aig_mode                              false
% 3.03/1.06  
% 3.03/1.06  ------ Instantiation Options
% 3.03/1.06  
% 3.03/1.06  --instantiation_flag                    true
% 3.03/1.06  --inst_sos_flag                         false
% 3.03/1.06  --inst_sos_phase                        true
% 3.03/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.06  --inst_lit_sel_side                     none
% 3.03/1.06  --inst_solver_per_active                1400
% 3.03/1.06  --inst_solver_calls_frac                1.
% 3.03/1.06  --inst_passive_queue_type               priority_queues
% 3.03/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.06  --inst_passive_queues_freq              [25;2]
% 3.03/1.06  --inst_dismatching                      true
% 3.03/1.06  --inst_eager_unprocessed_to_passive     true
% 3.03/1.06  --inst_prop_sim_given                   true
% 3.03/1.06  --inst_prop_sim_new                     false
% 3.03/1.06  --inst_subs_new                         false
% 3.03/1.06  --inst_eq_res_simp                      false
% 3.03/1.06  --inst_subs_given                       false
% 3.03/1.06  --inst_orphan_elimination               true
% 3.03/1.06  --inst_learning_loop_flag               true
% 3.03/1.06  --inst_learning_start                   3000
% 3.03/1.06  --inst_learning_factor                  2
% 3.03/1.06  --inst_start_prop_sim_after_learn       3
% 3.03/1.06  --inst_sel_renew                        solver
% 3.03/1.06  --inst_lit_activity_flag                true
% 3.03/1.06  --inst_restr_to_given                   false
% 3.03/1.06  --inst_activity_threshold               500
% 3.03/1.06  --inst_out_proof                        true
% 3.03/1.06  
% 3.03/1.06  ------ Resolution Options
% 3.03/1.06  
% 3.03/1.06  --resolution_flag                       false
% 3.03/1.06  --res_lit_sel                           adaptive
% 3.03/1.06  --res_lit_sel_side                      none
% 3.03/1.06  --res_ordering                          kbo
% 3.03/1.06  --res_to_prop_solver                    active
% 3.03/1.06  --res_prop_simpl_new                    false
% 3.03/1.06  --res_prop_simpl_given                  true
% 3.03/1.06  --res_passive_queue_type                priority_queues
% 3.03/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.06  --res_passive_queues_freq               [15;5]
% 3.03/1.06  --res_forward_subs                      full
% 3.03/1.06  --res_backward_subs                     full
% 3.03/1.06  --res_forward_subs_resolution           true
% 3.03/1.06  --res_backward_subs_resolution          true
% 3.03/1.06  --res_orphan_elimination                true
% 3.03/1.06  --res_time_limit                        2.
% 3.03/1.06  --res_out_proof                         true
% 3.03/1.06  
% 3.03/1.06  ------ Superposition Options
% 3.03/1.06  
% 3.03/1.06  --superposition_flag                    true
% 3.03/1.06  --sup_passive_queue_type                priority_queues
% 3.03/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.06  --demod_completeness_check              fast
% 3.03/1.06  --demod_use_ground                      true
% 3.03/1.06  --sup_to_prop_solver                    passive
% 3.03/1.06  --sup_prop_simpl_new                    true
% 3.03/1.06  --sup_prop_simpl_given                  true
% 3.03/1.06  --sup_fun_splitting                     false
% 3.03/1.06  --sup_smt_interval                      50000
% 3.03/1.06  
% 3.03/1.06  ------ Superposition Simplification Setup
% 3.03/1.06  
% 3.03/1.06  --sup_indices_passive                   []
% 3.03/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.06  --sup_full_bw                           [BwDemod]
% 3.03/1.06  --sup_immed_triv                        [TrivRules]
% 3.03/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.06  --sup_immed_bw_main                     []
% 3.03/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.06  
% 3.03/1.06  ------ Combination Options
% 3.03/1.06  
% 3.03/1.06  --comb_res_mult                         3
% 3.03/1.06  --comb_sup_mult                         2
% 3.03/1.06  --comb_inst_mult                        10
% 3.03/1.06  
% 3.03/1.06  ------ Debug Options
% 3.03/1.06  
% 3.03/1.06  --dbg_backtrace                         false
% 3.03/1.06  --dbg_dump_prop_clauses                 false
% 3.03/1.06  --dbg_dump_prop_clauses_file            -
% 3.03/1.06  --dbg_out_stat                          false
% 3.03/1.06  
% 3.03/1.06  
% 3.03/1.06  
% 3.03/1.06  
% 3.03/1.06  ------ Proving...
% 3.03/1.06  
% 3.03/1.06  
% 3.03/1.06  % SZS status Theorem for theBenchmark.p
% 3.03/1.06  
% 3.03/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/1.06  
% 3.03/1.06  fof(f18,conjecture,(
% 3.03/1.06    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.03/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.06  
% 3.03/1.06  fof(f19,negated_conjecture,(
% 3.03/1.06    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.03/1.06    inference(negated_conjecture,[],[f18])).
% 3.03/1.06  
% 3.03/1.06  fof(f25,plain,(
% 3.03/1.06    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.03/1.06    inference(ennf_transformation,[],[f19])).
% 3.03/1.06  
% 3.03/1.06  fof(f36,plain,(
% 3.03/1.06    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3))),
% 3.03/1.06    introduced(choice_axiom,[])).
% 3.03/1.06  
% 3.03/1.06  fof(f37,plain,(
% 3.03/1.06    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3)),
% 3.03/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f36])).
% 3.03/1.06  
% 3.03/1.06  fof(f62,plain,(
% 3.03/1.06    r2_hidden(sK2,sK3)),
% 3.03/1.06    inference(cnf_transformation,[],[f37])).
% 3.03/1.06  
% 3.03/1.06  fof(f17,axiom,(
% 3.03/1.06    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.03/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.06  
% 3.03/1.06  fof(f34,plain,(
% 3.03/1.06    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.03/1.07    inference(nnf_transformation,[],[f17])).
% 3.03/1.07  
% 3.03/1.07  fof(f35,plain,(
% 3.03/1.07    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.03/1.07    inference(flattening,[],[f34])).
% 3.03/1.07  
% 3.03/1.07  fof(f61,plain,(
% 3.03/1.07    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f35])).
% 3.03/1.07  
% 3.03/1.07  fof(f13,axiom,(
% 3.03/1.07    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f55,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f13])).
% 3.03/1.07  
% 3.03/1.07  fof(f14,axiom,(
% 3.03/1.07    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f56,plain,(
% 3.03/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f14])).
% 3.03/1.07  
% 3.03/1.07  fof(f15,axiom,(
% 3.03/1.07    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f57,plain,(
% 3.03/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f15])).
% 3.03/1.07  
% 3.03/1.07  fof(f64,plain,(
% 3.03/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.03/1.07    inference(definition_unfolding,[],[f56,f57])).
% 3.03/1.07  
% 3.03/1.07  fof(f65,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.03/1.07    inference(definition_unfolding,[],[f55,f64])).
% 3.03/1.07  
% 3.03/1.07  fof(f72,plain,(
% 3.03/1.07    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.03/1.07    inference(definition_unfolding,[],[f61,f65])).
% 3.03/1.07  
% 3.03/1.07  fof(f8,axiom,(
% 3.03/1.07    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f24,plain,(
% 3.03/1.07    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.03/1.07    inference(ennf_transformation,[],[f8])).
% 3.03/1.07  
% 3.03/1.07  fof(f50,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f24])).
% 3.03/1.07  
% 3.03/1.07  fof(f9,axiom,(
% 3.03/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f51,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.03/1.07    inference(cnf_transformation,[],[f9])).
% 3.03/1.07  
% 3.03/1.07  fof(f16,axiom,(
% 3.03/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f58,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.03/1.07    inference(cnf_transformation,[],[f16])).
% 3.03/1.07  
% 3.03/1.07  fof(f66,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.03/1.07    inference(definition_unfolding,[],[f58,f65])).
% 3.03/1.07  
% 3.03/1.07  fof(f6,axiom,(
% 3.03/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f48,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.03/1.07    inference(cnf_transformation,[],[f6])).
% 3.03/1.07  
% 3.03/1.07  fof(f70,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.03/1.07    inference(definition_unfolding,[],[f51,f66,f66,f48])).
% 3.03/1.07  
% 3.03/1.07  fof(f7,axiom,(
% 3.03/1.07    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f49,plain,(
% 3.03/1.07    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.03/1.07    inference(cnf_transformation,[],[f7])).
% 3.03/1.07  
% 3.03/1.07  fof(f69,plain,(
% 3.03/1.07    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.03/1.07    inference(definition_unfolding,[],[f49,f66])).
% 3.03/1.07  
% 3.03/1.07  fof(f11,axiom,(
% 3.03/1.07    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f53,plain,(
% 3.03/1.07    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f11])).
% 3.03/1.07  
% 3.03/1.07  fof(f2,axiom,(
% 3.03/1.07    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f21,plain,(
% 3.03/1.07    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.03/1.07    inference(ennf_transformation,[],[f2])).
% 3.03/1.07  
% 3.03/1.07  fof(f26,plain,(
% 3.03/1.07    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.03/1.07    inference(nnf_transformation,[],[f21])).
% 3.03/1.07  
% 3.03/1.07  fof(f27,plain,(
% 3.03/1.07    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.03/1.07    inference(rectify,[],[f26])).
% 3.03/1.07  
% 3.03/1.07  fof(f28,plain,(
% 3.03/1.07    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.03/1.07    introduced(choice_axiom,[])).
% 3.03/1.07  
% 3.03/1.07  fof(f29,plain,(
% 3.03/1.07    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.03/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.03/1.07  
% 3.03/1.07  fof(f40,plain,(
% 3.03/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f29])).
% 3.03/1.07  
% 3.03/1.07  fof(f5,axiom,(
% 3.03/1.07    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f32,plain,(
% 3.03/1.07    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/1.07    inference(nnf_transformation,[],[f5])).
% 3.03/1.07  
% 3.03/1.07  fof(f33,plain,(
% 3.03/1.07    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/1.07    inference(flattening,[],[f32])).
% 3.03/1.07  
% 3.03/1.07  fof(f45,plain,(
% 3.03/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.03/1.07    inference(cnf_transformation,[],[f33])).
% 3.03/1.07  
% 3.03/1.07  fof(f77,plain,(
% 3.03/1.07    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.03/1.07    inference(equality_resolution,[],[f45])).
% 3.03/1.07  
% 3.03/1.07  fof(f4,axiom,(
% 3.03/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f20,plain,(
% 3.03/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.03/1.07    inference(rectify,[],[f4])).
% 3.03/1.07  
% 3.03/1.07  fof(f23,plain,(
% 3.03/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.03/1.07    inference(ennf_transformation,[],[f20])).
% 3.03/1.07  
% 3.03/1.07  fof(f30,plain,(
% 3.03/1.07    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.03/1.07    introduced(choice_axiom,[])).
% 3.03/1.07  
% 3.03/1.07  fof(f31,plain,(
% 3.03/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.03/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f30])).
% 3.03/1.07  
% 3.03/1.07  fof(f44,plain,(
% 3.03/1.07    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.03/1.07    inference(cnf_transformation,[],[f31])).
% 3.03/1.07  
% 3.03/1.07  fof(f1,axiom,(
% 3.03/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f38,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f1])).
% 3.03/1.07  
% 3.03/1.07  fof(f68,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 3.03/1.07    inference(definition_unfolding,[],[f38,f66,f66])).
% 3.03/1.07  
% 3.03/1.07  fof(f10,axiom,(
% 3.03/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f52,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f10])).
% 3.03/1.07  
% 3.03/1.07  fof(f71,plain,(
% 3.03/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 3.03/1.07    inference(definition_unfolding,[],[f52,f48,f48,f66])).
% 3.03/1.07  
% 3.03/1.07  fof(f63,plain,(
% 3.03/1.07    k2_xboole_0(k1_tarski(sK2),sK3) != sK3),
% 3.03/1.07    inference(cnf_transformation,[],[f37])).
% 3.03/1.07  
% 3.03/1.07  fof(f12,axiom,(
% 3.03/1.07    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.03/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.07  
% 3.03/1.07  fof(f54,plain,(
% 3.03/1.07    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.03/1.07    inference(cnf_transformation,[],[f12])).
% 3.03/1.07  
% 3.03/1.07  fof(f67,plain,(
% 3.03/1.07    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.03/1.07    inference(definition_unfolding,[],[f54,f65])).
% 3.03/1.07  
% 3.03/1.07  fof(f75,plain,(
% 3.03/1.07    k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3),
% 3.03/1.07    inference(definition_unfolding,[],[f63,f66,f67])).
% 3.03/1.07  
% 3.03/1.07  cnf(c_19,negated_conjecture,
% 3.03/1.07      ( r2_hidden(sK2,sK3) ),
% 3.03/1.07      inference(cnf_transformation,[],[f62]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_546,plain,
% 3.03/1.07      ( r2_hidden(sK2,sK3) = iProver_top ),
% 3.03/1.07      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_15,plain,
% 3.03/1.07      ( ~ r2_hidden(X0,X1)
% 3.03/1.07      | ~ r2_hidden(X2,X1)
% 3.03/1.07      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 3.03/1.07      inference(cnf_transformation,[],[f72]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_549,plain,
% 3.03/1.07      ( r2_hidden(X0,X1) != iProver_top
% 3.03/1.07      | r2_hidden(X2,X1) != iProver_top
% 3.03/1.07      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
% 3.03/1.07      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_11,plain,
% 3.03/1.07      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.03/1.07      inference(cnf_transformation,[],[f50]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_551,plain,
% 3.03/1.07      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.03/1.07      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_2229,plain,
% 3.03/1.07      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 3.03/1.07      | r2_hidden(X1,X2) != iProver_top
% 3.03/1.07      | r2_hidden(X0,X2) != iProver_top ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_549,c_551]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_5612,plain,
% 3.03/1.07      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,X0),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,X0)
% 3.03/1.07      | r2_hidden(X0,sK3) != iProver_top ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_546,c_2229]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_5782,plain,
% 3.03/1.07      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_546,c_5612]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_12,plain,
% 3.03/1.07      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.03/1.07      inference(cnf_transformation,[],[f70]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_6607,plain,
% 3.03/1.07      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_5782,c_12]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_10,plain,
% 3.03/1.07      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.03/1.07      inference(cnf_transformation,[],[f69]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_14,plain,
% 3.03/1.07      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.03/1.07      inference(cnf_transformation,[],[f53]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_550,plain,
% 3.03/1.07      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.03/1.07      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_2,plain,
% 3.03/1.07      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.03/1.07      inference(cnf_transformation,[],[f40]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_558,plain,
% 3.03/1.07      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.03/1.07      | r1_tarski(X0,X1) = iProver_top ),
% 3.03/1.07      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_9,plain,
% 3.03/1.07      ( r1_tarski(X0,X0) ),
% 3.03/1.07      inference(cnf_transformation,[],[f77]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_552,plain,
% 3.03/1.07      ( r1_tarski(X0,X0) = iProver_top ),
% 3.03/1.07      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_728,plain,
% 3.03/1.07      ( k3_xboole_0(X0,X0) = X0 ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_552,c_551]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_5,plain,
% 3.03/1.07      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.03/1.07      inference(cnf_transformation,[],[f44]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_555,plain,
% 3.03/1.07      ( r1_xboole_0(X0,X1) != iProver_top
% 3.03/1.07      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 3.03/1.07      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_1639,plain,
% 3.03/1.07      ( r1_xboole_0(X0,X0) != iProver_top
% 3.03/1.07      | r2_hidden(X1,X0) != iProver_top ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_728,c_555]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_1720,plain,
% 3.03/1.07      ( r1_xboole_0(X0,X0) != iProver_top
% 3.03/1.07      | r1_tarski(X0,X1) = iProver_top ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_558,c_1639]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_1904,plain,
% 3.03/1.07      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_550,c_1720]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_2030,plain,
% 3.03/1.07      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_1904,c_551]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_0,plain,
% 3.03/1.07      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 3.03/1.07      inference(cnf_transformation,[],[f68]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_829,plain,
% 3.03/1.07      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_13,plain,
% 3.03/1.07      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.03/1.07      inference(cnf_transformation,[],[f71]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_955,plain,
% 3.03/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_829,c_13]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_964,plain,
% 3.03/1.07      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 3.03/1.07      inference(light_normalisation,[status(thm)],[c_955,c_728]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_2034,plain,
% 3.03/1.07      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.03/1.07      inference(demodulation,[status(thm)],[c_2030,c_964]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_959,plain,
% 3.03/1.07      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_829,c_12]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_960,plain,
% 3.03/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.03/1.07      inference(light_normalisation,[status(thm)],[c_959,c_829]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_1003,plain,
% 3.03/1.07      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.03/1.07      inference(superposition,[status(thm)],[c_728,c_960]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_2036,plain,
% 3.03/1.07      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.03/1.07      inference(light_normalisation,[status(thm)],[c_2034,c_1003]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_6609,plain,
% 3.03/1.07      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 3.03/1.07      inference(demodulation,[status(thm)],[c_6607,c_10,c_2036]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_18,negated_conjecture,
% 3.03/1.07      ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
% 3.03/1.07      inference(cnf_transformation,[],[f75]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(c_828,plain,
% 3.03/1.07      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != sK3 ),
% 3.03/1.07      inference(demodulation,[status(thm)],[c_0,c_18]) ).
% 3.03/1.07  
% 3.03/1.07  cnf(contradiction,plain,
% 3.03/1.07      ( $false ),
% 3.03/1.07      inference(minisat,[status(thm)],[c_6609,c_828]) ).
% 3.03/1.07  
% 3.03/1.07  
% 3.03/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/1.07  
% 3.03/1.07  ------                               Statistics
% 3.03/1.07  
% 3.03/1.07  ------ General
% 3.03/1.07  
% 3.03/1.07  abstr_ref_over_cycles:                  0
% 3.03/1.07  abstr_ref_under_cycles:                 0
% 3.03/1.07  gc_basic_clause_elim:                   0
% 3.03/1.07  forced_gc_time:                         0
% 3.03/1.07  parsing_time:                           0.007
% 3.03/1.07  unif_index_cands_time:                  0.
% 3.03/1.07  unif_index_add_time:                    0.
% 3.03/1.07  orderings_time:                         0.
% 3.03/1.07  out_proof_time:                         0.007
% 3.03/1.07  total_time:                             0.224
% 3.03/1.07  num_of_symbols:                         43
% 3.03/1.07  num_of_terms:                           6473
% 3.03/1.07  
% 3.03/1.07  ------ Preprocessing
% 3.03/1.07  
% 3.03/1.07  num_of_splits:                          0
% 3.03/1.07  num_of_split_atoms:                     0
% 3.03/1.07  num_of_reused_defs:                     0
% 3.03/1.07  num_eq_ax_congr_red:                    21
% 3.03/1.07  num_of_sem_filtered_clauses:            1
% 3.03/1.07  num_of_subtypes:                        0
% 3.03/1.07  monotx_restored_types:                  0
% 3.03/1.07  sat_num_of_epr_types:                   0
% 3.03/1.07  sat_num_of_non_cyclic_types:            0
% 3.03/1.07  sat_guarded_non_collapsed_types:        0
% 3.03/1.07  num_pure_diseq_elim:                    0
% 3.03/1.07  simp_replaced_by:                       0
% 3.03/1.07  res_preprocessed:                       95
% 3.03/1.07  prep_upred:                             0
% 3.03/1.07  prep_unflattend:                        0
% 3.03/1.07  smt_new_axioms:                         0
% 3.03/1.07  pred_elim_cands:                        3
% 3.03/1.07  pred_elim:                              0
% 3.03/1.07  pred_elim_cl:                           0
% 3.03/1.07  pred_elim_cycles:                       2
% 3.03/1.07  merged_defs:                            0
% 3.03/1.07  merged_defs_ncl:                        0
% 3.03/1.07  bin_hyper_res:                          0
% 3.03/1.07  prep_cycles:                            4
% 3.03/1.07  pred_elim_time:                         0.
% 3.03/1.07  splitting_time:                         0.
% 3.03/1.07  sem_filter_time:                        0.
% 3.03/1.07  monotx_time:                            0.
% 3.03/1.07  subtype_inf_time:                       0.
% 3.03/1.07  
% 3.03/1.07  ------ Problem properties
% 3.03/1.07  
% 3.03/1.07  clauses:                                19
% 3.03/1.07  conjectures:                            2
% 3.03/1.07  epr:                                    6
% 3.03/1.07  horn:                                   17
% 3.03/1.07  ground:                                 2
% 3.03/1.07  unary:                                  8
% 3.03/1.07  binary:                                 8
% 3.03/1.07  lits:                                   33
% 3.03/1.07  lits_eq:                                7
% 3.03/1.07  fd_pure:                                0
% 3.03/1.07  fd_pseudo:                              0
% 3.03/1.07  fd_cond:                                0
% 3.03/1.07  fd_pseudo_cond:                         1
% 3.03/1.07  ac_symbols:                             0
% 3.03/1.07  
% 3.03/1.07  ------ Propositional Solver
% 3.03/1.07  
% 3.03/1.07  prop_solver_calls:                      30
% 3.03/1.07  prop_fast_solver_calls:                 495
% 3.03/1.07  smt_solver_calls:                       0
% 3.03/1.07  smt_fast_solver_calls:                  0
% 3.03/1.07  prop_num_of_clauses:                    2068
% 3.03/1.07  prop_preprocess_simplified:             5827
% 3.03/1.07  prop_fo_subsumed:                       1
% 3.03/1.07  prop_solver_time:                       0.
% 3.03/1.07  smt_solver_time:                        0.
% 3.03/1.07  smt_fast_solver_time:                   0.
% 3.03/1.07  prop_fast_solver_time:                  0.
% 3.03/1.07  prop_unsat_core_time:                   0.
% 3.03/1.07  
% 3.03/1.07  ------ QBF
% 3.03/1.07  
% 3.03/1.07  qbf_q_res:                              0
% 3.03/1.07  qbf_num_tautologies:                    0
% 3.03/1.07  qbf_prep_cycles:                        0
% 3.03/1.07  
% 3.03/1.07  ------ BMC1
% 3.03/1.07  
% 3.03/1.07  bmc1_current_bound:                     -1
% 3.03/1.07  bmc1_last_solved_bound:                 -1
% 3.03/1.07  bmc1_unsat_core_size:                   -1
% 3.03/1.07  bmc1_unsat_core_parents_size:           -1
% 3.03/1.07  bmc1_merge_next_fun:                    0
% 3.03/1.07  bmc1_unsat_core_clauses_time:           0.
% 3.03/1.07  
% 3.03/1.07  ------ Instantiation
% 3.03/1.07  
% 3.03/1.07  inst_num_of_clauses:                    593
% 3.03/1.07  inst_num_in_passive:                    274
% 3.03/1.07  inst_num_in_active:                     240
% 3.03/1.07  inst_num_in_unprocessed:                79
% 3.03/1.07  inst_num_of_loops:                      390
% 3.03/1.07  inst_num_of_learning_restarts:          0
% 3.03/1.07  inst_num_moves_active_passive:          146
% 3.03/1.07  inst_lit_activity:                      0
% 3.03/1.07  inst_lit_activity_moves:                0
% 3.03/1.07  inst_num_tautologies:                   0
% 3.03/1.07  inst_num_prop_implied:                  0
% 3.03/1.07  inst_num_existing_simplified:           0
% 3.03/1.07  inst_num_eq_res_simplified:             0
% 3.03/1.07  inst_num_child_elim:                    0
% 3.03/1.07  inst_num_of_dismatching_blockings:      335
% 3.03/1.07  inst_num_of_non_proper_insts:           754
% 3.03/1.07  inst_num_of_duplicates:                 0
% 3.03/1.07  inst_inst_num_from_inst_to_res:         0
% 3.03/1.07  inst_dismatching_checking_time:         0.
% 3.03/1.07  
% 3.03/1.07  ------ Resolution
% 3.03/1.07  
% 3.03/1.07  res_num_of_clauses:                     0
% 3.03/1.07  res_num_in_passive:                     0
% 3.03/1.07  res_num_in_active:                      0
% 3.03/1.07  res_num_of_loops:                       99
% 3.03/1.07  res_forward_subset_subsumed:            78
% 3.03/1.07  res_backward_subset_subsumed:           0
% 3.03/1.07  res_forward_subsumed:                   0
% 3.03/1.07  res_backward_subsumed:                  0
% 3.03/1.07  res_forward_subsumption_resolution:     0
% 3.03/1.07  res_backward_subsumption_resolution:    0
% 3.03/1.07  res_clause_to_clause_subsumption:       1098
% 3.03/1.07  res_orphan_elimination:                 0
% 3.03/1.07  res_tautology_del:                      47
% 3.03/1.07  res_num_eq_res_simplified:              0
% 3.03/1.07  res_num_sel_changes:                    0
% 3.03/1.07  res_moves_from_active_to_pass:          0
% 3.03/1.07  
% 3.03/1.07  ------ Superposition
% 3.03/1.07  
% 3.03/1.07  sup_time_total:                         0.
% 3.03/1.07  sup_time_generating:                    0.
% 3.03/1.07  sup_time_sim_full:                      0.
% 3.03/1.07  sup_time_sim_immed:                     0.
% 3.03/1.07  
% 3.03/1.07  sup_num_of_clauses:                     142
% 3.03/1.07  sup_num_in_active:                      71
% 3.03/1.07  sup_num_in_passive:                     71
% 3.03/1.07  sup_num_of_loops:                       76
% 3.03/1.07  sup_fw_superposition:                   642
% 3.03/1.07  sup_bw_superposition:                   285
% 3.03/1.07  sup_immediate_simplified:               345
% 3.03/1.07  sup_given_eliminated:                   1
% 3.03/1.07  comparisons_done:                       0
% 3.03/1.07  comparisons_avoided:                    0
% 3.03/1.07  
% 3.03/1.07  ------ Simplifications
% 3.03/1.07  
% 3.03/1.07  
% 3.03/1.07  sim_fw_subset_subsumed:                 6
% 3.03/1.07  sim_bw_subset_subsumed:                 0
% 3.03/1.07  sim_fw_subsumed:                        44
% 3.03/1.07  sim_bw_subsumed:                        0
% 3.03/1.07  sim_fw_subsumption_res:                 0
% 3.03/1.07  sim_bw_subsumption_res:                 0
% 3.03/1.07  sim_tautology_del:                      9
% 3.03/1.07  sim_eq_tautology_del:                   114
% 3.03/1.07  sim_eq_res_simp:                        0
% 3.03/1.07  sim_fw_demodulated:                     127
% 3.03/1.07  sim_bw_demodulated:                     9
% 3.03/1.07  sim_light_normalised:                   208
% 3.03/1.07  sim_joinable_taut:                      0
% 3.03/1.07  sim_joinable_simp:                      0
% 3.03/1.07  sim_ac_normalised:                      0
% 3.03/1.07  sim_smt_subsumption:                    0
% 3.03/1.07  
%------------------------------------------------------------------------------
