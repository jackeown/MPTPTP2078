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
% DateTime   : Thu Dec  3 11:38:44 EST 2020

% Result     : Theorem 11.75s
% Output     : CNFRefutation 11.75s
% Verified   : 
% Statistics : Number of formulae       :  140 (1190 expanded)
%              Number of clauses        :   78 ( 389 expanded)
%              Number of leaves         :   19 ( 290 expanded)
%              Depth                    :   23
%              Number of atoms          :  249 (2389 expanded)
%              Number of equality atoms :  107 ( 904 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f42,f42])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f41,f42,f42,f42,f42])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31])).

fof(f58,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f55,f61])).

fof(f57,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f56,f42,f61])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_918,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_916,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1944,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_918,c_916])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1678,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_26080,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1944,c_1678])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_922,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_927,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3887,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_922,c_927])).

cnf(c_1943,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_922,c_916])).

cnf(c_3904,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3887,c_1943])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1796,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_912,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1945,plain,
    ( k4_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_912,c_916])).

cnf(c_2199,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) ),
    inference(superposition,[status(thm)],[c_1945,c_8])).

cnf(c_2545,plain,
    ( k5_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) = k4_xboole_0(X0,k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_2199,c_1678])).

cnf(c_4591,plain,
    ( k5_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) = X0 ),
    inference(demodulation,[status(thm)],[c_2545,c_1943,c_3904])).

cnf(c_4594,plain,
    ( k5_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_4591])).

cnf(c_5830,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) = X0 ),
    inference(superposition,[status(thm)],[c_1796,c_4594])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_926,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2938,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_926])).

cnf(c_3235,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_2938,c_916])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_915,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_911,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_925,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4612,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_925])).

cnf(c_4999,plain,
    ( k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = X0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_4612])).

cnf(c_5150,plain,
    ( k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_2938,c_4999])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_282,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | k2_enumset1(sK4,sK4,sK4,sK4) != X2
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_283,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_910,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_2939,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_926])).

cnf(c_5171,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5150,c_2939])).

cnf(c_5569,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5171,c_927])).

cnf(c_5571,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_5171,c_916])).

cnf(c_5572,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5569,c_5571])).

cnf(c_5833,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5830,c_1943,c_3235,c_3904,c_5572])).

cnf(c_26260,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_26080,c_3904,c_5833])).

cnf(c_1946,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_910,c_916])).

cnf(c_1807,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_9443,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_1946,c_1807])).

cnf(c_9458,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_5150,c_1807])).

cnf(c_1677,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_918])).

cnf(c_2538,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))),k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2199,c_1677])).

cnf(c_4450,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2538,c_1943,c_3904])).

cnf(c_4454,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_4450])).

cnf(c_5152,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))) ),
    inference(superposition,[status(thm)],[c_4454,c_4999])).

cnf(c_5153,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))) ),
    inference(light_normalisation,[status(thm)],[c_5152,c_1945])).

cnf(c_5154,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5153,c_1943,c_3904])).

cnf(c_5746,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_5154,c_1796])).

cnf(c_5356,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_5154,c_8])).

cnf(c_5376,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_5356,c_1943])).

cnf(c_5859,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5746,c_5376])).

cnf(c_5860,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5859,c_1943,c_3904])).

cnf(c_9590,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9458,c_5572,c_5860])).

cnf(c_9608,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9443,c_1807,c_9590])).

cnf(c_30663,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_26260,c_9608])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1875,plain,
    ( r1_xboole_0(sK2,sK1)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1214,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1023,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_968,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30663,c_1875,c_1214,c_1023,c_968,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:36:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.75/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.75/1.99  
% 11.75/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.75/1.99  
% 11.75/1.99  ------  iProver source info
% 11.75/1.99  
% 11.75/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.75/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.75/1.99  git: non_committed_changes: false
% 11.75/1.99  git: last_make_outside_of_git: false
% 11.75/1.99  
% 11.75/1.99  ------ 
% 11.75/1.99  
% 11.75/1.99  ------ Input Options
% 11.75/1.99  
% 11.75/1.99  --out_options                           all
% 11.75/1.99  --tptp_safe_out                         true
% 11.75/1.99  --problem_path                          ""
% 11.75/1.99  --include_path                          ""
% 11.75/1.99  --clausifier                            res/vclausify_rel
% 11.75/1.99  --clausifier_options                    ""
% 11.75/1.99  --stdin                                 false
% 11.75/1.99  --stats_out                             all
% 11.75/1.99  
% 11.75/1.99  ------ General Options
% 11.75/1.99  
% 11.75/1.99  --fof                                   false
% 11.75/1.99  --time_out_real                         305.
% 11.75/1.99  --time_out_virtual                      -1.
% 11.75/1.99  --symbol_type_check                     false
% 11.75/1.99  --clausify_out                          false
% 11.75/1.99  --sig_cnt_out                           false
% 11.75/1.99  --trig_cnt_out                          false
% 11.75/1.99  --trig_cnt_out_tolerance                1.
% 11.75/1.99  --trig_cnt_out_sk_spl                   false
% 11.75/1.99  --abstr_cl_out                          false
% 11.75/1.99  
% 11.75/1.99  ------ Global Options
% 11.75/1.99  
% 11.75/1.99  --schedule                              default
% 11.75/1.99  --add_important_lit                     false
% 11.75/1.99  --prop_solver_per_cl                    1000
% 11.75/1.99  --min_unsat_core                        false
% 11.75/1.99  --soft_assumptions                      false
% 11.75/1.99  --soft_lemma_size                       3
% 11.75/1.99  --prop_impl_unit_size                   0
% 11.75/1.99  --prop_impl_unit                        []
% 11.75/1.99  --share_sel_clauses                     true
% 11.75/1.99  --reset_solvers                         false
% 11.75/1.99  --bc_imp_inh                            [conj_cone]
% 11.75/1.99  --conj_cone_tolerance                   3.
% 11.75/1.99  --extra_neg_conj                        none
% 11.75/1.99  --large_theory_mode                     true
% 11.75/1.99  --prolific_symb_bound                   200
% 11.75/1.99  --lt_threshold                          2000
% 11.75/1.99  --clause_weak_htbl                      true
% 11.75/1.99  --gc_record_bc_elim                     false
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing Options
% 11.75/1.99  
% 11.75/1.99  --preprocessing_flag                    true
% 11.75/1.99  --time_out_prep_mult                    0.1
% 11.75/1.99  --splitting_mode                        input
% 11.75/1.99  --splitting_grd                         true
% 11.75/1.99  --splitting_cvd                         false
% 11.75/1.99  --splitting_cvd_svl                     false
% 11.75/1.99  --splitting_nvd                         32
% 11.75/1.99  --sub_typing                            true
% 11.75/1.99  --prep_gs_sim                           true
% 11.75/1.99  --prep_unflatten                        true
% 11.75/1.99  --prep_res_sim                          true
% 11.75/1.99  --prep_upred                            true
% 11.75/1.99  --prep_sem_filter                       exhaustive
% 11.75/1.99  --prep_sem_filter_out                   false
% 11.75/1.99  --pred_elim                             true
% 11.75/1.99  --res_sim_input                         true
% 11.75/1.99  --eq_ax_congr_red                       true
% 11.75/1.99  --pure_diseq_elim                       true
% 11.75/1.99  --brand_transform                       false
% 11.75/1.99  --non_eq_to_eq                          false
% 11.75/1.99  --prep_def_merge                        true
% 11.75/1.99  --prep_def_merge_prop_impl              false
% 11.75/1.99  --prep_def_merge_mbd                    true
% 11.75/1.99  --prep_def_merge_tr_red                 false
% 11.75/1.99  --prep_def_merge_tr_cl                  false
% 11.75/1.99  --smt_preprocessing                     true
% 11.75/1.99  --smt_ac_axioms                         fast
% 11.75/1.99  --preprocessed_out                      false
% 11.75/1.99  --preprocessed_stats                    false
% 11.75/1.99  
% 11.75/1.99  ------ Abstraction refinement Options
% 11.75/1.99  
% 11.75/1.99  --abstr_ref                             []
% 11.75/1.99  --abstr_ref_prep                        false
% 11.75/1.99  --abstr_ref_until_sat                   false
% 11.75/1.99  --abstr_ref_sig_restrict                funpre
% 11.75/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.75/1.99  --abstr_ref_under                       []
% 11.75/1.99  
% 11.75/1.99  ------ SAT Options
% 11.75/1.99  
% 11.75/1.99  --sat_mode                              false
% 11.75/1.99  --sat_fm_restart_options                ""
% 11.75/1.99  --sat_gr_def                            false
% 11.75/1.99  --sat_epr_types                         true
% 11.75/1.99  --sat_non_cyclic_types                  false
% 11.75/1.99  --sat_finite_models                     false
% 11.75/1.99  --sat_fm_lemmas                         false
% 11.75/1.99  --sat_fm_prep                           false
% 11.75/1.99  --sat_fm_uc_incr                        true
% 11.75/1.99  --sat_out_model                         small
% 11.75/1.99  --sat_out_clauses                       false
% 11.75/1.99  
% 11.75/1.99  ------ QBF Options
% 11.75/1.99  
% 11.75/1.99  --qbf_mode                              false
% 11.75/1.99  --qbf_elim_univ                         false
% 11.75/1.99  --qbf_dom_inst                          none
% 11.75/1.99  --qbf_dom_pre_inst                      false
% 11.75/1.99  --qbf_sk_in                             false
% 11.75/1.99  --qbf_pred_elim                         true
% 11.75/1.99  --qbf_split                             512
% 11.75/1.99  
% 11.75/1.99  ------ BMC1 Options
% 11.75/1.99  
% 11.75/1.99  --bmc1_incremental                      false
% 11.75/1.99  --bmc1_axioms                           reachable_all
% 11.75/1.99  --bmc1_min_bound                        0
% 11.75/1.99  --bmc1_max_bound                        -1
% 11.75/1.99  --bmc1_max_bound_default                -1
% 11.75/1.99  --bmc1_symbol_reachability              true
% 11.75/1.99  --bmc1_property_lemmas                  false
% 11.75/1.99  --bmc1_k_induction                      false
% 11.75/1.99  --bmc1_non_equiv_states                 false
% 11.75/1.99  --bmc1_deadlock                         false
% 11.75/1.99  --bmc1_ucm                              false
% 11.75/1.99  --bmc1_add_unsat_core                   none
% 11.75/1.99  --bmc1_unsat_core_children              false
% 11.75/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.75/1.99  --bmc1_out_stat                         full
% 11.75/1.99  --bmc1_ground_init                      false
% 11.75/1.99  --bmc1_pre_inst_next_state              false
% 11.75/1.99  --bmc1_pre_inst_state                   false
% 11.75/1.99  --bmc1_pre_inst_reach_state             false
% 11.75/1.99  --bmc1_out_unsat_core                   false
% 11.75/1.99  --bmc1_aig_witness_out                  false
% 11.75/1.99  --bmc1_verbose                          false
% 11.75/1.99  --bmc1_dump_clauses_tptp                false
% 11.75/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.75/1.99  --bmc1_dump_file                        -
% 11.75/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.75/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.75/1.99  --bmc1_ucm_extend_mode                  1
% 11.75/1.99  --bmc1_ucm_init_mode                    2
% 11.75/1.99  --bmc1_ucm_cone_mode                    none
% 11.75/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.75/1.99  --bmc1_ucm_relax_model                  4
% 11.75/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.75/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.75/1.99  --bmc1_ucm_layered_model                none
% 11.75/1.99  --bmc1_ucm_max_lemma_size               10
% 11.75/1.99  
% 11.75/1.99  ------ AIG Options
% 11.75/1.99  
% 11.75/1.99  --aig_mode                              false
% 11.75/1.99  
% 11.75/1.99  ------ Instantiation Options
% 11.75/1.99  
% 11.75/1.99  --instantiation_flag                    true
% 11.75/1.99  --inst_sos_flag                         true
% 11.75/1.99  --inst_sos_phase                        true
% 11.75/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.75/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.75/1.99  --inst_lit_sel_side                     num_symb
% 11.75/1.99  --inst_solver_per_active                1400
% 11.75/1.99  --inst_solver_calls_frac                1.
% 11.75/1.99  --inst_passive_queue_type               priority_queues
% 11.75/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.75/1.99  --inst_passive_queues_freq              [25;2]
% 11.75/1.99  --inst_dismatching                      true
% 11.75/1.99  --inst_eager_unprocessed_to_passive     true
% 11.75/1.99  --inst_prop_sim_given                   true
% 11.75/1.99  --inst_prop_sim_new                     false
% 11.75/1.99  --inst_subs_new                         false
% 11.75/1.99  --inst_eq_res_simp                      false
% 11.75/1.99  --inst_subs_given                       false
% 11.75/1.99  --inst_orphan_elimination               true
% 11.75/1.99  --inst_learning_loop_flag               true
% 11.75/1.99  --inst_learning_start                   3000
% 11.75/1.99  --inst_learning_factor                  2
% 11.75/1.99  --inst_start_prop_sim_after_learn       3
% 11.75/1.99  --inst_sel_renew                        solver
% 11.75/1.99  --inst_lit_activity_flag                true
% 11.75/1.99  --inst_restr_to_given                   false
% 11.75/1.99  --inst_activity_threshold               500
% 11.75/1.99  --inst_out_proof                        true
% 11.75/1.99  
% 11.75/1.99  ------ Resolution Options
% 11.75/1.99  
% 11.75/1.99  --resolution_flag                       true
% 11.75/1.99  --res_lit_sel                           adaptive
% 11.75/1.99  --res_lit_sel_side                      none
% 11.75/1.99  --res_ordering                          kbo
% 11.75/1.99  --res_to_prop_solver                    active
% 11.75/1.99  --res_prop_simpl_new                    false
% 11.75/1.99  --res_prop_simpl_given                  true
% 11.75/1.99  --res_passive_queue_type                priority_queues
% 11.75/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.75/1.99  --res_passive_queues_freq               [15;5]
% 11.75/1.99  --res_forward_subs                      full
% 11.75/1.99  --res_backward_subs                     full
% 11.75/1.99  --res_forward_subs_resolution           true
% 11.75/1.99  --res_backward_subs_resolution          true
% 11.75/1.99  --res_orphan_elimination                true
% 11.75/1.99  --res_time_limit                        2.
% 11.75/1.99  --res_out_proof                         true
% 11.75/1.99  
% 11.75/1.99  ------ Superposition Options
% 11.75/1.99  
% 11.75/1.99  --superposition_flag                    true
% 11.75/1.99  --sup_passive_queue_type                priority_queues
% 11.75/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.75/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.75/1.99  --demod_completeness_check              fast
% 11.75/1.99  --demod_use_ground                      true
% 11.75/1.99  --sup_to_prop_solver                    passive
% 11.75/1.99  --sup_prop_simpl_new                    true
% 11.75/1.99  --sup_prop_simpl_given                  true
% 11.75/1.99  --sup_fun_splitting                     true
% 11.75/1.99  --sup_smt_interval                      50000
% 11.75/1.99  
% 11.75/1.99  ------ Superposition Simplification Setup
% 11.75/1.99  
% 11.75/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.75/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.75/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.75/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.75/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.75/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.75/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.75/1.99  --sup_immed_triv                        [TrivRules]
% 11.75/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/1.99  --sup_immed_bw_main                     []
% 11.75/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.75/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.75/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/1.99  --sup_input_bw                          []
% 11.75/1.99  
% 11.75/1.99  ------ Combination Options
% 11.75/1.99  
% 11.75/1.99  --comb_res_mult                         3
% 11.75/1.99  --comb_sup_mult                         2
% 11.75/1.99  --comb_inst_mult                        10
% 11.75/1.99  
% 11.75/1.99  ------ Debug Options
% 11.75/1.99  
% 11.75/1.99  --dbg_backtrace                         false
% 11.75/1.99  --dbg_dump_prop_clauses                 false
% 11.75/1.99  --dbg_dump_prop_clauses_file            -
% 11.75/1.99  --dbg_out_stat                          false
% 11.75/1.99  ------ Parsing...
% 11.75/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.75/1.99  ------ Proving...
% 11.75/1.99  ------ Problem Properties 
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  clauses                                 22
% 11.75/1.99  conjectures                             3
% 11.75/1.99  EPR                                     5
% 11.75/1.99  Horn                                    19
% 11.75/1.99  unary                                   9
% 11.75/1.99  binary                                  11
% 11.75/1.99  lits                                    37
% 11.75/1.99  lits eq                                 9
% 11.75/1.99  fd_pure                                 0
% 11.75/1.99  fd_pseudo                               0
% 11.75/1.99  fd_cond                                 0
% 11.75/1.99  fd_pseudo_cond                          0
% 11.75/1.99  AC symbols                              0
% 11.75/1.99  
% 11.75/1.99  ------ Schedule dynamic 5 is on 
% 11.75/1.99  
% 11.75/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  ------ 
% 11.75/1.99  Current options:
% 11.75/1.99  ------ 
% 11.75/1.99  
% 11.75/1.99  ------ Input Options
% 11.75/1.99  
% 11.75/1.99  --out_options                           all
% 11.75/1.99  --tptp_safe_out                         true
% 11.75/1.99  --problem_path                          ""
% 11.75/1.99  --include_path                          ""
% 11.75/1.99  --clausifier                            res/vclausify_rel
% 11.75/1.99  --clausifier_options                    ""
% 11.75/1.99  --stdin                                 false
% 11.75/1.99  --stats_out                             all
% 11.75/1.99  
% 11.75/1.99  ------ General Options
% 11.75/1.99  
% 11.75/1.99  --fof                                   false
% 11.75/1.99  --time_out_real                         305.
% 11.75/1.99  --time_out_virtual                      -1.
% 11.75/1.99  --symbol_type_check                     false
% 11.75/1.99  --clausify_out                          false
% 11.75/1.99  --sig_cnt_out                           false
% 11.75/1.99  --trig_cnt_out                          false
% 11.75/1.99  --trig_cnt_out_tolerance                1.
% 11.75/1.99  --trig_cnt_out_sk_spl                   false
% 11.75/1.99  --abstr_cl_out                          false
% 11.75/1.99  
% 11.75/1.99  ------ Global Options
% 11.75/1.99  
% 11.75/1.99  --schedule                              default
% 11.75/1.99  --add_important_lit                     false
% 11.75/1.99  --prop_solver_per_cl                    1000
% 11.75/1.99  --min_unsat_core                        false
% 11.75/1.99  --soft_assumptions                      false
% 11.75/1.99  --soft_lemma_size                       3
% 11.75/1.99  --prop_impl_unit_size                   0
% 11.75/1.99  --prop_impl_unit                        []
% 11.75/1.99  --share_sel_clauses                     true
% 11.75/1.99  --reset_solvers                         false
% 11.75/1.99  --bc_imp_inh                            [conj_cone]
% 11.75/1.99  --conj_cone_tolerance                   3.
% 11.75/1.99  --extra_neg_conj                        none
% 11.75/1.99  --large_theory_mode                     true
% 11.75/1.99  --prolific_symb_bound                   200
% 11.75/1.99  --lt_threshold                          2000
% 11.75/1.99  --clause_weak_htbl                      true
% 11.75/1.99  --gc_record_bc_elim                     false
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing Options
% 11.75/1.99  
% 11.75/1.99  --preprocessing_flag                    true
% 11.75/1.99  --time_out_prep_mult                    0.1
% 11.75/1.99  --splitting_mode                        input
% 11.75/1.99  --splitting_grd                         true
% 11.75/1.99  --splitting_cvd                         false
% 11.75/1.99  --splitting_cvd_svl                     false
% 11.75/1.99  --splitting_nvd                         32
% 11.75/1.99  --sub_typing                            true
% 11.75/1.99  --prep_gs_sim                           true
% 11.75/1.99  --prep_unflatten                        true
% 11.75/1.99  --prep_res_sim                          true
% 11.75/1.99  --prep_upred                            true
% 11.75/1.99  --prep_sem_filter                       exhaustive
% 11.75/1.99  --prep_sem_filter_out                   false
% 11.75/1.99  --pred_elim                             true
% 11.75/1.99  --res_sim_input                         true
% 11.75/1.99  --eq_ax_congr_red                       true
% 11.75/1.99  --pure_diseq_elim                       true
% 11.75/1.99  --brand_transform                       false
% 11.75/1.99  --non_eq_to_eq                          false
% 11.75/1.99  --prep_def_merge                        true
% 11.75/1.99  --prep_def_merge_prop_impl              false
% 11.75/1.99  --prep_def_merge_mbd                    true
% 11.75/1.99  --prep_def_merge_tr_red                 false
% 11.75/1.99  --prep_def_merge_tr_cl                  false
% 11.75/1.99  --smt_preprocessing                     true
% 11.75/1.99  --smt_ac_axioms                         fast
% 11.75/1.99  --preprocessed_out                      false
% 11.75/1.99  --preprocessed_stats                    false
% 11.75/1.99  
% 11.75/1.99  ------ Abstraction refinement Options
% 11.75/1.99  
% 11.75/1.99  --abstr_ref                             []
% 11.75/1.99  --abstr_ref_prep                        false
% 11.75/1.99  --abstr_ref_until_sat                   false
% 11.75/1.99  --abstr_ref_sig_restrict                funpre
% 11.75/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.75/1.99  --abstr_ref_under                       []
% 11.75/1.99  
% 11.75/1.99  ------ SAT Options
% 11.75/1.99  
% 11.75/1.99  --sat_mode                              false
% 11.75/1.99  --sat_fm_restart_options                ""
% 11.75/1.99  --sat_gr_def                            false
% 11.75/1.99  --sat_epr_types                         true
% 11.75/1.99  --sat_non_cyclic_types                  false
% 11.75/1.99  --sat_finite_models                     false
% 11.75/1.99  --sat_fm_lemmas                         false
% 11.75/1.99  --sat_fm_prep                           false
% 11.75/1.99  --sat_fm_uc_incr                        true
% 11.75/1.99  --sat_out_model                         small
% 11.75/1.99  --sat_out_clauses                       false
% 11.75/1.99  
% 11.75/1.99  ------ QBF Options
% 11.75/1.99  
% 11.75/1.99  --qbf_mode                              false
% 11.75/1.99  --qbf_elim_univ                         false
% 11.75/1.99  --qbf_dom_inst                          none
% 11.75/1.99  --qbf_dom_pre_inst                      false
% 11.75/1.99  --qbf_sk_in                             false
% 11.75/1.99  --qbf_pred_elim                         true
% 11.75/1.99  --qbf_split                             512
% 11.75/1.99  
% 11.75/1.99  ------ BMC1 Options
% 11.75/1.99  
% 11.75/1.99  --bmc1_incremental                      false
% 11.75/1.99  --bmc1_axioms                           reachable_all
% 11.75/1.99  --bmc1_min_bound                        0
% 11.75/1.99  --bmc1_max_bound                        -1
% 11.75/1.99  --bmc1_max_bound_default                -1
% 11.75/1.99  --bmc1_symbol_reachability              true
% 11.75/1.99  --bmc1_property_lemmas                  false
% 11.75/1.99  --bmc1_k_induction                      false
% 11.75/1.99  --bmc1_non_equiv_states                 false
% 11.75/1.99  --bmc1_deadlock                         false
% 11.75/1.99  --bmc1_ucm                              false
% 11.75/1.99  --bmc1_add_unsat_core                   none
% 11.75/1.99  --bmc1_unsat_core_children              false
% 11.75/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.75/1.99  --bmc1_out_stat                         full
% 11.75/1.99  --bmc1_ground_init                      false
% 11.75/1.99  --bmc1_pre_inst_next_state              false
% 11.75/1.99  --bmc1_pre_inst_state                   false
% 11.75/1.99  --bmc1_pre_inst_reach_state             false
% 11.75/1.99  --bmc1_out_unsat_core                   false
% 11.75/1.99  --bmc1_aig_witness_out                  false
% 11.75/1.99  --bmc1_verbose                          false
% 11.75/1.99  --bmc1_dump_clauses_tptp                false
% 11.75/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.75/1.99  --bmc1_dump_file                        -
% 11.75/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.75/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.75/1.99  --bmc1_ucm_extend_mode                  1
% 11.75/1.99  --bmc1_ucm_init_mode                    2
% 11.75/1.99  --bmc1_ucm_cone_mode                    none
% 11.75/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.75/1.99  --bmc1_ucm_relax_model                  4
% 11.75/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.75/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.75/1.99  --bmc1_ucm_layered_model                none
% 11.75/1.99  --bmc1_ucm_max_lemma_size               10
% 11.75/1.99  
% 11.75/1.99  ------ AIG Options
% 11.75/1.99  
% 11.75/1.99  --aig_mode                              false
% 11.75/1.99  
% 11.75/1.99  ------ Instantiation Options
% 11.75/1.99  
% 11.75/1.99  --instantiation_flag                    true
% 11.75/1.99  --inst_sos_flag                         true
% 11.75/1.99  --inst_sos_phase                        true
% 11.75/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.75/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.75/1.99  --inst_lit_sel_side                     none
% 11.75/1.99  --inst_solver_per_active                1400
% 11.75/1.99  --inst_solver_calls_frac                1.
% 11.75/1.99  --inst_passive_queue_type               priority_queues
% 11.75/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.75/1.99  --inst_passive_queues_freq              [25;2]
% 11.75/1.99  --inst_dismatching                      true
% 11.75/1.99  --inst_eager_unprocessed_to_passive     true
% 11.75/1.99  --inst_prop_sim_given                   true
% 11.75/1.99  --inst_prop_sim_new                     false
% 11.75/1.99  --inst_subs_new                         false
% 11.75/1.99  --inst_eq_res_simp                      false
% 11.75/1.99  --inst_subs_given                       false
% 11.75/1.99  --inst_orphan_elimination               true
% 11.75/1.99  --inst_learning_loop_flag               true
% 11.75/1.99  --inst_learning_start                   3000
% 11.75/1.99  --inst_learning_factor                  2
% 11.75/1.99  --inst_start_prop_sim_after_learn       3
% 11.75/1.99  --inst_sel_renew                        solver
% 11.75/1.99  --inst_lit_activity_flag                true
% 11.75/1.99  --inst_restr_to_given                   false
% 11.75/1.99  --inst_activity_threshold               500
% 11.75/1.99  --inst_out_proof                        true
% 11.75/1.99  
% 11.75/1.99  ------ Resolution Options
% 11.75/1.99  
% 11.75/1.99  --resolution_flag                       false
% 11.75/1.99  --res_lit_sel                           adaptive
% 11.75/1.99  --res_lit_sel_side                      none
% 11.75/1.99  --res_ordering                          kbo
% 11.75/1.99  --res_to_prop_solver                    active
% 11.75/1.99  --res_prop_simpl_new                    false
% 11.75/1.99  --res_prop_simpl_given                  true
% 11.75/1.99  --res_passive_queue_type                priority_queues
% 11.75/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.75/1.99  --res_passive_queues_freq               [15;5]
% 11.75/1.99  --res_forward_subs                      full
% 11.75/1.99  --res_backward_subs                     full
% 11.75/1.99  --res_forward_subs_resolution           true
% 11.75/1.99  --res_backward_subs_resolution          true
% 11.75/1.99  --res_orphan_elimination                true
% 11.75/1.99  --res_time_limit                        2.
% 11.75/1.99  --res_out_proof                         true
% 11.75/1.99  
% 11.75/1.99  ------ Superposition Options
% 11.75/1.99  
% 11.75/1.99  --superposition_flag                    true
% 11.75/1.99  --sup_passive_queue_type                priority_queues
% 11.75/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.75/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.75/1.99  --demod_completeness_check              fast
% 11.75/1.99  --demod_use_ground                      true
% 11.75/1.99  --sup_to_prop_solver                    passive
% 11.75/1.99  --sup_prop_simpl_new                    true
% 11.75/1.99  --sup_prop_simpl_given                  true
% 11.75/1.99  --sup_fun_splitting                     true
% 11.75/1.99  --sup_smt_interval                      50000
% 11.75/1.99  
% 11.75/1.99  ------ Superposition Simplification Setup
% 11.75/1.99  
% 11.75/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.75/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.75/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.75/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.75/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.75/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.75/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.75/1.99  --sup_immed_triv                        [TrivRules]
% 11.75/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/1.99  --sup_immed_bw_main                     []
% 11.75/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.75/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.75/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/1.99  --sup_input_bw                          []
% 11.75/1.99  
% 11.75/1.99  ------ Combination Options
% 11.75/1.99  
% 11.75/1.99  --comb_res_mult                         3
% 11.75/1.99  --comb_sup_mult                         2
% 11.75/1.99  --comb_inst_mult                        10
% 11.75/1.99  
% 11.75/1.99  ------ Debug Options
% 11.75/1.99  
% 11.75/1.99  --dbg_backtrace                         false
% 11.75/1.99  --dbg_dump_prop_clauses                 false
% 11.75/1.99  --dbg_dump_prop_clauses_file            -
% 11.75/1.99  --dbg_out_stat                          false
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  ------ Proving...
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  % SZS status Theorem for theBenchmark.p
% 11.75/1.99  
% 11.75/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.75/1.99  
% 11.75/1.99  fof(f10,axiom,(
% 11.75/1.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f47,plain,(
% 11.75/1.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f10])).
% 11.75/1.99  
% 11.75/1.99  fof(f11,axiom,(
% 11.75/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f29,plain,(
% 11.75/1.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 11.75/1.99    inference(nnf_transformation,[],[f11])).
% 11.75/1.99  
% 11.75/1.99  fof(f48,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f29])).
% 11.75/1.99  
% 11.75/1.99  fof(f1,axiom,(
% 11.75/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f33,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f1])).
% 11.75/1.99  
% 11.75/1.99  fof(f7,axiom,(
% 11.75/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f42,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.75/1.99    inference(cnf_transformation,[],[f7])).
% 11.75/1.99  
% 11.75/1.99  fof(f63,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.75/1.99    inference(definition_unfolding,[],[f33,f42,f42])).
% 11.75/1.99  
% 11.75/1.99  fof(f5,axiom,(
% 11.75/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f40,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.75/1.99    inference(cnf_transformation,[],[f5])).
% 11.75/1.99  
% 11.75/1.99  fof(f62,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.75/1.99    inference(definition_unfolding,[],[f40,f42])).
% 11.75/1.99  
% 11.75/1.99  fof(f8,axiom,(
% 11.75/1.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f43,plain,(
% 11.75/1.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f8])).
% 11.75/1.99  
% 11.75/1.99  fof(f2,axiom,(
% 11.75/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f26,plain,(
% 11.75/1.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.75/1.99    inference(nnf_transformation,[],[f2])).
% 11.75/1.99  
% 11.75/1.99  fof(f34,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f26])).
% 11.75/1.99  
% 11.75/1.99  fof(f65,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.75/1.99    inference(definition_unfolding,[],[f34,f42])).
% 11.75/1.99  
% 11.75/1.99  fof(f6,axiom,(
% 11.75/1.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f41,plain,(
% 11.75/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f6])).
% 11.75/1.99  
% 11.75/1.99  fof(f66,plain,(
% 11.75/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 11.75/1.99    inference(definition_unfolding,[],[f41,f42,f42,f42,f42])).
% 11.75/1.99  
% 11.75/1.99  fof(f17,conjecture,(
% 11.75/1.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f18,negated_conjecture,(
% 11.75/1.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 11.75/1.99    inference(negated_conjecture,[],[f17])).
% 11.75/1.99  
% 11.75/1.99  fof(f24,plain,(
% 11.75/1.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 11.75/1.99    inference(ennf_transformation,[],[f18])).
% 11.75/1.99  
% 11.75/1.99  fof(f25,plain,(
% 11.75/1.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 11.75/1.99    inference(flattening,[],[f24])).
% 11.75/1.99  
% 11.75/1.99  fof(f31,plain,(
% 11.75/1.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 11.75/1.99    introduced(choice_axiom,[])).
% 11.75/1.99  
% 11.75/1.99  fof(f32,plain,(
% 11.75/1.99    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 11.75/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31])).
% 11.75/1.99  
% 11.75/1.99  fof(f58,plain,(
% 11.75/1.99    r1_xboole_0(sK3,sK2)),
% 11.75/1.99    inference(cnf_transformation,[],[f32])).
% 11.75/1.99  
% 11.75/1.99  fof(f3,axiom,(
% 11.75/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f20,plain,(
% 11.75/1.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.75/1.99    inference(ennf_transformation,[],[f3])).
% 11.75/1.99  
% 11.75/1.99  fof(f36,plain,(
% 11.75/1.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f20])).
% 11.75/1.99  
% 11.75/1.99  fof(f16,axiom,(
% 11.75/1.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f30,plain,(
% 11.75/1.99    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 11.75/1.99    inference(nnf_transformation,[],[f16])).
% 11.75/1.99  
% 11.75/1.99  fof(f55,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f30])).
% 11.75/1.99  
% 11.75/1.99  fof(f13,axiom,(
% 11.75/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f51,plain,(
% 11.75/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f13])).
% 11.75/1.99  
% 11.75/1.99  fof(f14,axiom,(
% 11.75/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f52,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f14])).
% 11.75/1.99  
% 11.75/1.99  fof(f15,axiom,(
% 11.75/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f53,plain,(
% 11.75/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f15])).
% 11.75/1.99  
% 11.75/1.99  fof(f60,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.75/1.99    inference(definition_unfolding,[],[f52,f53])).
% 11.75/1.99  
% 11.75/1.99  fof(f61,plain,(
% 11.75/1.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.75/1.99    inference(definition_unfolding,[],[f51,f60])).
% 11.75/1.99  
% 11.75/1.99  fof(f67,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 11.75/1.99    inference(definition_unfolding,[],[f55,f61])).
% 11.75/1.99  
% 11.75/1.99  fof(f57,plain,(
% 11.75/1.99    r2_hidden(sK4,sK3)),
% 11.75/1.99    inference(cnf_transformation,[],[f32])).
% 11.75/1.99  
% 11.75/1.99  fof(f4,axiom,(
% 11.75/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f19,plain,(
% 11.75/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.75/1.99    inference(rectify,[],[f4])).
% 11.75/1.99  
% 11.75/1.99  fof(f21,plain,(
% 11.75/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.75/1.99    inference(ennf_transformation,[],[f19])).
% 11.75/1.99  
% 11.75/1.99  fof(f27,plain,(
% 11.75/1.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.75/1.99    introduced(choice_axiom,[])).
% 11.75/1.99  
% 11.75/1.99  fof(f28,plain,(
% 11.75/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.75/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f27])).
% 11.75/1.99  
% 11.75/1.99  fof(f39,plain,(
% 11.75/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f28])).
% 11.75/1.99  
% 11.75/1.99  fof(f12,axiom,(
% 11.75/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f23,plain,(
% 11.75/1.99    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.75/1.99    inference(ennf_transformation,[],[f12])).
% 11.75/1.99  
% 11.75/1.99  fof(f50,plain,(
% 11.75/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f23])).
% 11.75/1.99  
% 11.75/1.99  fof(f56,plain,(
% 11.75/1.99    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 11.75/1.99    inference(cnf_transformation,[],[f32])).
% 11.75/1.99  
% 11.75/1.99  fof(f69,plain,(
% 11.75/1.99    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),
% 11.75/1.99    inference(definition_unfolding,[],[f56,f42,f61])).
% 11.75/1.99  
% 11.75/1.99  fof(f35,plain,(
% 11.75/1.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.75/1.99    inference(cnf_transformation,[],[f26])).
% 11.75/1.99  
% 11.75/1.99  fof(f64,plain,(
% 11.75/1.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.75/1.99    inference(definition_unfolding,[],[f35,f42])).
% 11.75/1.99  
% 11.75/1.99  fof(f9,axiom,(
% 11.75/1.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 11.75/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f22,plain,(
% 11.75/1.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 11.75/1.99    inference(ennf_transformation,[],[f9])).
% 11.75/1.99  
% 11.75/1.99  fof(f44,plain,(
% 11.75/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 11.75/1.99    inference(cnf_transformation,[],[f22])).
% 11.75/1.99  
% 11.75/1.99  fof(f59,plain,(
% 11.75/1.99    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 11.75/1.99    inference(cnf_transformation,[],[f32])).
% 11.75/1.99  
% 11.75/1.99  cnf(c_13,plain,
% 11.75/1.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_918,plain,
% 11.75/1.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_15,plain,
% 11.75/1.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 11.75/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_916,plain,
% 11.75/1.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1944,plain,
% 11.75/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_918,c_916]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1,plain,
% 11.75/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.75/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_0,plain,
% 11.75/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1678,plain,
% 11.75/1.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_26080,plain,
% 11.75/1.99      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1944,c_1678]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_9,plain,
% 11.75/1.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_922,plain,
% 11.75/1.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_3,plain,
% 11.75/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.75/1.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.75/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_927,plain,
% 11.75/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.75/1.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_3887,plain,
% 11.75/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_922,c_927]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1943,plain,
% 11.75/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_922,c_916]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_3904,plain,
% 11.75/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.75/1.99      inference(light_normalisation,[status(thm)],[c_3887,c_1943]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_8,plain,
% 11.75/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 11.75/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1796,plain,
% 11.75/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_20,negated_conjecture,
% 11.75/1.99      ( r1_xboole_0(sK3,sK2) ),
% 11.75/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_912,plain,
% 11.75/1.99      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1945,plain,
% 11.75/1.99      ( k4_xboole_0(sK3,sK2) = sK3 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_912,c_916]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2199,plain,
% 11.75/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1945,c_8]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2545,plain,
% 11.75/1.99      ( k5_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) = k4_xboole_0(X0,k4_xboole_0(sK3,sK3)) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_2199,c_1678]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4591,plain,
% 11.75/1.99      ( k5_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) = X0 ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_2545,c_1943,c_3904]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4594,plain,
% 11.75/1.99      ( k5_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))) = X0 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1,c_4591]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5830,plain,
% 11.75/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) = X0 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1796,c_4594]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4,plain,
% 11.75/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_926,plain,
% 11.75/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 11.75/1.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2938,plain,
% 11.75/1.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_912,c_926]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_3235,plain,
% 11.75/1.99      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_2938,c_916]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_17,plain,
% 11.75/1.99      ( r2_hidden(X0,X1)
% 11.75/1.99      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 11.75/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_915,plain,
% 11.75/1.99      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 11.75/1.99      | r2_hidden(X1,X0) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_21,negated_conjecture,
% 11.75/1.99      ( r2_hidden(sK4,sK3) ),
% 11.75/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_911,plain,
% 11.75/1.99      ( r2_hidden(sK4,sK3) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5,plain,
% 11.75/1.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_925,plain,
% 11.75/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.75/1.99      | r2_hidden(X0,X2) != iProver_top
% 11.75/1.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4612,plain,
% 11.75/1.99      ( r2_hidden(sK4,X0) != iProver_top
% 11.75/1.99      | r1_xboole_0(X0,sK3) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_911,c_925]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4999,plain,
% 11.75/1.99      ( k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = X0
% 11.75/1.99      | r1_xboole_0(X0,sK3) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_915,c_4612]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5150,plain,
% 11.75/1.99      ( k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = sK2 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_2938,c_4999]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_16,plain,
% 11.75/1.99      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 11.75/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_22,negated_conjecture,
% 11.75/1.99      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 11.75/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_282,plain,
% 11.75/1.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 11.75/1.99      | k2_enumset1(sK4,sK4,sK4,sK4) != X2
% 11.75/1.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X0 ),
% 11.75/1.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_283,plain,
% 11.75/1.99      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 11.75/1.99      inference(unflattening,[status(thm)],[c_282]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_910,plain,
% 11.75/1.99      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2939,plain,
% 11.75/1.99      ( r1_xboole_0(k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_910,c_926]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5171,plain,
% 11.75/1.99      ( r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_5150,c_2939]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5569,plain,
% 11.75/1.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_5171,c_927]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5571,plain,
% 11.75/1.99      ( k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK2 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_5171,c_916]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5572,plain,
% 11.75/1.99      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_5569,c_5571]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5833,plain,
% 11.75/1.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.75/1.99      inference(light_normalisation,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_5830,c_1943,c_3235,c_3904,c_5572]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_26260,plain,
% 11.75/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_26080,c_3904,c_5833]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1946,plain,
% 11.75/1.99      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_910,c_916]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1807,plain,
% 11.75/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_9443,plain,
% 11.75/1.99      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1946,c_1807]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_9458,plain,
% 11.75/1.99      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),X0)) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_5150,c_1807]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1677,plain,
% 11.75/1.99      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1,c_918]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2538,plain,
% 11.75/1.99      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))),k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) = iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_2199,c_1677]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4450,plain,
% 11.75/1.99      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))),X0) = iProver_top ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_2538,c_1943,c_3904]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4454,plain,
% 11.75/1.99      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))),X0) = iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_1,c_4450]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5152,plain,
% 11.75/1.99      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_4454,c_4999]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5153,plain,
% 11.75/1.99      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))) ),
% 11.75/1.99      inference(light_normalisation,[status(thm)],[c_5152,c_1945]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5154,plain,
% 11.75/1.99      ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_5153,c_1943,c_3904]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5746,plain,
% 11.75/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_5154,c_1796]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5356,plain,
% 11.75/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0)) ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_5154,c_8]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5376,plain,
% 11.75/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_5356,c_1943]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5859,plain,
% 11.75/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.75/1.99      inference(light_normalisation,[status(thm)],[c_5746,c_5376]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5860,plain,
% 11.75/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_5859,c_1943,c_3904]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_9590,plain,
% 11.75/1.99      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k1_xboole_0 ),
% 11.75/1.99      inference(light_normalisation,[status(thm)],[c_9458,c_5572,c_5860]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_9608,plain,
% 11.75/1.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k1_xboole_0 ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_9443,c_1807,c_9590]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_30663,plain,
% 11.75/1.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_26260,c_9608]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2,plain,
% 11.75/1.99      ( r1_xboole_0(X0,X1)
% 11.75/1.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 11.75/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1875,plain,
% 11.75/1.99      ( r1_xboole_0(sK2,sK1)
% 11.75/1.99      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k1_xboole_0 ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1214,plain,
% 11.75/1.99      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_12,plain,
% 11.75/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.75/1.99      | ~ r1_xboole_0(X0,X2)
% 11.75/1.99      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.75/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1023,plain,
% 11.75/1.99      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
% 11.75/1.99      | ~ r1_xboole_0(sK2,sK3)
% 11.75/1.99      | ~ r1_xboole_0(sK2,sK1) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_968,plain,
% 11.75/1.99      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
% 11.75/1.99      | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_19,negated_conjecture,
% 11.75/1.99      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 11.75/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(contradiction,plain,
% 11.75/1.99      ( $false ),
% 11.75/1.99      inference(minisat,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_30663,c_1875,c_1214,c_1023,c_968,c_19,c_20]) ).
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.75/1.99  
% 11.75/1.99  ------                               Statistics
% 11.75/1.99  
% 11.75/1.99  ------ General
% 11.75/1.99  
% 11.75/1.99  abstr_ref_over_cycles:                  0
% 11.75/1.99  abstr_ref_under_cycles:                 0
% 11.75/1.99  gc_basic_clause_elim:                   0
% 11.75/1.99  forced_gc_time:                         0
% 11.75/1.99  parsing_time:                           0.007
% 11.75/1.99  unif_index_cands_time:                  0.
% 11.75/1.99  unif_index_add_time:                    0.
% 11.75/1.99  orderings_time:                         0.
% 11.75/1.99  out_proof_time:                         0.009
% 11.75/1.99  total_time:                             1.108
% 11.75/1.99  num_of_symbols:                         44
% 11.75/1.99  num_of_terms:                           55529
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing
% 11.75/1.99  
% 11.75/1.99  num_of_splits:                          0
% 11.75/1.99  num_of_split_atoms:                     0
% 11.75/1.99  num_of_reused_defs:                     0
% 11.75/1.99  num_eq_ax_congr_red:                    9
% 11.75/1.99  num_of_sem_filtered_clauses:            1
% 11.75/1.99  num_of_subtypes:                        0
% 11.75/1.99  monotx_restored_types:                  0
% 11.75/1.99  sat_num_of_epr_types:                   0
% 11.75/1.99  sat_num_of_non_cyclic_types:            0
% 11.75/1.99  sat_guarded_non_collapsed_types:        0
% 11.75/1.99  num_pure_diseq_elim:                    0
% 11.75/1.99  simp_replaced_by:                       0
% 11.75/1.99  res_preprocessed:                       106
% 11.75/1.99  prep_upred:                             0
% 11.75/1.99  prep_unflattend:                        2
% 11.75/1.99  smt_new_axioms:                         0
% 11.75/1.99  pred_elim_cands:                        2
% 11.75/1.99  pred_elim:                              1
% 11.75/1.99  pred_elim_cl:                           1
% 11.75/1.99  pred_elim_cycles:                       3
% 11.75/1.99  merged_defs:                            24
% 11.75/1.99  merged_defs_ncl:                        0
% 11.75/1.99  bin_hyper_res:                          24
% 11.75/1.99  prep_cycles:                            4
% 11.75/1.99  pred_elim_time:                         0.001
% 11.75/1.99  splitting_time:                         0.
% 11.75/1.99  sem_filter_time:                        0.
% 11.75/1.99  monotx_time:                            0.
% 11.75/1.99  subtype_inf_time:                       0.
% 11.75/1.99  
% 11.75/1.99  ------ Problem properties
% 11.75/1.99  
% 11.75/1.99  clauses:                                22
% 11.75/1.99  conjectures:                            3
% 11.75/1.99  epr:                                    5
% 11.75/1.99  horn:                                   19
% 11.75/1.99  ground:                                 3
% 11.75/1.99  unary:                                  9
% 11.75/1.99  binary:                                 11
% 11.75/1.99  lits:                                   37
% 11.75/1.99  lits_eq:                                9
% 11.75/1.99  fd_pure:                                0
% 11.75/1.99  fd_pseudo:                              0
% 11.75/1.99  fd_cond:                                0
% 11.75/1.99  fd_pseudo_cond:                         0
% 11.75/1.99  ac_symbols:                             0
% 11.75/1.99  
% 11.75/1.99  ------ Propositional Solver
% 11.75/1.99  
% 11.75/1.99  prop_solver_calls:                      29
% 11.75/1.99  prop_fast_solver_calls:                 649
% 11.75/1.99  smt_solver_calls:                       0
% 11.75/1.99  smt_fast_solver_calls:                  0
% 11.75/1.99  prop_num_of_clauses:                    9901
% 11.75/1.99  prop_preprocess_simplified:             12149
% 11.75/1.99  prop_fo_subsumed:                       2
% 11.75/1.99  prop_solver_time:                       0.
% 11.75/1.99  smt_solver_time:                        0.
% 11.75/1.99  smt_fast_solver_time:                   0.
% 11.75/1.99  prop_fast_solver_time:                  0.
% 11.75/1.99  prop_unsat_core_time:                   0.001
% 11.75/1.99  
% 11.75/1.99  ------ QBF
% 11.75/1.99  
% 11.75/1.99  qbf_q_res:                              0
% 11.75/1.99  qbf_num_tautologies:                    0
% 11.75/1.99  qbf_prep_cycles:                        0
% 11.75/1.99  
% 11.75/1.99  ------ BMC1
% 11.75/1.99  
% 11.75/1.99  bmc1_current_bound:                     -1
% 11.75/1.99  bmc1_last_solved_bound:                 -1
% 11.75/1.99  bmc1_unsat_core_size:                   -1
% 11.75/1.99  bmc1_unsat_core_parents_size:           -1
% 11.75/1.99  bmc1_merge_next_fun:                    0
% 11.75/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.75/1.99  
% 11.75/1.99  ------ Instantiation
% 11.75/1.99  
% 11.75/1.99  inst_num_of_clauses:                    1437
% 11.75/1.99  inst_num_in_passive:                    84
% 11.75/1.99  inst_num_in_active:                     725
% 11.75/1.99  inst_num_in_unprocessed:                628
% 11.75/1.99  inst_num_of_loops:                      740
% 11.75/1.99  inst_num_of_learning_restarts:          0
% 11.75/1.99  inst_num_moves_active_passive:          15
% 11.75/1.99  inst_lit_activity:                      0
% 11.75/1.99  inst_lit_activity_moves:                0
% 11.75/1.99  inst_num_tautologies:                   0
% 11.75/1.99  inst_num_prop_implied:                  0
% 11.75/1.99  inst_num_existing_simplified:           0
% 11.75/1.99  inst_num_eq_res_simplified:             0
% 11.75/1.99  inst_num_child_elim:                    0
% 11.75/1.99  inst_num_of_dismatching_blockings:      469
% 11.75/1.99  inst_num_of_non_proper_insts:           1782
% 11.75/1.99  inst_num_of_duplicates:                 0
% 11.75/1.99  inst_inst_num_from_inst_to_res:         0
% 11.75/1.99  inst_dismatching_checking_time:         0.
% 11.75/1.99  
% 11.75/1.99  ------ Resolution
% 11.75/1.99  
% 11.75/1.99  res_num_of_clauses:                     0
% 11.75/1.99  res_num_in_passive:                     0
% 11.75/1.99  res_num_in_active:                      0
% 11.75/1.99  res_num_of_loops:                       110
% 11.75/1.99  res_forward_subset_subsumed:            93
% 11.75/1.99  res_backward_subset_subsumed:           0
% 11.75/1.99  res_forward_subsumed:                   0
% 11.75/1.99  res_backward_subsumed:                  0
% 11.75/1.99  res_forward_subsumption_resolution:     0
% 11.75/1.99  res_backward_subsumption_resolution:    0
% 11.75/1.99  res_clause_to_clause_subsumption:       37937
% 11.75/1.99  res_orphan_elimination:                 0
% 11.75/1.99  res_tautology_del:                      137
% 11.75/1.99  res_num_eq_res_simplified:              0
% 11.75/1.99  res_num_sel_changes:                    0
% 11.75/1.99  res_moves_from_active_to_pass:          0
% 11.75/1.99  
% 11.75/1.99  ------ Superposition
% 11.75/1.99  
% 11.75/1.99  sup_time_total:                         0.
% 11.75/1.99  sup_time_generating:                    0.
% 11.75/1.99  sup_time_sim_full:                      0.
% 11.75/1.99  sup_time_sim_immed:                     0.
% 11.75/1.99  
% 11.75/1.99  sup_num_of_clauses:                     1997
% 11.75/1.99  sup_num_in_active:                      106
% 11.75/1.99  sup_num_in_passive:                     1891
% 11.75/1.99  sup_num_of_loops:                       146
% 11.75/1.99  sup_fw_superposition:                   4929
% 11.75/1.99  sup_bw_superposition:                   5010
% 11.75/1.99  sup_immediate_simplified:               5621
% 11.75/1.99  sup_given_eliminated:                   19
% 11.75/1.99  comparisons_done:                       0
% 11.75/1.99  comparisons_avoided:                    0
% 11.75/1.99  
% 11.75/1.99  ------ Simplifications
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  sim_fw_subset_subsumed:                 36
% 11.75/1.99  sim_bw_subset_subsumed:                 0
% 11.75/1.99  sim_fw_subsumed:                        806
% 11.75/1.99  sim_bw_subsumed:                        122
% 11.75/1.99  sim_fw_subsumption_res:                 0
% 11.75/1.99  sim_bw_subsumption_res:                 0
% 11.75/1.99  sim_tautology_del:                      2
% 11.75/1.99  sim_eq_tautology_del:                   1577
% 11.75/1.99  sim_eq_res_simp:                        108
% 11.75/1.99  sim_fw_demodulated:                     5451
% 11.75/1.99  sim_bw_demodulated:                     316
% 11.75/1.99  sim_light_normalised:                   2842
% 11.75/1.99  sim_joinable_taut:                      0
% 11.75/1.99  sim_joinable_simp:                      0
% 11.75/1.99  sim_ac_normalised:                      0
% 11.75/1.99  sim_smt_subsumption:                    0
% 11.75/1.99  
%------------------------------------------------------------------------------
