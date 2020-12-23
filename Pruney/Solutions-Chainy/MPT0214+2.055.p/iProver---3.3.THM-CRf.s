%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:51 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 383 expanded)
%              Number of clauses        :   43 (  63 expanded)
%              Number of leaves         :   18 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          :  226 ( 775 expanded)
%              Number of equality atoms :  144 ( 547 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f41])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f76,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f64,f75])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f76])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f71,f77])).

fof(f98,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f91])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f70,f77,f77])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f31,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK3 != sK4
      & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( sK3 != sK4
    & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f43])).

fof(f73,plain,(
    r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f73,f77,f77])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f59,f77])).

fof(f94,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f87])).

fof(f95,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f94])).

fof(f74,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f44])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f96,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f88])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18,plain,
    ( r1_tarski(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_241,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != X1
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X2
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_242,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1505,plain,
    ( k4_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_242,c_0])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1525,plain,
    ( k4_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1505,c_8])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1044,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5133,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1044])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1503,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_2549,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_1503])).

cnf(c_5142,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5133,c_2549])).

cnf(c_5181,plain,
    ( r2_hidden(sK3,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5142])).

cnf(c_9,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1041,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3449,plain,
    ( r1_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1041])).

cnf(c_3456,plain,
    ( r1_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3449])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_256,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_257,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(X0,X0,X0,X0,X0) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_1175,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_257])).

cnf(c_14,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1036,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2713,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | r2_hidden(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_1036])).

cnf(c_20,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_34,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_37,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_36,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_38,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_723,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1152,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_1153,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_1035,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2528,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK4 = X0
    | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_1035])).

cnf(c_2543,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK4 = sK3
    | r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_2727,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2713,c_20,c_34,c_37,c_38,c_1153,c_2543])).

cnf(c_2750,plain,
    ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_1036])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5181,c_3456,c_2750])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:47:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.43/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.07  
% 2.43/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/1.07  
% 2.43/1.07  ------  iProver source info
% 2.43/1.07  
% 2.43/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.43/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/1.07  git: non_committed_changes: false
% 2.43/1.07  git: last_make_outside_of_git: false
% 2.43/1.07  
% 2.43/1.07  ------ 
% 2.43/1.07  
% 2.43/1.07  ------ Input Options
% 2.43/1.07  
% 2.43/1.07  --out_options                           all
% 2.43/1.07  --tptp_safe_out                         true
% 2.43/1.07  --problem_path                          ""
% 2.43/1.07  --include_path                          ""
% 2.43/1.07  --clausifier                            res/vclausify_rel
% 2.43/1.07  --clausifier_options                    --mode clausify
% 2.43/1.07  --stdin                                 false
% 2.43/1.07  --stats_out                             all
% 2.43/1.07  
% 2.43/1.07  ------ General Options
% 2.43/1.07  
% 2.43/1.07  --fof                                   false
% 2.43/1.07  --time_out_real                         305.
% 2.43/1.07  --time_out_virtual                      -1.
% 2.43/1.07  --symbol_type_check                     false
% 2.43/1.07  --clausify_out                          false
% 2.43/1.07  --sig_cnt_out                           false
% 2.43/1.07  --trig_cnt_out                          false
% 2.43/1.07  --trig_cnt_out_tolerance                1.
% 2.43/1.07  --trig_cnt_out_sk_spl                   false
% 2.43/1.07  --abstr_cl_out                          false
% 2.43/1.07  
% 2.43/1.07  ------ Global Options
% 2.43/1.07  
% 2.43/1.07  --schedule                              default
% 2.43/1.07  --add_important_lit                     false
% 2.43/1.07  --prop_solver_per_cl                    1000
% 2.43/1.07  --min_unsat_core                        false
% 2.43/1.07  --soft_assumptions                      false
% 2.43/1.07  --soft_lemma_size                       3
% 2.43/1.07  --prop_impl_unit_size                   0
% 2.43/1.07  --prop_impl_unit                        []
% 2.43/1.07  --share_sel_clauses                     true
% 2.43/1.07  --reset_solvers                         false
% 2.43/1.07  --bc_imp_inh                            [conj_cone]
% 2.43/1.07  --conj_cone_tolerance                   3.
% 2.43/1.07  --extra_neg_conj                        none
% 2.43/1.07  --large_theory_mode                     true
% 2.43/1.07  --prolific_symb_bound                   200
% 2.43/1.07  --lt_threshold                          2000
% 2.43/1.07  --clause_weak_htbl                      true
% 2.43/1.07  --gc_record_bc_elim                     false
% 2.43/1.07  
% 2.43/1.07  ------ Preprocessing Options
% 2.43/1.07  
% 2.43/1.07  --preprocessing_flag                    true
% 2.43/1.07  --time_out_prep_mult                    0.1
% 2.43/1.07  --splitting_mode                        input
% 2.43/1.07  --splitting_grd                         true
% 2.43/1.07  --splitting_cvd                         false
% 2.43/1.07  --splitting_cvd_svl                     false
% 2.43/1.07  --splitting_nvd                         32
% 2.43/1.07  --sub_typing                            true
% 2.43/1.07  --prep_gs_sim                           true
% 2.43/1.07  --prep_unflatten                        true
% 2.43/1.07  --prep_res_sim                          true
% 2.43/1.07  --prep_upred                            true
% 2.43/1.07  --prep_sem_filter                       exhaustive
% 2.43/1.07  --prep_sem_filter_out                   false
% 2.43/1.07  --pred_elim                             true
% 2.43/1.07  --res_sim_input                         true
% 2.43/1.07  --eq_ax_congr_red                       true
% 2.43/1.07  --pure_diseq_elim                       true
% 2.43/1.07  --brand_transform                       false
% 2.43/1.07  --non_eq_to_eq                          false
% 2.43/1.07  --prep_def_merge                        true
% 2.43/1.07  --prep_def_merge_prop_impl              false
% 2.43/1.07  --prep_def_merge_mbd                    true
% 2.43/1.07  --prep_def_merge_tr_red                 false
% 2.43/1.07  --prep_def_merge_tr_cl                  false
% 2.43/1.07  --smt_preprocessing                     true
% 2.43/1.07  --smt_ac_axioms                         fast
% 2.43/1.07  --preprocessed_out                      false
% 2.43/1.07  --preprocessed_stats                    false
% 2.43/1.07  
% 2.43/1.07  ------ Abstraction refinement Options
% 2.43/1.07  
% 2.43/1.07  --abstr_ref                             []
% 2.43/1.07  --abstr_ref_prep                        false
% 2.43/1.07  --abstr_ref_until_sat                   false
% 2.43/1.07  --abstr_ref_sig_restrict                funpre
% 2.43/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.07  --abstr_ref_under                       []
% 2.43/1.07  
% 2.43/1.07  ------ SAT Options
% 2.43/1.07  
% 2.43/1.07  --sat_mode                              false
% 2.43/1.07  --sat_fm_restart_options                ""
% 2.43/1.07  --sat_gr_def                            false
% 2.43/1.07  --sat_epr_types                         true
% 2.43/1.07  --sat_non_cyclic_types                  false
% 2.43/1.07  --sat_finite_models                     false
% 2.43/1.07  --sat_fm_lemmas                         false
% 2.43/1.07  --sat_fm_prep                           false
% 2.43/1.07  --sat_fm_uc_incr                        true
% 2.43/1.07  --sat_out_model                         small
% 2.43/1.07  --sat_out_clauses                       false
% 2.43/1.07  
% 2.43/1.07  ------ QBF Options
% 2.43/1.07  
% 2.43/1.07  --qbf_mode                              false
% 2.43/1.07  --qbf_elim_univ                         false
% 2.43/1.07  --qbf_dom_inst                          none
% 2.43/1.07  --qbf_dom_pre_inst                      false
% 2.43/1.07  --qbf_sk_in                             false
% 2.43/1.07  --qbf_pred_elim                         true
% 2.43/1.07  --qbf_split                             512
% 2.43/1.07  
% 2.43/1.07  ------ BMC1 Options
% 2.43/1.07  
% 2.43/1.07  --bmc1_incremental                      false
% 2.43/1.07  --bmc1_axioms                           reachable_all
% 2.43/1.07  --bmc1_min_bound                        0
% 2.43/1.07  --bmc1_max_bound                        -1
% 2.43/1.07  --bmc1_max_bound_default                -1
% 2.43/1.07  --bmc1_symbol_reachability              true
% 2.43/1.07  --bmc1_property_lemmas                  false
% 2.43/1.07  --bmc1_k_induction                      false
% 2.43/1.07  --bmc1_non_equiv_states                 false
% 2.43/1.07  --bmc1_deadlock                         false
% 2.43/1.07  --bmc1_ucm                              false
% 2.43/1.07  --bmc1_add_unsat_core                   none
% 2.43/1.07  --bmc1_unsat_core_children              false
% 2.43/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.07  --bmc1_out_stat                         full
% 2.43/1.07  --bmc1_ground_init                      false
% 2.43/1.07  --bmc1_pre_inst_next_state              false
% 2.43/1.07  --bmc1_pre_inst_state                   false
% 2.43/1.07  --bmc1_pre_inst_reach_state             false
% 2.43/1.07  --bmc1_out_unsat_core                   false
% 2.43/1.07  --bmc1_aig_witness_out                  false
% 2.43/1.07  --bmc1_verbose                          false
% 2.43/1.07  --bmc1_dump_clauses_tptp                false
% 2.43/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.07  --bmc1_dump_file                        -
% 2.43/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.07  --bmc1_ucm_extend_mode                  1
% 2.43/1.07  --bmc1_ucm_init_mode                    2
% 2.43/1.07  --bmc1_ucm_cone_mode                    none
% 2.43/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.07  --bmc1_ucm_relax_model                  4
% 2.43/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.07  --bmc1_ucm_layered_model                none
% 2.43/1.07  --bmc1_ucm_max_lemma_size               10
% 2.43/1.07  
% 2.43/1.07  ------ AIG Options
% 2.43/1.07  
% 2.43/1.07  --aig_mode                              false
% 2.43/1.07  
% 2.43/1.07  ------ Instantiation Options
% 2.43/1.07  
% 2.43/1.07  --instantiation_flag                    true
% 2.43/1.07  --inst_sos_flag                         false
% 2.43/1.07  --inst_sos_phase                        true
% 2.43/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.07  --inst_lit_sel_side                     num_symb
% 2.43/1.07  --inst_solver_per_active                1400
% 2.43/1.07  --inst_solver_calls_frac                1.
% 2.43/1.07  --inst_passive_queue_type               priority_queues
% 2.43/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.07  --inst_passive_queues_freq              [25;2]
% 2.43/1.07  --inst_dismatching                      true
% 2.43/1.07  --inst_eager_unprocessed_to_passive     true
% 2.43/1.07  --inst_prop_sim_given                   true
% 2.43/1.07  --inst_prop_sim_new                     false
% 2.43/1.07  --inst_subs_new                         false
% 2.43/1.07  --inst_eq_res_simp                      false
% 2.43/1.07  --inst_subs_given                       false
% 2.43/1.07  --inst_orphan_elimination               true
% 2.43/1.07  --inst_learning_loop_flag               true
% 2.43/1.07  --inst_learning_start                   3000
% 2.43/1.07  --inst_learning_factor                  2
% 2.43/1.07  --inst_start_prop_sim_after_learn       3
% 2.43/1.07  --inst_sel_renew                        solver
% 2.43/1.07  --inst_lit_activity_flag                true
% 2.43/1.07  --inst_restr_to_given                   false
% 2.43/1.07  --inst_activity_threshold               500
% 2.43/1.07  --inst_out_proof                        true
% 2.43/1.07  
% 2.43/1.07  ------ Resolution Options
% 2.43/1.07  
% 2.43/1.07  --resolution_flag                       true
% 2.43/1.07  --res_lit_sel                           adaptive
% 2.43/1.07  --res_lit_sel_side                      none
% 2.43/1.07  --res_ordering                          kbo
% 2.43/1.07  --res_to_prop_solver                    active
% 2.43/1.07  --res_prop_simpl_new                    false
% 2.43/1.07  --res_prop_simpl_given                  true
% 2.43/1.07  --res_passive_queue_type                priority_queues
% 2.43/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.07  --res_passive_queues_freq               [15;5]
% 2.43/1.07  --res_forward_subs                      full
% 2.43/1.07  --res_backward_subs                     full
% 2.43/1.07  --res_forward_subs_resolution           true
% 2.43/1.07  --res_backward_subs_resolution          true
% 2.43/1.07  --res_orphan_elimination                true
% 2.43/1.07  --res_time_limit                        2.
% 2.43/1.07  --res_out_proof                         true
% 2.43/1.07  
% 2.43/1.07  ------ Superposition Options
% 2.43/1.07  
% 2.43/1.07  --superposition_flag                    true
% 2.43/1.07  --sup_passive_queue_type                priority_queues
% 2.43/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.07  --demod_completeness_check              fast
% 2.43/1.07  --demod_use_ground                      true
% 2.43/1.07  --sup_to_prop_solver                    passive
% 2.43/1.07  --sup_prop_simpl_new                    true
% 2.43/1.07  --sup_prop_simpl_given                  true
% 2.43/1.07  --sup_fun_splitting                     false
% 2.43/1.07  --sup_smt_interval                      50000
% 2.43/1.07  
% 2.43/1.07  ------ Superposition Simplification Setup
% 2.43/1.07  
% 2.43/1.07  --sup_indices_passive                   []
% 2.43/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.07  --sup_full_bw                           [BwDemod]
% 2.43/1.07  --sup_immed_triv                        [TrivRules]
% 2.43/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.07  --sup_immed_bw_main                     []
% 2.43/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.07  
% 2.43/1.07  ------ Combination Options
% 2.43/1.07  
% 2.43/1.07  --comb_res_mult                         3
% 2.43/1.07  --comb_sup_mult                         2
% 2.43/1.07  --comb_inst_mult                        10
% 2.43/1.07  
% 2.43/1.07  ------ Debug Options
% 2.43/1.07  
% 2.43/1.07  --dbg_backtrace                         false
% 2.43/1.07  --dbg_dump_prop_clauses                 false
% 2.43/1.07  --dbg_dump_prop_clauses_file            -
% 2.43/1.07  --dbg_out_stat                          false
% 2.43/1.07  ------ Parsing...
% 2.43/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/1.07  
% 2.43/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.43/1.07  
% 2.43/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/1.07  
% 2.43/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/1.07  ------ Proving...
% 2.43/1.07  ------ Problem Properties 
% 2.43/1.07  
% 2.43/1.07  
% 2.43/1.07  clauses                                 20
% 2.43/1.07  conjectures                             1
% 2.43/1.07  EPR                                     2
% 2.43/1.07  Horn                                    16
% 2.43/1.07  unary                                   10
% 2.43/1.07  binary                                  7
% 2.43/1.07  lits                                    33
% 2.43/1.07  lits eq                                 19
% 2.43/1.07  fd_pure                                 0
% 2.43/1.07  fd_pseudo                               0
% 2.43/1.07  fd_cond                                 1
% 2.43/1.07  fd_pseudo_cond                          2
% 2.43/1.07  AC symbols                              0
% 2.43/1.07  
% 2.43/1.07  ------ Schedule dynamic 5 is on 
% 2.43/1.07  
% 2.43/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/1.07  
% 2.43/1.07  
% 2.43/1.07  ------ 
% 2.43/1.07  Current options:
% 2.43/1.07  ------ 
% 2.43/1.07  
% 2.43/1.07  ------ Input Options
% 2.43/1.07  
% 2.43/1.07  --out_options                           all
% 2.43/1.07  --tptp_safe_out                         true
% 2.43/1.07  --problem_path                          ""
% 2.43/1.07  --include_path                          ""
% 2.43/1.07  --clausifier                            res/vclausify_rel
% 2.43/1.07  --clausifier_options                    --mode clausify
% 2.43/1.07  --stdin                                 false
% 2.43/1.07  --stats_out                             all
% 2.43/1.07  
% 2.43/1.07  ------ General Options
% 2.43/1.07  
% 2.43/1.07  --fof                                   false
% 2.43/1.07  --time_out_real                         305.
% 2.43/1.07  --time_out_virtual                      -1.
% 2.43/1.07  --symbol_type_check                     false
% 2.43/1.07  --clausify_out                          false
% 2.43/1.07  --sig_cnt_out                           false
% 2.43/1.07  --trig_cnt_out                          false
% 2.43/1.07  --trig_cnt_out_tolerance                1.
% 2.43/1.07  --trig_cnt_out_sk_spl                   false
% 2.43/1.07  --abstr_cl_out                          false
% 2.43/1.07  
% 2.43/1.07  ------ Global Options
% 2.43/1.07  
% 2.43/1.07  --schedule                              default
% 2.43/1.07  --add_important_lit                     false
% 2.43/1.07  --prop_solver_per_cl                    1000
% 2.43/1.07  --min_unsat_core                        false
% 2.43/1.07  --soft_assumptions                      false
% 2.43/1.07  --soft_lemma_size                       3
% 2.43/1.07  --prop_impl_unit_size                   0
% 2.43/1.07  --prop_impl_unit                        []
% 2.43/1.07  --share_sel_clauses                     true
% 2.43/1.07  --reset_solvers                         false
% 2.43/1.07  --bc_imp_inh                            [conj_cone]
% 2.43/1.07  --conj_cone_tolerance                   3.
% 2.43/1.07  --extra_neg_conj                        none
% 2.43/1.07  --large_theory_mode                     true
% 2.43/1.07  --prolific_symb_bound                   200
% 2.43/1.07  --lt_threshold                          2000
% 2.43/1.07  --clause_weak_htbl                      true
% 2.43/1.07  --gc_record_bc_elim                     false
% 2.43/1.07  
% 2.43/1.07  ------ Preprocessing Options
% 2.43/1.07  
% 2.43/1.07  --preprocessing_flag                    true
% 2.43/1.07  --time_out_prep_mult                    0.1
% 2.43/1.07  --splitting_mode                        input
% 2.43/1.07  --splitting_grd                         true
% 2.43/1.07  --splitting_cvd                         false
% 2.43/1.07  --splitting_cvd_svl                     false
% 2.43/1.07  --splitting_nvd                         32
% 2.43/1.07  --sub_typing                            true
% 2.43/1.07  --prep_gs_sim                           true
% 2.43/1.07  --prep_unflatten                        true
% 2.43/1.07  --prep_res_sim                          true
% 2.43/1.07  --prep_upred                            true
% 2.43/1.07  --prep_sem_filter                       exhaustive
% 2.43/1.07  --prep_sem_filter_out                   false
% 2.43/1.07  --pred_elim                             true
% 2.43/1.07  --res_sim_input                         true
% 2.43/1.07  --eq_ax_congr_red                       true
% 2.43/1.07  --pure_diseq_elim                       true
% 2.43/1.07  --brand_transform                       false
% 2.43/1.07  --non_eq_to_eq                          false
% 2.43/1.07  --prep_def_merge                        true
% 2.43/1.07  --prep_def_merge_prop_impl              false
% 2.43/1.07  --prep_def_merge_mbd                    true
% 2.43/1.07  --prep_def_merge_tr_red                 false
% 2.43/1.07  --prep_def_merge_tr_cl                  false
% 2.43/1.07  --smt_preprocessing                     true
% 2.43/1.07  --smt_ac_axioms                         fast
% 2.43/1.07  --preprocessed_out                      false
% 2.43/1.07  --preprocessed_stats                    false
% 2.43/1.07  
% 2.43/1.07  ------ Abstraction refinement Options
% 2.43/1.07  
% 2.43/1.07  --abstr_ref                             []
% 2.43/1.07  --abstr_ref_prep                        false
% 2.43/1.07  --abstr_ref_until_sat                   false
% 2.43/1.07  --abstr_ref_sig_restrict                funpre
% 2.43/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.07  --abstr_ref_under                       []
% 2.43/1.07  
% 2.43/1.07  ------ SAT Options
% 2.43/1.07  
% 2.43/1.07  --sat_mode                              false
% 2.43/1.07  --sat_fm_restart_options                ""
% 2.43/1.07  --sat_gr_def                            false
% 2.43/1.07  --sat_epr_types                         true
% 2.43/1.07  --sat_non_cyclic_types                  false
% 2.43/1.07  --sat_finite_models                     false
% 2.43/1.07  --sat_fm_lemmas                         false
% 2.43/1.07  --sat_fm_prep                           false
% 2.43/1.07  --sat_fm_uc_incr                        true
% 2.43/1.07  --sat_out_model                         small
% 2.43/1.07  --sat_out_clauses                       false
% 2.43/1.07  
% 2.43/1.07  ------ QBF Options
% 2.43/1.07  
% 2.43/1.07  --qbf_mode                              false
% 2.43/1.07  --qbf_elim_univ                         false
% 2.43/1.07  --qbf_dom_inst                          none
% 2.43/1.07  --qbf_dom_pre_inst                      false
% 2.43/1.07  --qbf_sk_in                             false
% 2.43/1.07  --qbf_pred_elim                         true
% 2.43/1.07  --qbf_split                             512
% 2.43/1.07  
% 2.43/1.07  ------ BMC1 Options
% 2.43/1.07  
% 2.43/1.07  --bmc1_incremental                      false
% 2.43/1.07  --bmc1_axioms                           reachable_all
% 2.43/1.07  --bmc1_min_bound                        0
% 2.43/1.07  --bmc1_max_bound                        -1
% 2.43/1.07  --bmc1_max_bound_default                -1
% 2.43/1.07  --bmc1_symbol_reachability              true
% 2.43/1.07  --bmc1_property_lemmas                  false
% 2.43/1.07  --bmc1_k_induction                      false
% 2.43/1.07  --bmc1_non_equiv_states                 false
% 2.43/1.07  --bmc1_deadlock                         false
% 2.43/1.07  --bmc1_ucm                              false
% 2.43/1.07  --bmc1_add_unsat_core                   none
% 2.43/1.07  --bmc1_unsat_core_children              false
% 2.43/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.07  --bmc1_out_stat                         full
% 2.43/1.07  --bmc1_ground_init                      false
% 2.43/1.07  --bmc1_pre_inst_next_state              false
% 2.43/1.07  --bmc1_pre_inst_state                   false
% 2.43/1.07  --bmc1_pre_inst_reach_state             false
% 2.43/1.07  --bmc1_out_unsat_core                   false
% 2.43/1.07  --bmc1_aig_witness_out                  false
% 2.43/1.07  --bmc1_verbose                          false
% 2.43/1.07  --bmc1_dump_clauses_tptp                false
% 2.43/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.07  --bmc1_dump_file                        -
% 2.43/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.07  --bmc1_ucm_extend_mode                  1
% 2.43/1.07  --bmc1_ucm_init_mode                    2
% 2.43/1.07  --bmc1_ucm_cone_mode                    none
% 2.43/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.07  --bmc1_ucm_relax_model                  4
% 2.43/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.07  --bmc1_ucm_layered_model                none
% 2.43/1.07  --bmc1_ucm_max_lemma_size               10
% 2.43/1.07  
% 2.43/1.07  ------ AIG Options
% 2.43/1.07  
% 2.43/1.07  --aig_mode                              false
% 2.43/1.07  
% 2.43/1.07  ------ Instantiation Options
% 2.43/1.07  
% 2.43/1.07  --instantiation_flag                    true
% 2.43/1.07  --inst_sos_flag                         false
% 2.43/1.07  --inst_sos_phase                        true
% 2.43/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.07  --inst_lit_sel_side                     none
% 2.43/1.07  --inst_solver_per_active                1400
% 2.43/1.07  --inst_solver_calls_frac                1.
% 2.43/1.07  --inst_passive_queue_type               priority_queues
% 2.43/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.07  --inst_passive_queues_freq              [25;2]
% 2.43/1.07  --inst_dismatching                      true
% 2.43/1.07  --inst_eager_unprocessed_to_passive     true
% 2.43/1.07  --inst_prop_sim_given                   true
% 2.43/1.07  --inst_prop_sim_new                     false
% 2.43/1.07  --inst_subs_new                         false
% 2.43/1.07  --inst_eq_res_simp                      false
% 2.43/1.07  --inst_subs_given                       false
% 2.43/1.07  --inst_orphan_elimination               true
% 2.43/1.07  --inst_learning_loop_flag               true
% 2.43/1.07  --inst_learning_start                   3000
% 2.43/1.07  --inst_learning_factor                  2
% 2.43/1.07  --inst_start_prop_sim_after_learn       3
% 2.43/1.07  --inst_sel_renew                        solver
% 2.43/1.07  --inst_lit_activity_flag                true
% 2.43/1.07  --inst_restr_to_given                   false
% 2.43/1.07  --inst_activity_threshold               500
% 2.43/1.07  --inst_out_proof                        true
% 2.43/1.07  
% 2.43/1.07  ------ Resolution Options
% 2.43/1.07  
% 2.43/1.07  --resolution_flag                       false
% 2.43/1.07  --res_lit_sel                           adaptive
% 2.43/1.07  --res_lit_sel_side                      none
% 2.43/1.07  --res_ordering                          kbo
% 2.43/1.07  --res_to_prop_solver                    active
% 2.43/1.07  --res_prop_simpl_new                    false
% 2.43/1.07  --res_prop_simpl_given                  true
% 2.43/1.07  --res_passive_queue_type                priority_queues
% 2.43/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.07  --res_passive_queues_freq               [15;5]
% 2.43/1.07  --res_forward_subs                      full
% 2.43/1.07  --res_backward_subs                     full
% 2.43/1.07  --res_forward_subs_resolution           true
% 2.43/1.07  --res_backward_subs_resolution          true
% 2.43/1.07  --res_orphan_elimination                true
% 2.43/1.07  --res_time_limit                        2.
% 2.43/1.07  --res_out_proof                         true
% 2.43/1.07  
% 2.43/1.07  ------ Superposition Options
% 2.43/1.07  
% 2.43/1.07  --superposition_flag                    true
% 2.43/1.07  --sup_passive_queue_type                priority_queues
% 2.43/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.07  --demod_completeness_check              fast
% 2.43/1.07  --demod_use_ground                      true
% 2.43/1.07  --sup_to_prop_solver                    passive
% 2.43/1.07  --sup_prop_simpl_new                    true
% 2.43/1.07  --sup_prop_simpl_given                  true
% 2.43/1.07  --sup_fun_splitting                     false
% 2.43/1.07  --sup_smt_interval                      50000
% 2.43/1.07  
% 2.43/1.07  ------ Superposition Simplification Setup
% 2.43/1.07  
% 2.43/1.07  --sup_indices_passive                   []
% 2.43/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.07  --sup_full_bw                           [BwDemod]
% 2.43/1.07  --sup_immed_triv                        [TrivRules]
% 2.43/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.07  --sup_immed_bw_main                     []
% 2.43/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.07  
% 2.43/1.07  ------ Combination Options
% 2.43/1.07  
% 2.43/1.07  --comb_res_mult                         3
% 2.43/1.07  --comb_sup_mult                         2
% 2.43/1.07  --comb_inst_mult                        10
% 2.43/1.07  
% 2.43/1.07  ------ Debug Options
% 2.43/1.07  
% 2.43/1.07  --dbg_backtrace                         false
% 2.43/1.07  --dbg_dump_prop_clauses                 false
% 2.43/1.07  --dbg_dump_prop_clauses_file            -
% 2.43/1.07  --dbg_out_stat                          false
% 2.43/1.07  
% 2.43/1.07  
% 2.43/1.07  
% 2.43/1.07  
% 2.43/1.07  ------ Proving...
% 2.43/1.07  
% 2.43/1.07  
% 2.43/1.07  % SZS status Theorem for theBenchmark.p
% 2.43/1.07  
% 2.43/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/1.07  
% 2.43/1.07  fof(f7,axiom,(
% 2.43/1.07    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f30,plain,(
% 2.43/1.07    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.43/1.07    inference(ennf_transformation,[],[f7])).
% 2.43/1.07  
% 2.43/1.07  fof(f51,plain,(
% 2.43/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.43/1.07    inference(cnf_transformation,[],[f30])).
% 2.43/1.07  
% 2.43/1.07  fof(f8,axiom,(
% 2.43/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f52,plain,(
% 2.43/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.43/1.07    inference(cnf_transformation,[],[f8])).
% 2.43/1.07  
% 2.43/1.07  fof(f84,plain,(
% 2.43/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.43/1.07    inference(definition_unfolding,[],[f51,f52])).
% 2.43/1.07  
% 2.43/1.07  fof(f22,axiom,(
% 2.43/1.07    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f41,plain,(
% 2.43/1.07    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.43/1.07    inference(nnf_transformation,[],[f22])).
% 2.43/1.07  
% 2.43/1.07  fof(f42,plain,(
% 2.43/1.07    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.43/1.07    inference(flattening,[],[f41])).
% 2.43/1.07  
% 2.43/1.07  fof(f71,plain,(
% 2.43/1.07    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 2.43/1.07    inference(cnf_transformation,[],[f42])).
% 2.43/1.07  
% 2.43/1.07  fof(f15,axiom,(
% 2.43/1.07    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f63,plain,(
% 2.43/1.07    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.43/1.07    inference(cnf_transformation,[],[f15])).
% 2.43/1.07  
% 2.43/1.07  fof(f16,axiom,(
% 2.43/1.07    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f64,plain,(
% 2.43/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.43/1.07    inference(cnf_transformation,[],[f16])).
% 2.43/1.07  
% 2.43/1.07  fof(f17,axiom,(
% 2.43/1.07    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f65,plain,(
% 2.43/1.07    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.43/1.07    inference(cnf_transformation,[],[f17])).
% 2.43/1.07  
% 2.43/1.07  fof(f18,axiom,(
% 2.43/1.07    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f66,plain,(
% 2.43/1.07    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.43/1.07    inference(cnf_transformation,[],[f18])).
% 2.43/1.07  
% 2.43/1.07  fof(f75,plain,(
% 2.43/1.07    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.43/1.07    inference(definition_unfolding,[],[f65,f66])).
% 2.43/1.07  
% 2.43/1.07  fof(f76,plain,(
% 2.43/1.07    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.43/1.07    inference(definition_unfolding,[],[f64,f75])).
% 2.43/1.07  
% 2.43/1.07  fof(f77,plain,(
% 2.43/1.07    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.43/1.07    inference(definition_unfolding,[],[f63,f76])).
% 2.43/1.07  
% 2.43/1.07  fof(f91,plain,(
% 2.43/1.07    ( ! [X0,X1] : (r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 2.43/1.07    inference(definition_unfolding,[],[f71,f77])).
% 2.43/1.07  
% 2.43/1.07  fof(f98,plain,(
% 2.43/1.07    ( ! [X1] : (r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 2.43/1.07    inference(equality_resolution,[],[f91])).
% 2.43/1.07  
% 2.43/1.07  fof(f6,axiom,(
% 2.43/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f50,plain,(
% 2.43/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.43/1.07    inference(cnf_transformation,[],[f6])).
% 2.43/1.07  
% 2.43/1.07  fof(f79,plain,(
% 2.43/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.43/1.07    inference(definition_unfolding,[],[f50,f52])).
% 2.43/1.07  
% 2.43/1.07  fof(f9,axiom,(
% 2.43/1.07    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f53,plain,(
% 2.43/1.07    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.43/1.07    inference(cnf_transformation,[],[f9])).
% 2.43/1.07  
% 2.43/1.07  fof(f4,axiom,(
% 2.43/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f26,plain,(
% 2.43/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.43/1.07    inference(rectify,[],[f4])).
% 2.43/1.07  
% 2.43/1.07  fof(f28,plain,(
% 2.43/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.43/1.07    inference(ennf_transformation,[],[f26])).
% 2.43/1.07  
% 2.43/1.07  fof(f32,plain,(
% 2.43/1.07    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 2.43/1.07    introduced(choice_axiom,[])).
% 2.43/1.07  
% 2.43/1.07  fof(f33,plain,(
% 2.43/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.43/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).
% 2.43/1.07  
% 2.43/1.07  fof(f48,plain,(
% 2.43/1.07    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.43/1.07    inference(cnf_transformation,[],[f33])).
% 2.43/1.07  
% 2.43/1.07  fof(f82,plain,(
% 2.43/1.07    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.43/1.07    inference(definition_unfolding,[],[f48,f52])).
% 2.43/1.07  
% 2.43/1.07  fof(f2,axiom,(
% 2.43/1.07    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f25,plain,(
% 2.43/1.07    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.43/1.07    inference(rectify,[],[f2])).
% 2.43/1.07  
% 2.43/1.07  fof(f45,plain,(
% 2.43/1.07    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.43/1.07    inference(cnf_transformation,[],[f25])).
% 2.43/1.07  
% 2.43/1.07  fof(f81,plain,(
% 2.43/1.07    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.43/1.07    inference(definition_unfolding,[],[f45,f52])).
% 2.43/1.07  
% 2.43/1.07  fof(f10,axiom,(
% 2.43/1.07    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f54,plain,(
% 2.43/1.07    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.43/1.07    inference(cnf_transformation,[],[f10])).
% 2.43/1.07  
% 2.43/1.07  fof(f70,plain,(
% 2.43/1.07    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.43/1.07    inference(cnf_transformation,[],[f42])).
% 2.43/1.07  
% 2.43/1.07  fof(f92,plain,(
% 2.43/1.07    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 2.43/1.07    inference(definition_unfolding,[],[f70,f77,f77])).
% 2.43/1.07  
% 2.43/1.07  fof(f23,conjecture,(
% 2.43/1.07    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f24,negated_conjecture,(
% 2.43/1.07    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.43/1.07    inference(negated_conjecture,[],[f23])).
% 2.43/1.07  
% 2.43/1.07  fof(f31,plain,(
% 2.43/1.07    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.43/1.07    inference(ennf_transformation,[],[f24])).
% 2.43/1.07  
% 2.43/1.07  fof(f43,plain,(
% 2.43/1.07    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK3 != sK4 & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 2.43/1.07    introduced(choice_axiom,[])).
% 2.43/1.07  
% 2.43/1.07  fof(f44,plain,(
% 2.43/1.07    sK3 != sK4 & r1_tarski(k1_tarski(sK3),k1_tarski(sK4))),
% 2.43/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f43])).
% 2.43/1.07  
% 2.43/1.07  fof(f73,plain,(
% 2.43/1.07    r1_tarski(k1_tarski(sK3),k1_tarski(sK4))),
% 2.43/1.07    inference(cnf_transformation,[],[f44])).
% 2.43/1.07  
% 2.43/1.07  fof(f93,plain,(
% 2.43/1.07    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 2.43/1.07    inference(definition_unfolding,[],[f73,f77,f77])).
% 2.43/1.07  
% 2.43/1.07  fof(f13,axiom,(
% 2.43/1.07    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.43/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.07  
% 2.43/1.07  fof(f37,plain,(
% 2.43/1.07    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.43/1.07    inference(nnf_transformation,[],[f13])).
% 2.43/1.07  
% 2.43/1.07  fof(f38,plain,(
% 2.43/1.07    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.43/1.07    inference(rectify,[],[f37])).
% 2.43/1.07  
% 2.43/1.07  fof(f39,plain,(
% 2.43/1.07    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.43/1.07    introduced(choice_axiom,[])).
% 2.43/1.07  
% 2.43/1.07  fof(f40,plain,(
% 2.43/1.07    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.43/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 2.43/1.07  
% 2.43/1.07  fof(f59,plain,(
% 2.43/1.07    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.43/1.07    inference(cnf_transformation,[],[f40])).
% 2.43/1.07  
% 2.43/1.07  fof(f87,plain,(
% 2.43/1.07    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.43/1.07    inference(definition_unfolding,[],[f59,f77])).
% 2.43/1.07  
% 2.43/1.07  fof(f94,plain,(
% 2.43/1.07    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 2.43/1.07    inference(equality_resolution,[],[f87])).
% 2.43/1.07  
% 2.43/1.07  fof(f95,plain,(
% 2.43/1.07    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 2.43/1.07    inference(equality_resolution,[],[f94])).
% 2.43/1.07  
% 2.43/1.07  fof(f74,plain,(
% 2.43/1.07    sK3 != sK4),
% 2.43/1.07    inference(cnf_transformation,[],[f44])).
% 2.43/1.07  
% 2.43/1.07  fof(f58,plain,(
% 2.43/1.07    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.43/1.07    inference(cnf_transformation,[],[f40])).
% 2.43/1.07  
% 2.43/1.07  fof(f88,plain,(
% 2.43/1.07    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.43/1.07    inference(definition_unfolding,[],[f58,f77])).
% 2.43/1.07  
% 2.43/1.07  fof(f96,plain,(
% 2.43/1.07    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 2.43/1.07    inference(equality_resolution,[],[f88])).
% 2.43/1.07  
% 2.43/1.07  cnf(c_7,plain,
% 2.43/1.07      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.43/1.07      inference(cnf_transformation,[],[f84]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_18,plain,
% 2.43/1.07      ( r1_tarski(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 2.43/1.07      inference(cnf_transformation,[],[f98]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_241,plain,
% 2.43/1.07      ( k3_enumset1(X0,X0,X0,X0,X0) != X1
% 2.43/1.07      | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X2
% 2.43/1.07      | k1_xboole_0 != X2 ),
% 2.43/1.07      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_242,plain,
% 2.43/1.07      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0))) = k1_xboole_0 ),
% 2.43/1.07      inference(unflattening,[status(thm)],[c_241]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_0,plain,
% 2.43/1.07      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.43/1.07      inference(cnf_transformation,[],[f79]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1505,plain,
% 2.43/1.07      ( k4_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.43/1.07      inference(superposition,[status(thm)],[c_242,c_0]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_8,plain,
% 2.43/1.07      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.43/1.07      inference(cnf_transformation,[],[f53]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1525,plain,
% 2.43/1.07      ( k4_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) = k1_xboole_0 ),
% 2.43/1.07      inference(demodulation,[status(thm)],[c_1505,c_8]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_4,plain,
% 2.43/1.07      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 2.43/1.07      | ~ r1_xboole_0(X1,X2) ),
% 2.43/1.07      inference(cnf_transformation,[],[f82]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1044,plain,
% 2.43/1.07      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 2.43/1.07      | r1_xboole_0(X1,X2) != iProver_top ),
% 2.43/1.07      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_5133,plain,
% 2.43/1.07      ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 2.43/1.07      | r1_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 2.43/1.07      inference(superposition,[status(thm)],[c_1525,c_1044]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_2,plain,
% 2.43/1.07      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 2.43/1.07      inference(cnf_transformation,[],[f81]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1503,plain,
% 2.43/1.07      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 2.43/1.07      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_2549,plain,
% 2.43/1.07      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.43/1.07      inference(superposition,[status(thm)],[c_8,c_1503]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_5142,plain,
% 2.43/1.07      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.43/1.07      | r1_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 2.43/1.07      inference(light_normalisation,[status(thm)],[c_5133,c_2549]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_5181,plain,
% 2.43/1.07      ( r2_hidden(sK3,k1_xboole_0) != iProver_top
% 2.43/1.07      | r1_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.43/1.07      inference(instantiation,[status(thm)],[c_5142]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_9,plain,
% 2.43/1.07      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 2.43/1.07      inference(cnf_transformation,[],[f54]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1041,plain,
% 2.43/1.07      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 2.43/1.07      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_3449,plain,
% 2.43/1.07      ( r1_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 2.43/1.07      inference(superposition,[status(thm)],[c_1525,c_1041]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_3456,plain,
% 2.43/1.07      ( r1_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.43/1.07      inference(instantiation,[status(thm)],[c_3449]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_19,plain,
% 2.43/1.07      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 2.43/1.07      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 2.43/1.07      | k1_xboole_0 = X0 ),
% 2.43/1.07      inference(cnf_transformation,[],[f92]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_21,negated_conjecture,
% 2.43/1.07      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 2.43/1.07      inference(cnf_transformation,[],[f93]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_256,plain,
% 2.43/1.07      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.43/1.07      | k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 2.43/1.07      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
% 2.43/1.07      | k1_xboole_0 = X1 ),
% 2.43/1.07      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_257,plain,
% 2.43/1.07      ( k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 2.43/1.07      | k3_enumset1(X0,X0,X0,X0,X0) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.43/1.07      | k1_xboole_0 = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 2.43/1.07      inference(unflattening,[status(thm)],[c_256]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1175,plain,
% 2.43/1.07      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.43/1.07      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 2.43/1.07      inference(equality_resolution,[status(thm)],[c_257]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_14,plain,
% 2.43/1.07      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 2.43/1.07      inference(cnf_transformation,[],[f95]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1036,plain,
% 2.43/1.07      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 2.43/1.07      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_2713,plain,
% 2.43/1.07      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 2.43/1.07      | r2_hidden(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.43/1.07      inference(superposition,[status(thm)],[c_1175,c_1036]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_20,negated_conjecture,
% 2.43/1.07      ( sK3 != sK4 ),
% 2.43/1.07      inference(cnf_transformation,[],[f74]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_15,plain,
% 2.43/1.07      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.43/1.07      inference(cnf_transformation,[],[f96]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_34,plain,
% 2.43/1.07      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 2.43/1.07      inference(instantiation,[status(thm)],[c_15]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_37,plain,
% 2.43/1.07      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 2.43/1.07      inference(instantiation,[status(thm)],[c_14]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_36,plain,
% 2.43/1.07      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 2.43/1.07      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_38,plain,
% 2.43/1.07      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.43/1.07      inference(instantiation,[status(thm)],[c_36]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_723,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1152,plain,
% 2.43/1.07      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 2.43/1.07      inference(instantiation,[status(thm)],[c_723]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1153,plain,
% 2.43/1.07      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 2.43/1.07      inference(instantiation,[status(thm)],[c_1152]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_1035,plain,
% 2.43/1.07      ( X0 = X1
% 2.43/1.07      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 2.43/1.07      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_2528,plain,
% 2.43/1.07      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 2.43/1.07      | sK4 = X0
% 2.43/1.07      | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.43/1.07      inference(superposition,[status(thm)],[c_1175,c_1035]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_2543,plain,
% 2.43/1.07      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 2.43/1.07      | sK4 = sK3
% 2.43/1.07      | r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.43/1.07      inference(instantiation,[status(thm)],[c_2528]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_2727,plain,
% 2.43/1.07      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 2.43/1.07      inference(global_propositional_subsumption,
% 2.43/1.07                [status(thm)],
% 2.43/1.07                [c_2713,c_20,c_34,c_37,c_38,c_1153,c_2543]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(c_2750,plain,
% 2.43/1.07      ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 2.43/1.07      inference(superposition,[status(thm)],[c_2727,c_1036]) ).
% 2.43/1.07  
% 2.43/1.07  cnf(contradiction,plain,
% 2.43/1.07      ( $false ),
% 2.43/1.07      inference(minisat,[status(thm)],[c_5181,c_3456,c_2750]) ).
% 2.43/1.07  
% 2.43/1.07  
% 2.43/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/1.07  
% 2.43/1.07  ------                               Statistics
% 2.43/1.07  
% 2.43/1.07  ------ General
% 2.43/1.07  
% 2.43/1.07  abstr_ref_over_cycles:                  0
% 2.43/1.07  abstr_ref_under_cycles:                 0
% 2.43/1.07  gc_basic_clause_elim:                   0
% 2.43/1.07  forced_gc_time:                         0
% 2.43/1.07  parsing_time:                           0.008
% 2.43/1.07  unif_index_cands_time:                  0.
% 2.43/1.07  unif_index_add_time:                    0.
% 2.43/1.07  orderings_time:                         0.
% 2.43/1.07  out_proof_time:                         0.009
% 2.43/1.07  total_time:                             0.224
% 2.43/1.07  num_of_symbols:                         44
% 2.43/1.07  num_of_terms:                           5424
% 2.43/1.07  
% 2.43/1.07  ------ Preprocessing
% 2.43/1.07  
% 2.43/1.07  num_of_splits:                          0
% 2.43/1.07  num_of_split_atoms:                     0
% 2.43/1.07  num_of_reused_defs:                     0
% 2.43/1.07  num_eq_ax_congr_red:                    42
% 2.43/1.07  num_of_sem_filtered_clauses:            1
% 2.43/1.07  num_of_subtypes:                        0
% 2.43/1.07  monotx_restored_types:                  0
% 2.43/1.07  sat_num_of_epr_types:                   0
% 2.43/1.07  sat_num_of_non_cyclic_types:            0
% 2.43/1.07  sat_guarded_non_collapsed_types:        0
% 2.43/1.07  num_pure_diseq_elim:                    0
% 2.43/1.07  simp_replaced_by:                       0
% 2.43/1.07  res_preprocessed:                       97
% 2.43/1.07  prep_upred:                             0
% 2.43/1.07  prep_unflattend:                        39
% 2.43/1.07  smt_new_axioms:                         0
% 2.43/1.07  pred_elim_cands:                        2
% 2.43/1.07  pred_elim:                              1
% 2.43/1.07  pred_elim_cl:                           2
% 2.43/1.07  pred_elim_cycles:                       3
% 2.43/1.07  merged_defs:                            8
% 2.43/1.07  merged_defs_ncl:                        0
% 2.43/1.07  bin_hyper_res:                          8
% 2.43/1.07  prep_cycles:                            4
% 2.43/1.07  pred_elim_time:                         0.007
% 2.43/1.07  splitting_time:                         0.
% 2.43/1.07  sem_filter_time:                        0.
% 2.43/1.07  monotx_time:                            0.
% 2.43/1.07  subtype_inf_time:                       0.
% 2.43/1.07  
% 2.43/1.07  ------ Problem properties
% 2.43/1.07  
% 2.43/1.07  clauses:                                20
% 2.43/1.07  conjectures:                            1
% 2.43/1.07  epr:                                    2
% 2.43/1.07  horn:                                   16
% 2.43/1.07  ground:                                 2
% 2.43/1.07  unary:                                  10
% 2.43/1.07  binary:                                 7
% 2.43/1.07  lits:                                   33
% 2.43/1.07  lits_eq:                                19
% 2.43/1.07  fd_pure:                                0
% 2.43/1.07  fd_pseudo:                              0
% 2.43/1.07  fd_cond:                                1
% 2.43/1.07  fd_pseudo_cond:                         2
% 2.43/1.07  ac_symbols:                             0
% 2.43/1.07  
% 2.43/1.07  ------ Propositional Solver
% 2.43/1.07  
% 2.43/1.07  prop_solver_calls:                      27
% 2.43/1.07  prop_fast_solver_calls:                 532
% 2.43/1.07  smt_solver_calls:                       0
% 2.43/1.07  smt_fast_solver_calls:                  0
% 2.43/1.07  prop_num_of_clauses:                    1713
% 2.43/1.07  prop_preprocess_simplified:             5805
% 2.43/1.07  prop_fo_subsumed:                       7
% 2.43/1.07  prop_solver_time:                       0.
% 2.43/1.07  smt_solver_time:                        0.
% 2.43/1.07  smt_fast_solver_time:                   0.
% 2.43/1.07  prop_fast_solver_time:                  0.
% 2.43/1.07  prop_unsat_core_time:                   0.
% 2.43/1.07  
% 2.43/1.07  ------ QBF
% 2.43/1.07  
% 2.43/1.07  qbf_q_res:                              0
% 2.43/1.07  qbf_num_tautologies:                    0
% 2.43/1.07  qbf_prep_cycles:                        0
% 2.43/1.07  
% 2.43/1.07  ------ BMC1
% 2.43/1.07  
% 2.43/1.07  bmc1_current_bound:                     -1
% 2.43/1.07  bmc1_last_solved_bound:                 -1
% 2.43/1.07  bmc1_unsat_core_size:                   -1
% 2.43/1.07  bmc1_unsat_core_parents_size:           -1
% 2.43/1.07  bmc1_merge_next_fun:                    0
% 2.43/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.43/1.07  
% 2.43/1.07  ------ Instantiation
% 2.43/1.07  
% 2.43/1.07  inst_num_of_clauses:                    655
% 2.43/1.07  inst_num_in_passive:                    259
% 2.43/1.07  inst_num_in_active:                     247
% 2.43/1.07  inst_num_in_unprocessed:                150
% 2.43/1.07  inst_num_of_loops:                      260
% 2.43/1.07  inst_num_of_learning_restarts:          0
% 2.43/1.07  inst_num_moves_active_passive:          12
% 2.43/1.07  inst_lit_activity:                      0
% 2.43/1.07  inst_lit_activity_moves:                0
% 2.43/1.07  inst_num_tautologies:                   0
% 2.43/1.07  inst_num_prop_implied:                  0
% 2.43/1.07  inst_num_existing_simplified:           0
% 2.43/1.07  inst_num_eq_res_simplified:             0
% 2.43/1.07  inst_num_child_elim:                    0
% 2.43/1.07  inst_num_of_dismatching_blockings:      337
% 2.43/1.07  inst_num_of_non_proper_insts:           632
% 2.43/1.07  inst_num_of_duplicates:                 0
% 2.43/1.07  inst_inst_num_from_inst_to_res:         0
% 2.43/1.07  inst_dismatching_checking_time:         0.
% 2.43/1.07  
% 2.43/1.07  ------ Resolution
% 2.43/1.07  
% 2.43/1.07  res_num_of_clauses:                     0
% 2.43/1.07  res_num_in_passive:                     0
% 2.43/1.07  res_num_in_active:                      0
% 2.43/1.07  res_num_of_loops:                       101
% 2.43/1.07  res_forward_subset_subsumed:            107
% 2.43/1.07  res_backward_subset_subsumed:           2
% 2.43/1.07  res_forward_subsumed:                   1
% 2.43/1.07  res_backward_subsumed:                  0
% 2.43/1.07  res_forward_subsumption_resolution:     0
% 2.43/1.07  res_backward_subsumption_resolution:    1
% 2.43/1.07  res_clause_to_clause_subsumption:       409
% 2.43/1.07  res_orphan_elimination:                 0
% 2.43/1.07  res_tautology_del:                      98
% 2.43/1.07  res_num_eq_res_simplified:              0
% 2.43/1.07  res_num_sel_changes:                    0
% 2.43/1.07  res_moves_from_active_to_pass:          0
% 2.43/1.07  
% 2.43/1.07  ------ Superposition
% 2.43/1.07  
% 2.43/1.07  sup_time_total:                         0.
% 2.43/1.07  sup_time_generating:                    0.
% 2.43/1.07  sup_time_sim_full:                      0.
% 2.43/1.07  sup_time_sim_immed:                     0.
% 2.43/1.07  
% 2.43/1.07  sup_num_of_clauses:                     89
% 2.43/1.07  sup_num_in_active:                      38
% 2.43/1.07  sup_num_in_passive:                     51
% 2.43/1.07  sup_num_of_loops:                       51
% 2.43/1.07  sup_fw_superposition:                   96
% 2.43/1.07  sup_bw_superposition:                   101
% 2.43/1.07  sup_immediate_simplified:               72
% 2.43/1.07  sup_given_eliminated:                   1
% 2.43/1.07  comparisons_done:                       0
% 2.43/1.07  comparisons_avoided:                    33
% 2.43/1.07  
% 2.43/1.07  ------ Simplifications
% 2.43/1.07  
% 2.43/1.07  
% 2.43/1.07  sim_fw_subset_subsumed:                 18
% 2.43/1.07  sim_bw_subset_subsumed:                 9
% 2.43/1.07  sim_fw_subsumed:                        11
% 2.43/1.07  sim_bw_subsumed:                        6
% 2.43/1.07  sim_fw_subsumption_res:                 0
% 2.43/1.07  sim_bw_subsumption_res:                 0
% 2.43/1.07  sim_tautology_del:                      3
% 2.43/1.07  sim_eq_tautology_del:                   12
% 2.43/1.07  sim_eq_res_simp:                        0
% 2.43/1.07  sim_fw_demodulated:                     18
% 2.43/1.07  sim_bw_demodulated:                     15
% 2.43/1.07  sim_light_normalised:                   28
% 2.43/1.07  sim_joinable_taut:                      0
% 2.43/1.07  sim_joinable_simp:                      0
% 2.43/1.07  sim_ac_normalised:                      0
% 2.43/1.07  sim_smt_subsumption:                    0
% 2.43/1.07  
%------------------------------------------------------------------------------
