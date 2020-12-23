%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:02 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  123 (1061 expanded)
%              Number of clauses        :   68 ( 410 expanded)
%              Number of leaves         :   18 ( 272 expanded)
%              Depth                    :   22
%              Number of atoms          :  321 (2923 expanded)
%              Number of equality atoms :  174 (1782 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f28])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK4 = X2
          | ~ r2_hidden(X2,sK3) )
      & k1_xboole_0 != sK3
      & k1_tarski(sK4) != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ! [X2] :
        ( sK4 = X2
        | ~ r2_hidden(X2,sK3) )
    & k1_xboole_0 != sK3
    & k1_tarski(sK4) != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f33])).

fof(f60,plain,(
    ! [X2] :
      ( sK4 = X2
      | ~ r2_hidden(X2,sK3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f49,f49])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    k1_tarski(sK4) != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    k2_enumset1(sK4,sK4,sK4,sK4) != sK3 ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1064,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | sK4 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1060,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1820,plain,
    ( sK2(sK3) = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1064,c_1060])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_676,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_687,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_677,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1094,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1095,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1094])).

cnf(c_1920,plain,
    ( sK2(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1820,c_20,c_687,c_1095])).

cnf(c_1922,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_1064])).

cnf(c_2177,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1922,c_20,c_687,c_1095])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_153,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_16,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_161,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_162,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_281,plain,
    ( ~ r2_hidden(X0,X1)
    | X1 != X2
    | k2_enumset1(X0,X0,X0,X0) != X3
    | k4_xboole_0(X3,X2) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_153,c_162])).

cnf(c_282,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_478,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_282])).

cnf(c_1058,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_2181,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2177,c_1058])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1068,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2998,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_1068])).

cnf(c_32878,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2998])).

cnf(c_33667,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = k1_xboole_0
    | sK2(k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = sK4 ),
    inference(superposition,[status(thm)],[c_32878,c_1060])).

cnf(c_34817,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k1_xboole_0
    | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = k1_xboole_0
    | r2_hidden(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_33667,c_1064])).

cnf(c_37085,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = k1_xboole_0
    | k4_xboole_0(sK3,k4_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0
    | r2_hidden(sK4,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_34817])).

cnf(c_37105,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = k1_xboole_0
    | k4_xboole_0(sK3,k4_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0
    | r2_hidden(sK4,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_37085,c_2181])).

cnf(c_13,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2284,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2181,c_0])).

cnf(c_2286,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_2284,c_13])).

cnf(c_37106,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37105,c_13,c_2286])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1071,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8679,plain,
    ( sK0(X0,X1,sK3) = sK4
    | k4_xboole_0(X0,X1) = sK3
    | r2_hidden(sK0(X0,X1,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_1060])).

cnf(c_2999,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1068])).

cnf(c_9276,plain,
    ( sK0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2,sK3) = sK4
    | k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = sK3
    | r2_hidden(sK0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2,sK3),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8679,c_2999])).

cnf(c_23290,plain,
    ( sK0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),X1,sK3) = sK4
    | k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),X1) = sK3 ),
    inference(superposition,[status(thm)],[c_9276,c_1060])).

cnf(c_24714,plain,
    ( sK0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),X1,sK3) = sK4
    | k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),X1) = sK3 ),
    inference(superposition,[status(thm)],[c_0,c_23290])).

cnf(c_24883,plain,
    ( sK0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k1_xboole_0,sK3) = sK4
    | k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_24714,c_13])).

cnf(c_27579,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3) = sK4
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2286,c_24883])).

cnf(c_27813,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3) = sK4
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_27579,c_2181])).

cnf(c_27814,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = sK3
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_27813,c_13])).

cnf(c_21,negated_conjecture,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != sK3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28352,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27814,c_21])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1073,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_28354,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = sK3
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3),sK3) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3),k1_xboole_0) = iProver_top
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28352,c_1073])).

cnf(c_28365,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = sK3
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28354,c_28352])).

cnf(c_28366,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = sK3
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28365,c_13])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1202,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_14947,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1202])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1069,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3253,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1069])).

cnf(c_3278,plain,
    ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2177,c_3253])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1063,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2283,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k1_xboole_0
    | r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_1063])).

cnf(c_2287,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | k2_enumset1(sK4,sK4,sK4,sK4) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2283])).

cnf(c_1923,plain,
    ( r2_hidden(sK4,sK3)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1922])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37106,c_28366,c_14947,c_3278,c_2287,c_1923,c_1922,c_1095,c_687,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:42:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 7.88/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/1.51  
% 7.88/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.88/1.51  
% 7.88/1.51  ------  iProver source info
% 7.88/1.51  
% 7.88/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.88/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.88/1.51  git: non_committed_changes: false
% 7.88/1.51  git: last_make_outside_of_git: false
% 7.88/1.51  
% 7.88/1.51  ------ 
% 7.88/1.51  
% 7.88/1.51  ------ Input Options
% 7.88/1.51  
% 7.88/1.51  --out_options                           all
% 7.88/1.51  --tptp_safe_out                         true
% 7.88/1.51  --problem_path                          ""
% 7.88/1.51  --include_path                          ""
% 7.88/1.51  --clausifier                            res/vclausify_rel
% 7.88/1.51  --clausifier_options                    ""
% 7.88/1.51  --stdin                                 false
% 7.88/1.51  --stats_out                             all
% 7.88/1.51  
% 7.88/1.51  ------ General Options
% 7.88/1.51  
% 7.88/1.51  --fof                                   false
% 7.88/1.51  --time_out_real                         305.
% 7.88/1.51  --time_out_virtual                      -1.
% 7.88/1.51  --symbol_type_check                     false
% 7.88/1.51  --clausify_out                          false
% 7.88/1.51  --sig_cnt_out                           false
% 7.88/1.51  --trig_cnt_out                          false
% 7.88/1.51  --trig_cnt_out_tolerance                1.
% 7.88/1.51  --trig_cnt_out_sk_spl                   false
% 7.88/1.51  --abstr_cl_out                          false
% 7.88/1.51  
% 7.88/1.51  ------ Global Options
% 7.88/1.51  
% 7.88/1.51  --schedule                              default
% 7.88/1.51  --add_important_lit                     false
% 7.88/1.51  --prop_solver_per_cl                    1000
% 7.88/1.51  --min_unsat_core                        false
% 7.88/1.51  --soft_assumptions                      false
% 7.88/1.51  --soft_lemma_size                       3
% 7.88/1.51  --prop_impl_unit_size                   0
% 7.88/1.51  --prop_impl_unit                        []
% 7.88/1.51  --share_sel_clauses                     true
% 7.88/1.51  --reset_solvers                         false
% 7.88/1.51  --bc_imp_inh                            [conj_cone]
% 7.88/1.51  --conj_cone_tolerance                   3.
% 7.88/1.51  --extra_neg_conj                        none
% 7.88/1.51  --large_theory_mode                     true
% 7.88/1.51  --prolific_symb_bound                   200
% 7.88/1.51  --lt_threshold                          2000
% 7.88/1.51  --clause_weak_htbl                      true
% 7.88/1.51  --gc_record_bc_elim                     false
% 7.88/1.51  
% 7.88/1.51  ------ Preprocessing Options
% 7.88/1.52  
% 7.88/1.52  --preprocessing_flag                    true
% 7.88/1.52  --time_out_prep_mult                    0.1
% 7.88/1.52  --splitting_mode                        input
% 7.88/1.52  --splitting_grd                         true
% 7.88/1.52  --splitting_cvd                         false
% 7.88/1.52  --splitting_cvd_svl                     false
% 7.88/1.52  --splitting_nvd                         32
% 7.88/1.52  --sub_typing                            true
% 7.88/1.52  --prep_gs_sim                           true
% 7.88/1.52  --prep_unflatten                        true
% 7.88/1.52  --prep_res_sim                          true
% 7.88/1.52  --prep_upred                            true
% 7.88/1.52  --prep_sem_filter                       exhaustive
% 7.88/1.52  --prep_sem_filter_out                   false
% 7.88/1.52  --pred_elim                             true
% 7.88/1.52  --res_sim_input                         true
% 7.88/1.52  --eq_ax_congr_red                       true
% 7.88/1.52  --pure_diseq_elim                       true
% 7.88/1.52  --brand_transform                       false
% 7.88/1.52  --non_eq_to_eq                          false
% 7.88/1.52  --prep_def_merge                        true
% 7.88/1.52  --prep_def_merge_prop_impl              false
% 7.88/1.52  --prep_def_merge_mbd                    true
% 7.88/1.52  --prep_def_merge_tr_red                 false
% 7.88/1.52  --prep_def_merge_tr_cl                  false
% 7.88/1.52  --smt_preprocessing                     true
% 7.88/1.52  --smt_ac_axioms                         fast
% 7.88/1.52  --preprocessed_out                      false
% 7.88/1.52  --preprocessed_stats                    false
% 7.88/1.52  
% 7.88/1.52  ------ Abstraction refinement Options
% 7.88/1.52  
% 7.88/1.52  --abstr_ref                             []
% 7.88/1.52  --abstr_ref_prep                        false
% 7.88/1.52  --abstr_ref_until_sat                   false
% 7.88/1.52  --abstr_ref_sig_restrict                funpre
% 7.88/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.52  --abstr_ref_under                       []
% 7.88/1.52  
% 7.88/1.52  ------ SAT Options
% 7.88/1.52  
% 7.88/1.52  --sat_mode                              false
% 7.88/1.52  --sat_fm_restart_options                ""
% 7.88/1.52  --sat_gr_def                            false
% 7.88/1.52  --sat_epr_types                         true
% 7.88/1.52  --sat_non_cyclic_types                  false
% 7.88/1.52  --sat_finite_models                     false
% 7.88/1.52  --sat_fm_lemmas                         false
% 7.88/1.52  --sat_fm_prep                           false
% 7.88/1.52  --sat_fm_uc_incr                        true
% 7.88/1.52  --sat_out_model                         small
% 7.88/1.52  --sat_out_clauses                       false
% 7.88/1.52  
% 7.88/1.52  ------ QBF Options
% 7.88/1.52  
% 7.88/1.52  --qbf_mode                              false
% 7.88/1.52  --qbf_elim_univ                         false
% 7.88/1.52  --qbf_dom_inst                          none
% 7.88/1.52  --qbf_dom_pre_inst                      false
% 7.88/1.52  --qbf_sk_in                             false
% 7.88/1.52  --qbf_pred_elim                         true
% 7.88/1.52  --qbf_split                             512
% 7.88/1.52  
% 7.88/1.52  ------ BMC1 Options
% 7.88/1.52  
% 7.88/1.52  --bmc1_incremental                      false
% 7.88/1.52  --bmc1_axioms                           reachable_all
% 7.88/1.52  --bmc1_min_bound                        0
% 7.88/1.52  --bmc1_max_bound                        -1
% 7.88/1.52  --bmc1_max_bound_default                -1
% 7.88/1.52  --bmc1_symbol_reachability              true
% 7.88/1.52  --bmc1_property_lemmas                  false
% 7.88/1.52  --bmc1_k_induction                      false
% 7.88/1.52  --bmc1_non_equiv_states                 false
% 7.88/1.52  --bmc1_deadlock                         false
% 7.88/1.52  --bmc1_ucm                              false
% 7.88/1.52  --bmc1_add_unsat_core                   none
% 7.88/1.52  --bmc1_unsat_core_children              false
% 7.88/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.52  --bmc1_out_stat                         full
% 7.88/1.52  --bmc1_ground_init                      false
% 7.88/1.52  --bmc1_pre_inst_next_state              false
% 7.88/1.52  --bmc1_pre_inst_state                   false
% 7.88/1.52  --bmc1_pre_inst_reach_state             false
% 7.88/1.52  --bmc1_out_unsat_core                   false
% 7.88/1.52  --bmc1_aig_witness_out                  false
% 7.88/1.52  --bmc1_verbose                          false
% 7.88/1.52  --bmc1_dump_clauses_tptp                false
% 7.88/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.52  --bmc1_dump_file                        -
% 7.88/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.52  --bmc1_ucm_extend_mode                  1
% 7.88/1.52  --bmc1_ucm_init_mode                    2
% 7.88/1.52  --bmc1_ucm_cone_mode                    none
% 7.88/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.52  --bmc1_ucm_relax_model                  4
% 7.88/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.52  --bmc1_ucm_layered_model                none
% 7.88/1.52  --bmc1_ucm_max_lemma_size               10
% 7.88/1.52  
% 7.88/1.52  ------ AIG Options
% 7.88/1.52  
% 7.88/1.52  --aig_mode                              false
% 7.88/1.52  
% 7.88/1.52  ------ Instantiation Options
% 7.88/1.52  
% 7.88/1.52  --instantiation_flag                    true
% 7.88/1.52  --inst_sos_flag                         true
% 7.88/1.52  --inst_sos_phase                        true
% 7.88/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.52  --inst_lit_sel_side                     num_symb
% 7.88/1.52  --inst_solver_per_active                1400
% 7.88/1.52  --inst_solver_calls_frac                1.
% 7.88/1.52  --inst_passive_queue_type               priority_queues
% 7.88/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.52  --inst_passive_queues_freq              [25;2]
% 7.88/1.52  --inst_dismatching                      true
% 7.88/1.52  --inst_eager_unprocessed_to_passive     true
% 7.88/1.52  --inst_prop_sim_given                   true
% 7.88/1.52  --inst_prop_sim_new                     false
% 7.88/1.52  --inst_subs_new                         false
% 7.88/1.52  --inst_eq_res_simp                      false
% 7.88/1.52  --inst_subs_given                       false
% 7.88/1.52  --inst_orphan_elimination               true
% 7.88/1.52  --inst_learning_loop_flag               true
% 7.88/1.52  --inst_learning_start                   3000
% 7.88/1.52  --inst_learning_factor                  2
% 7.88/1.52  --inst_start_prop_sim_after_learn       3
% 7.88/1.52  --inst_sel_renew                        solver
% 7.88/1.52  --inst_lit_activity_flag                true
% 7.88/1.52  --inst_restr_to_given                   false
% 7.88/1.52  --inst_activity_threshold               500
% 7.88/1.52  --inst_out_proof                        true
% 7.88/1.52  
% 7.88/1.52  ------ Resolution Options
% 7.88/1.52  
% 7.88/1.52  --resolution_flag                       true
% 7.88/1.52  --res_lit_sel                           adaptive
% 7.88/1.52  --res_lit_sel_side                      none
% 7.88/1.52  --res_ordering                          kbo
% 7.88/1.52  --res_to_prop_solver                    active
% 7.88/1.52  --res_prop_simpl_new                    false
% 7.88/1.52  --res_prop_simpl_given                  true
% 7.88/1.52  --res_passive_queue_type                priority_queues
% 7.88/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.52  --res_passive_queues_freq               [15;5]
% 7.88/1.52  --res_forward_subs                      full
% 7.88/1.52  --res_backward_subs                     full
% 7.88/1.52  --res_forward_subs_resolution           true
% 7.88/1.52  --res_backward_subs_resolution          true
% 7.88/1.52  --res_orphan_elimination                true
% 7.88/1.52  --res_time_limit                        2.
% 7.88/1.52  --res_out_proof                         true
% 7.88/1.52  
% 7.88/1.52  ------ Superposition Options
% 7.88/1.52  
% 7.88/1.52  --superposition_flag                    true
% 7.88/1.52  --sup_passive_queue_type                priority_queues
% 7.88/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.52  --demod_completeness_check              fast
% 7.88/1.52  --demod_use_ground                      true
% 7.88/1.52  --sup_to_prop_solver                    passive
% 7.88/1.52  --sup_prop_simpl_new                    true
% 7.88/1.52  --sup_prop_simpl_given                  true
% 7.88/1.52  --sup_fun_splitting                     true
% 7.88/1.52  --sup_smt_interval                      50000
% 7.88/1.52  
% 7.88/1.52  ------ Superposition Simplification Setup
% 7.88/1.52  
% 7.88/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.88/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.88/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.88/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.88/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.88/1.52  --sup_immed_triv                        [TrivRules]
% 7.88/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.52  --sup_immed_bw_main                     []
% 7.88/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.88/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.52  --sup_input_bw                          []
% 7.88/1.52  
% 7.88/1.52  ------ Combination Options
% 7.88/1.52  
% 7.88/1.52  --comb_res_mult                         3
% 7.88/1.52  --comb_sup_mult                         2
% 7.88/1.52  --comb_inst_mult                        10
% 7.88/1.52  
% 7.88/1.52  ------ Debug Options
% 7.88/1.52  
% 7.88/1.52  --dbg_backtrace                         false
% 7.88/1.52  --dbg_dump_prop_clauses                 false
% 7.88/1.52  --dbg_dump_prop_clauses_file            -
% 7.88/1.52  --dbg_out_stat                          false
% 7.88/1.52  ------ Parsing...
% 7.88/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.88/1.52  
% 7.88/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.88/1.52  
% 7.88/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.88/1.52  
% 7.88/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.88/1.52  ------ Proving...
% 7.88/1.52  ------ Problem Properties 
% 7.88/1.52  
% 7.88/1.52  
% 7.88/1.52  clauses                                 20
% 7.88/1.52  conjectures                             3
% 7.88/1.52  EPR                                     3
% 7.88/1.52  Horn                                    13
% 7.88/1.52  unary                                   4
% 7.88/1.52  binary                                  11
% 7.88/1.52  lits                                    42
% 7.88/1.52  lits eq                                 13
% 7.88/1.52  fd_pure                                 0
% 7.88/1.52  fd_pseudo                               0
% 7.88/1.52  fd_cond                                 2
% 7.88/1.52  fd_pseudo_cond                          3
% 7.88/1.52  AC symbols                              0
% 7.88/1.52  
% 7.88/1.52  ------ Schedule dynamic 5 is on 
% 7.88/1.52  
% 7.88/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.88/1.52  
% 7.88/1.52  
% 7.88/1.52  ------ 
% 7.88/1.52  Current options:
% 7.88/1.52  ------ 
% 7.88/1.52  
% 7.88/1.52  ------ Input Options
% 7.88/1.52  
% 7.88/1.52  --out_options                           all
% 7.88/1.52  --tptp_safe_out                         true
% 7.88/1.52  --problem_path                          ""
% 7.88/1.52  --include_path                          ""
% 7.88/1.52  --clausifier                            res/vclausify_rel
% 7.88/1.52  --clausifier_options                    ""
% 7.88/1.52  --stdin                                 false
% 7.88/1.52  --stats_out                             all
% 7.88/1.52  
% 7.88/1.52  ------ General Options
% 7.88/1.52  
% 7.88/1.52  --fof                                   false
% 7.88/1.52  --time_out_real                         305.
% 7.88/1.52  --time_out_virtual                      -1.
% 7.88/1.52  --symbol_type_check                     false
% 7.88/1.52  --clausify_out                          false
% 7.88/1.52  --sig_cnt_out                           false
% 7.88/1.52  --trig_cnt_out                          false
% 7.88/1.52  --trig_cnt_out_tolerance                1.
% 7.88/1.52  --trig_cnt_out_sk_spl                   false
% 7.88/1.52  --abstr_cl_out                          false
% 7.88/1.52  
% 7.88/1.52  ------ Global Options
% 7.88/1.52  
% 7.88/1.52  --schedule                              default
% 7.88/1.52  --add_important_lit                     false
% 7.88/1.52  --prop_solver_per_cl                    1000
% 7.88/1.52  --min_unsat_core                        false
% 7.88/1.52  --soft_assumptions                      false
% 7.88/1.52  --soft_lemma_size                       3
% 7.88/1.52  --prop_impl_unit_size                   0
% 7.88/1.52  --prop_impl_unit                        []
% 7.88/1.52  --share_sel_clauses                     true
% 7.88/1.52  --reset_solvers                         false
% 7.88/1.52  --bc_imp_inh                            [conj_cone]
% 7.88/1.52  --conj_cone_tolerance                   3.
% 7.88/1.52  --extra_neg_conj                        none
% 7.88/1.52  --large_theory_mode                     true
% 7.88/1.52  --prolific_symb_bound                   200
% 7.88/1.52  --lt_threshold                          2000
% 7.88/1.52  --clause_weak_htbl                      true
% 7.88/1.52  --gc_record_bc_elim                     false
% 7.88/1.52  
% 7.88/1.52  ------ Preprocessing Options
% 7.88/1.52  
% 7.88/1.52  --preprocessing_flag                    true
% 7.88/1.52  --time_out_prep_mult                    0.1
% 7.88/1.52  --splitting_mode                        input
% 7.88/1.52  --splitting_grd                         true
% 7.88/1.52  --splitting_cvd                         false
% 7.88/1.52  --splitting_cvd_svl                     false
% 7.88/1.52  --splitting_nvd                         32
% 7.88/1.52  --sub_typing                            true
% 7.88/1.52  --prep_gs_sim                           true
% 7.88/1.52  --prep_unflatten                        true
% 7.88/1.52  --prep_res_sim                          true
% 7.88/1.52  --prep_upred                            true
% 7.88/1.52  --prep_sem_filter                       exhaustive
% 7.88/1.52  --prep_sem_filter_out                   false
% 7.88/1.52  --pred_elim                             true
% 7.88/1.52  --res_sim_input                         true
% 7.88/1.52  --eq_ax_congr_red                       true
% 7.88/1.52  --pure_diseq_elim                       true
% 7.88/1.52  --brand_transform                       false
% 7.88/1.52  --non_eq_to_eq                          false
% 7.88/1.52  --prep_def_merge                        true
% 7.88/1.52  --prep_def_merge_prop_impl              false
% 7.88/1.52  --prep_def_merge_mbd                    true
% 7.88/1.52  --prep_def_merge_tr_red                 false
% 7.88/1.52  --prep_def_merge_tr_cl                  false
% 7.88/1.52  --smt_preprocessing                     true
% 7.88/1.52  --smt_ac_axioms                         fast
% 7.88/1.52  --preprocessed_out                      false
% 7.88/1.52  --preprocessed_stats                    false
% 7.88/1.52  
% 7.88/1.52  ------ Abstraction refinement Options
% 7.88/1.52  
% 7.88/1.52  --abstr_ref                             []
% 7.88/1.52  --abstr_ref_prep                        false
% 7.88/1.52  --abstr_ref_until_sat                   false
% 7.88/1.52  --abstr_ref_sig_restrict                funpre
% 7.88/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.52  --abstr_ref_under                       []
% 7.88/1.52  
% 7.88/1.52  ------ SAT Options
% 7.88/1.52  
% 7.88/1.52  --sat_mode                              false
% 7.88/1.52  --sat_fm_restart_options                ""
% 7.88/1.52  --sat_gr_def                            false
% 7.88/1.52  --sat_epr_types                         true
% 7.88/1.52  --sat_non_cyclic_types                  false
% 7.88/1.52  --sat_finite_models                     false
% 7.88/1.52  --sat_fm_lemmas                         false
% 7.88/1.52  --sat_fm_prep                           false
% 7.88/1.52  --sat_fm_uc_incr                        true
% 7.88/1.52  --sat_out_model                         small
% 7.88/1.52  --sat_out_clauses                       false
% 7.88/1.52  
% 7.88/1.52  ------ QBF Options
% 7.88/1.52  
% 7.88/1.52  --qbf_mode                              false
% 7.88/1.52  --qbf_elim_univ                         false
% 7.88/1.52  --qbf_dom_inst                          none
% 7.88/1.52  --qbf_dom_pre_inst                      false
% 7.88/1.52  --qbf_sk_in                             false
% 7.88/1.52  --qbf_pred_elim                         true
% 7.88/1.52  --qbf_split                             512
% 7.88/1.52  
% 7.88/1.52  ------ BMC1 Options
% 7.88/1.52  
% 7.88/1.52  --bmc1_incremental                      false
% 7.88/1.52  --bmc1_axioms                           reachable_all
% 7.88/1.52  --bmc1_min_bound                        0
% 7.88/1.52  --bmc1_max_bound                        -1
% 7.88/1.52  --bmc1_max_bound_default                -1
% 7.88/1.52  --bmc1_symbol_reachability              true
% 7.88/1.52  --bmc1_property_lemmas                  false
% 7.88/1.52  --bmc1_k_induction                      false
% 7.88/1.52  --bmc1_non_equiv_states                 false
% 7.88/1.52  --bmc1_deadlock                         false
% 7.88/1.52  --bmc1_ucm                              false
% 7.88/1.52  --bmc1_add_unsat_core                   none
% 7.88/1.52  --bmc1_unsat_core_children              false
% 7.88/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.52  --bmc1_out_stat                         full
% 7.88/1.52  --bmc1_ground_init                      false
% 7.88/1.52  --bmc1_pre_inst_next_state              false
% 7.88/1.52  --bmc1_pre_inst_state                   false
% 7.88/1.52  --bmc1_pre_inst_reach_state             false
% 7.88/1.52  --bmc1_out_unsat_core                   false
% 7.88/1.52  --bmc1_aig_witness_out                  false
% 7.88/1.52  --bmc1_verbose                          false
% 7.88/1.52  --bmc1_dump_clauses_tptp                false
% 7.88/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.52  --bmc1_dump_file                        -
% 7.88/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.52  --bmc1_ucm_extend_mode                  1
% 7.88/1.52  --bmc1_ucm_init_mode                    2
% 7.88/1.52  --bmc1_ucm_cone_mode                    none
% 7.88/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.52  --bmc1_ucm_relax_model                  4
% 7.88/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.52  --bmc1_ucm_layered_model                none
% 7.88/1.52  --bmc1_ucm_max_lemma_size               10
% 7.88/1.52  
% 7.88/1.52  ------ AIG Options
% 7.88/1.52  
% 7.88/1.52  --aig_mode                              false
% 7.88/1.52  
% 7.88/1.52  ------ Instantiation Options
% 7.88/1.52  
% 7.88/1.52  --instantiation_flag                    true
% 7.88/1.52  --inst_sos_flag                         true
% 7.88/1.52  --inst_sos_phase                        true
% 7.88/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.52  --inst_lit_sel_side                     none
% 7.88/1.52  --inst_solver_per_active                1400
% 7.88/1.52  --inst_solver_calls_frac                1.
% 7.88/1.52  --inst_passive_queue_type               priority_queues
% 7.88/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.52  --inst_passive_queues_freq              [25;2]
% 7.88/1.52  --inst_dismatching                      true
% 7.88/1.52  --inst_eager_unprocessed_to_passive     true
% 7.88/1.52  --inst_prop_sim_given                   true
% 7.88/1.52  --inst_prop_sim_new                     false
% 7.88/1.52  --inst_subs_new                         false
% 7.88/1.52  --inst_eq_res_simp                      false
% 7.88/1.52  --inst_subs_given                       false
% 7.88/1.52  --inst_orphan_elimination               true
% 7.88/1.52  --inst_learning_loop_flag               true
% 7.88/1.52  --inst_learning_start                   3000
% 7.88/1.52  --inst_learning_factor                  2
% 7.88/1.52  --inst_start_prop_sim_after_learn       3
% 7.88/1.52  --inst_sel_renew                        solver
% 7.88/1.52  --inst_lit_activity_flag                true
% 7.88/1.52  --inst_restr_to_given                   false
% 7.88/1.52  --inst_activity_threshold               500
% 7.88/1.52  --inst_out_proof                        true
% 7.88/1.52  
% 7.88/1.52  ------ Resolution Options
% 7.88/1.52  
% 7.88/1.52  --resolution_flag                       false
% 7.88/1.52  --res_lit_sel                           adaptive
% 7.88/1.52  --res_lit_sel_side                      none
% 7.88/1.52  --res_ordering                          kbo
% 7.88/1.52  --res_to_prop_solver                    active
% 7.88/1.52  --res_prop_simpl_new                    false
% 7.88/1.52  --res_prop_simpl_given                  true
% 7.88/1.52  --res_passive_queue_type                priority_queues
% 7.88/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.52  --res_passive_queues_freq               [15;5]
% 7.88/1.52  --res_forward_subs                      full
% 7.88/1.52  --res_backward_subs                     full
% 7.88/1.52  --res_forward_subs_resolution           true
% 7.88/1.52  --res_backward_subs_resolution          true
% 7.88/1.52  --res_orphan_elimination                true
% 7.88/1.52  --res_time_limit                        2.
% 7.88/1.52  --res_out_proof                         true
% 7.88/1.52  
% 7.88/1.52  ------ Superposition Options
% 7.88/1.52  
% 7.88/1.52  --superposition_flag                    true
% 7.88/1.52  --sup_passive_queue_type                priority_queues
% 7.88/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.52  --demod_completeness_check              fast
% 7.88/1.52  --demod_use_ground                      true
% 7.88/1.52  --sup_to_prop_solver                    passive
% 7.88/1.52  --sup_prop_simpl_new                    true
% 7.88/1.52  --sup_prop_simpl_given                  true
% 7.88/1.52  --sup_fun_splitting                     true
% 7.88/1.52  --sup_smt_interval                      50000
% 7.88/1.52  
% 7.88/1.52  ------ Superposition Simplification Setup
% 7.88/1.52  
% 7.88/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.88/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.88/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.88/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.88/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.88/1.52  --sup_immed_triv                        [TrivRules]
% 7.88/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.52  --sup_immed_bw_main                     []
% 7.88/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.88/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.52  --sup_input_bw                          []
% 7.88/1.52  
% 7.88/1.52  ------ Combination Options
% 7.88/1.52  
% 7.88/1.52  --comb_res_mult                         3
% 7.88/1.52  --comb_sup_mult                         2
% 7.88/1.52  --comb_inst_mult                        10
% 7.88/1.52  
% 7.88/1.52  ------ Debug Options
% 7.88/1.52  
% 7.88/1.52  --dbg_backtrace                         false
% 7.88/1.52  --dbg_dump_prop_clauses                 false
% 7.88/1.52  --dbg_dump_prop_clauses_file            -
% 7.88/1.52  --dbg_out_stat                          false
% 7.88/1.52  
% 7.88/1.52  
% 7.88/1.52  
% 7.88/1.52  
% 7.88/1.52  ------ Proving...
% 7.88/1.52  
% 7.88/1.52  
% 7.88/1.52  % SZS status Theorem for theBenchmark.p
% 7.88/1.52  
% 7.88/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.88/1.52  
% 7.88/1.52  fof(f4,axiom,(
% 7.88/1.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f18,plain,(
% 7.88/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.88/1.52    inference(ennf_transformation,[],[f4])).
% 7.88/1.52  
% 7.88/1.52  fof(f28,plain,(
% 7.88/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 7.88/1.52    introduced(choice_axiom,[])).
% 7.88/1.52  
% 7.88/1.52  fof(f29,plain,(
% 7.88/1.52    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 7.88/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f28])).
% 7.88/1.52  
% 7.88/1.52  fof(f45,plain,(
% 7.88/1.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 7.88/1.52    inference(cnf_transformation,[],[f29])).
% 7.88/1.52  
% 7.88/1.52  fof(f14,conjecture,(
% 7.88/1.52    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f15,negated_conjecture,(
% 7.88/1.52    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.88/1.52    inference(negated_conjecture,[],[f14])).
% 7.88/1.52  
% 7.88/1.52  fof(f20,plain,(
% 7.88/1.52    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.88/1.52    inference(ennf_transformation,[],[f15])).
% 7.88/1.52  
% 7.88/1.52  fof(f33,plain,(
% 7.88/1.52    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK4 = X2 | ~r2_hidden(X2,sK3)) & k1_xboole_0 != sK3 & k1_tarski(sK4) != sK3)),
% 7.88/1.52    introduced(choice_axiom,[])).
% 7.88/1.52  
% 7.88/1.52  fof(f34,plain,(
% 7.88/1.52    ! [X2] : (sK4 = X2 | ~r2_hidden(X2,sK3)) & k1_xboole_0 != sK3 & k1_tarski(sK4) != sK3),
% 7.88/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f33])).
% 7.88/1.52  
% 7.88/1.52  fof(f60,plain,(
% 7.88/1.52    ( ! [X2] : (sK4 = X2 | ~r2_hidden(X2,sK3)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f34])).
% 7.88/1.52  
% 7.88/1.52  fof(f59,plain,(
% 7.88/1.52    k1_xboole_0 != sK3),
% 7.88/1.52    inference(cnf_transformation,[],[f34])).
% 7.88/1.52  
% 7.88/1.52  fof(f5,axiom,(
% 7.88/1.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f30,plain,(
% 7.88/1.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.88/1.52    inference(nnf_transformation,[],[f5])).
% 7.88/1.52  
% 7.88/1.52  fof(f47,plain,(
% 7.88/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f30])).
% 7.88/1.52  
% 7.88/1.52  fof(f12,axiom,(
% 7.88/1.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f32,plain,(
% 7.88/1.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.88/1.52    inference(nnf_transformation,[],[f12])).
% 7.88/1.52  
% 7.88/1.52  fof(f56,plain,(
% 7.88/1.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f32])).
% 7.88/1.52  
% 7.88/1.52  fof(f9,axiom,(
% 7.88/1.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f52,plain,(
% 7.88/1.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f9])).
% 7.88/1.52  
% 7.88/1.52  fof(f10,axiom,(
% 7.88/1.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f53,plain,(
% 7.88/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f10])).
% 7.88/1.52  
% 7.88/1.52  fof(f11,axiom,(
% 7.88/1.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f54,plain,(
% 7.88/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f11])).
% 7.88/1.52  
% 7.88/1.52  fof(f61,plain,(
% 7.88/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.88/1.52    inference(definition_unfolding,[],[f53,f54])).
% 7.88/1.52  
% 7.88/1.52  fof(f62,plain,(
% 7.88/1.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.88/1.52    inference(definition_unfolding,[],[f52,f61])).
% 7.88/1.52  
% 7.88/1.52  fof(f64,plain,(
% 7.88/1.52    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.88/1.52    inference(definition_unfolding,[],[f56,f62])).
% 7.88/1.52  
% 7.88/1.52  fof(f1,axiom,(
% 7.88/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f35,plain,(
% 7.88/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f1])).
% 7.88/1.52  
% 7.88/1.52  fof(f7,axiom,(
% 7.88/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f49,plain,(
% 7.88/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.88/1.52    inference(cnf_transformation,[],[f7])).
% 7.88/1.52  
% 7.88/1.52  fof(f63,plain,(
% 7.88/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.88/1.52    inference(definition_unfolding,[],[f35,f49,f49])).
% 7.88/1.52  
% 7.88/1.52  fof(f2,axiom,(
% 7.88/1.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f21,plain,(
% 7.88/1.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.88/1.52    inference(nnf_transformation,[],[f2])).
% 7.88/1.52  
% 7.88/1.52  fof(f22,plain,(
% 7.88/1.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.88/1.52    inference(flattening,[],[f21])).
% 7.88/1.52  
% 7.88/1.52  fof(f23,plain,(
% 7.88/1.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.88/1.52    inference(rectify,[],[f22])).
% 7.88/1.52  
% 7.88/1.52  fof(f24,plain,(
% 7.88/1.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.88/1.52    introduced(choice_axiom,[])).
% 7.88/1.52  
% 7.88/1.52  fof(f25,plain,(
% 7.88/1.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.88/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 7.88/1.52  
% 7.88/1.52  fof(f36,plain,(
% 7.88/1.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.88/1.52    inference(cnf_transformation,[],[f25])).
% 7.88/1.52  
% 7.88/1.52  fof(f70,plain,(
% 7.88/1.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.88/1.52    inference(equality_resolution,[],[f36])).
% 7.88/1.52  
% 7.88/1.52  fof(f6,axiom,(
% 7.88/1.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f48,plain,(
% 7.88/1.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.88/1.52    inference(cnf_transformation,[],[f6])).
% 7.88/1.52  
% 7.88/1.52  fof(f39,plain,(
% 7.88/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f25])).
% 7.88/1.52  
% 7.88/1.52  fof(f58,plain,(
% 7.88/1.52    k1_tarski(sK4) != sK3),
% 7.88/1.52    inference(cnf_transformation,[],[f34])).
% 7.88/1.52  
% 7.88/1.52  fof(f67,plain,(
% 7.88/1.52    k2_enumset1(sK4,sK4,sK4,sK4) != sK3),
% 7.88/1.52    inference(definition_unfolding,[],[f58,f62])).
% 7.88/1.52  
% 7.88/1.52  fof(f41,plain,(
% 7.88/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f25])).
% 7.88/1.52  
% 7.88/1.52  fof(f13,axiom,(
% 7.88/1.52    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f19,plain,(
% 7.88/1.52    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 7.88/1.52    inference(ennf_transformation,[],[f13])).
% 7.88/1.52  
% 7.88/1.52  fof(f57,plain,(
% 7.88/1.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 7.88/1.52    inference(cnf_transformation,[],[f19])).
% 7.88/1.52  
% 7.88/1.52  fof(f66,plain,(
% 7.88/1.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 7.88/1.52    inference(definition_unfolding,[],[f57,f62])).
% 7.88/1.52  
% 7.88/1.52  fof(f37,plain,(
% 7.88/1.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.88/1.52    inference(cnf_transformation,[],[f25])).
% 7.88/1.52  
% 7.88/1.52  fof(f69,plain,(
% 7.88/1.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.88/1.52    inference(equality_resolution,[],[f37])).
% 7.88/1.52  
% 7.88/1.52  fof(f8,axiom,(
% 7.88/1.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.88/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.52  
% 7.88/1.52  fof(f31,plain,(
% 7.88/1.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.88/1.52    inference(nnf_transformation,[],[f8])).
% 7.88/1.52  
% 7.88/1.52  fof(f51,plain,(
% 7.88/1.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 7.88/1.52    inference(cnf_transformation,[],[f31])).
% 7.88/1.52  
% 7.88/1.52  cnf(c_10,plain,
% 7.88/1.52      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 7.88/1.52      inference(cnf_transformation,[],[f45]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1064,plain,
% 7.88/1.52      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 7.88/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_19,negated_conjecture,
% 7.88/1.52      ( ~ r2_hidden(X0,sK3) | sK4 = X0 ),
% 7.88/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1060,plain,
% 7.88/1.52      ( sK4 = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 7.88/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1820,plain,
% 7.88/1.52      ( sK2(sK3) = sK4 | sK3 = k1_xboole_0 ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_1064,c_1060]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_20,negated_conjecture,
% 7.88/1.52      ( k1_xboole_0 != sK3 ),
% 7.88/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_676,plain,( X0 = X0 ),theory(equality) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_687,plain,
% 7.88/1.52      ( k1_xboole_0 = k1_xboole_0 ),
% 7.88/1.52      inference(instantiation,[status(thm)],[c_676]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_677,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1094,plain,
% 7.88/1.52      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.88/1.52      inference(instantiation,[status(thm)],[c_677]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1095,plain,
% 7.88/1.52      ( sK3 != k1_xboole_0
% 7.88/1.52      | k1_xboole_0 = sK3
% 7.88/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.88/1.52      inference(instantiation,[status(thm)],[c_1094]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1920,plain,
% 7.88/1.52      ( sK2(sK3) = sK4 ),
% 7.88/1.52      inference(global_propositional_subsumption,
% 7.88/1.52                [status(thm)],
% 7.88/1.52                [c_1820,c_20,c_687,c_1095]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1922,plain,
% 7.88/1.52      ( sK3 = k1_xboole_0 | r2_hidden(sK4,sK3) = iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_1920,c_1064]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_2177,plain,
% 7.88/1.52      ( r2_hidden(sK4,sK3) = iProver_top ),
% 7.88/1.52      inference(global_propositional_subsumption,
% 7.88/1.52                [status(thm)],
% 7.88/1.52                [c_1922,c_20,c_687,c_1095]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_11,plain,
% 7.88/1.52      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.88/1.52      inference(cnf_transformation,[],[f47]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_153,plain,
% 7.88/1.52      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.88/1.52      inference(prop_impl,[status(thm)],[c_11]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_16,plain,
% 7.88/1.52      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 7.88/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_161,plain,
% 7.88/1.52      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 7.88/1.52      inference(prop_impl,[status(thm)],[c_16]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_162,plain,
% 7.88/1.52      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 7.88/1.52      inference(renaming,[status(thm)],[c_161]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_281,plain,
% 7.88/1.52      ( ~ r2_hidden(X0,X1)
% 7.88/1.52      | X1 != X2
% 7.88/1.52      | k2_enumset1(X0,X0,X0,X0) != X3
% 7.88/1.52      | k4_xboole_0(X3,X2) = k1_xboole_0 ),
% 7.88/1.52      inference(resolution_lifted,[status(thm)],[c_153,c_162]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_282,plain,
% 7.88/1.52      ( ~ r2_hidden(X0,X1)
% 7.88/1.52      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0 ),
% 7.88/1.52      inference(unflattening,[status(thm)],[c_281]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_478,plain,
% 7.88/1.52      ( ~ r2_hidden(X0,X1)
% 7.88/1.52      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0 ),
% 7.88/1.52      inference(prop_impl,[status(thm)],[c_282]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1058,plain,
% 7.88/1.52      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
% 7.88/1.52      | r2_hidden(X0,X1) != iProver_top ),
% 7.88/1.52      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_2181,plain,
% 7.88/1.52      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = k1_xboole_0 ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_2177,c_1058]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_0,plain,
% 7.88/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.88/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_6,plain,
% 7.88/1.52      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.88/1.52      inference(cnf_transformation,[],[f70]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1068,plain,
% 7.88/1.52      ( r2_hidden(X0,X1) = iProver_top
% 7.88/1.52      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.88/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_2998,plain,
% 7.88/1.52      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.88/1.52      | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_1064,c_1068]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_32878,plain,
% 7.88/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.88/1.52      | r2_hidden(sK2(k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_0,c_2998]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_33667,plain,
% 7.88/1.52      ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = k1_xboole_0
% 7.88/1.52      | sK2(k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = sK4 ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_32878,c_1060]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_34817,plain,
% 7.88/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k1_xboole_0
% 7.88/1.52      | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = k1_xboole_0
% 7.88/1.52      | r2_hidden(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_33667,c_1064]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_37085,plain,
% 7.88/1.52      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = k1_xboole_0
% 7.88/1.52      | k4_xboole_0(sK3,k4_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0
% 7.88/1.52      | r2_hidden(sK4,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0)) = iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_2181,c_34817]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_37105,plain,
% 7.88/1.52      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = k1_xboole_0
% 7.88/1.52      | k4_xboole_0(sK3,k4_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0
% 7.88/1.52      | r2_hidden(sK4,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0)) = iProver_top ),
% 7.88/1.52      inference(light_normalisation,[status(thm)],[c_37085,c_2181]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_13,plain,
% 7.88/1.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.88/1.52      inference(cnf_transformation,[],[f48]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_2284,plain,
% 7.88/1.52      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_2181,c_0]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_2286,plain,
% 7.88/1.52      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.88/1.52      inference(demodulation,[status(thm)],[c_2284,c_13]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_37106,plain,
% 7.88/1.52      ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
% 7.88/1.52      | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.88/1.52      inference(demodulation,[status(thm)],[c_37105,c_13,c_2286]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_3,plain,
% 7.88/1.52      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.88/1.52      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.88/1.52      | k4_xboole_0(X0,X1) = X2 ),
% 7.88/1.52      inference(cnf_transformation,[],[f39]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1071,plain,
% 7.88/1.52      ( k4_xboole_0(X0,X1) = X2
% 7.88/1.52      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.88/1.52      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.88/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_8679,plain,
% 7.88/1.52      ( sK0(X0,X1,sK3) = sK4
% 7.88/1.52      | k4_xboole_0(X0,X1) = sK3
% 7.88/1.52      | r2_hidden(sK0(X0,X1,sK3),X0) = iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_1071,c_1060]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_2999,plain,
% 7.88/1.52      ( r2_hidden(X0,X1) = iProver_top
% 7.88/1.52      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_0,c_1068]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_9276,plain,
% 7.88/1.52      ( sK0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2,sK3) = sK4
% 7.88/1.52      | k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = sK3
% 7.88/1.52      | r2_hidden(sK0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2,sK3),X1) = iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_8679,c_2999]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_23290,plain,
% 7.88/1.52      ( sK0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),X1,sK3) = sK4
% 7.88/1.52      | k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),X1) = sK3 ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_9276,c_1060]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_24714,plain,
% 7.88/1.52      ( sK0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),X1,sK3) = sK4
% 7.88/1.52      | k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),X1) = sK3 ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_0,c_23290]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_24883,plain,
% 7.88/1.52      ( sK0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k1_xboole_0,sK3) = sK4
% 7.88/1.52      | k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = sK3 ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_24714,c_13]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_27579,plain,
% 7.88/1.52      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3) = sK4
% 7.88/1.52      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = sK3 ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_2286,c_24883]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_27813,plain,
% 7.88/1.52      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3) = sK4
% 7.88/1.52      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = sK3 ),
% 7.88/1.52      inference(light_normalisation,[status(thm)],[c_27579,c_2181]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_27814,plain,
% 7.88/1.52      ( k2_enumset1(sK4,sK4,sK4,sK4) = sK3
% 7.88/1.52      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3) = sK4 ),
% 7.88/1.52      inference(demodulation,[status(thm)],[c_27813,c_13]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_21,negated_conjecture,
% 7.88/1.52      ( k2_enumset1(sK4,sK4,sK4,sK4) != sK3 ),
% 7.88/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_28352,plain,
% 7.88/1.52      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3) = sK4 ),
% 7.88/1.52      inference(global_propositional_subsumption,
% 7.88/1.52                [status(thm)],
% 7.88/1.52                [c_27814,c_21]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1,plain,
% 7.88/1.52      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.88/1.52      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.88/1.52      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.88/1.52      | k4_xboole_0(X0,X1) = X2 ),
% 7.88/1.52      inference(cnf_transformation,[],[f41]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1073,plain,
% 7.88/1.52      ( k4_xboole_0(X0,X1) = X2
% 7.88/1.52      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 7.88/1.52      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 7.88/1.52      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 7.88/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_28354,plain,
% 7.88/1.52      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = sK3
% 7.88/1.52      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3),sK3) != iProver_top
% 7.88/1.52      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0,sK3),k1_xboole_0) = iProver_top
% 7.88/1.52      | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_28352,c_1073]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_28365,plain,
% 7.88/1.52      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = sK3
% 7.88/1.52      | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 7.88/1.52      | r2_hidden(sK4,sK3) != iProver_top
% 7.88/1.52      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 7.88/1.52      inference(light_normalisation,[status(thm)],[c_28354,c_28352]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_28366,plain,
% 7.88/1.52      ( k2_enumset1(sK4,sK4,sK4,sK4) = sK3
% 7.88/1.52      | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 7.88/1.52      | r2_hidden(sK4,sK3) != iProver_top
% 7.88/1.52      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 7.88/1.52      inference(demodulation,[status(thm)],[c_28365,c_13]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_18,plain,
% 7.88/1.52      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 7.88/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1202,plain,
% 7.88/1.52      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
% 7.88/1.52      | ~ r2_hidden(X0,sK3) ),
% 7.88/1.52      inference(instantiation,[status(thm)],[c_18]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_14947,plain,
% 7.88/1.52      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 7.88/1.52      | ~ r2_hidden(sK4,sK3) ),
% 7.88/1.52      inference(instantiation,[status(thm)],[c_1202]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_5,plain,
% 7.88/1.52      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.88/1.52      inference(cnf_transformation,[],[f69]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1069,plain,
% 7.88/1.52      ( r2_hidden(X0,X1) != iProver_top
% 7.88/1.52      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.88/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_3253,plain,
% 7.88/1.52      ( r2_hidden(X0,X1) != iProver_top
% 7.88/1.52      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_13,c_1069]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_3278,plain,
% 7.88/1.52      ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_2177,c_3253]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_14,plain,
% 7.88/1.52      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 7.88/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1063,plain,
% 7.88/1.52      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 7.88/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_2283,plain,
% 7.88/1.52      ( k2_enumset1(sK4,sK4,sK4,sK4) != k1_xboole_0
% 7.88/1.52      | r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = iProver_top ),
% 7.88/1.52      inference(superposition,[status(thm)],[c_2181,c_1063]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_2287,plain,
% 7.88/1.52      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 7.88/1.52      | k2_enumset1(sK4,sK4,sK4,sK4) != k1_xboole_0 ),
% 7.88/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_2283]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(c_1923,plain,
% 7.88/1.52      ( r2_hidden(sK4,sK3) | sK3 = k1_xboole_0 ),
% 7.88/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_1922]) ).
% 7.88/1.52  
% 7.88/1.52  cnf(contradiction,plain,
% 7.88/1.52      ( $false ),
% 7.88/1.52      inference(minisat,
% 7.88/1.52                [status(thm)],
% 7.88/1.52                [c_37106,c_28366,c_14947,c_3278,c_2287,c_1923,c_1922,
% 7.88/1.52                 c_1095,c_687,c_20,c_21]) ).
% 7.88/1.52  
% 7.88/1.52  
% 7.88/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.88/1.52  
% 7.88/1.52  ------                               Statistics
% 7.88/1.52  
% 7.88/1.52  ------ General
% 7.88/1.52  
% 7.88/1.52  abstr_ref_over_cycles:                  0
% 7.88/1.52  abstr_ref_under_cycles:                 0
% 7.88/1.52  gc_basic_clause_elim:                   0
% 7.88/1.52  forced_gc_time:                         0
% 7.88/1.52  parsing_time:                           0.014
% 7.88/1.52  unif_index_cands_time:                  0.
% 7.88/1.52  unif_index_add_time:                    0.
% 7.88/1.52  orderings_time:                         0.
% 7.88/1.52  out_proof_time:                         0.012
% 7.88/1.52  total_time:                             0.983
% 7.88/1.52  num_of_symbols:                         42
% 7.88/1.52  num_of_terms:                           32897
% 7.88/1.52  
% 7.88/1.52  ------ Preprocessing
% 7.88/1.52  
% 7.88/1.52  num_of_splits:                          0
% 7.88/1.52  num_of_split_atoms:                     0
% 7.88/1.52  num_of_reused_defs:                     0
% 7.88/1.52  num_eq_ax_congr_red:                    23
% 7.88/1.52  num_of_sem_filtered_clauses:            1
% 7.88/1.52  num_of_subtypes:                        0
% 7.88/1.52  monotx_restored_types:                  0
% 7.88/1.52  sat_num_of_epr_types:                   0
% 7.88/1.52  sat_num_of_non_cyclic_types:            0
% 7.88/1.52  sat_guarded_non_collapsed_types:        0
% 7.88/1.52  num_pure_diseq_elim:                    0
% 7.88/1.52  simp_replaced_by:                       0
% 7.88/1.52  res_preprocessed:                       95
% 7.88/1.52  prep_upred:                             0
% 7.88/1.52  prep_unflattend:                        16
% 7.88/1.52  smt_new_axioms:                         0
% 7.88/1.52  pred_elim_cands:                        2
% 7.88/1.52  pred_elim:                              1
% 7.88/1.52  pred_elim_cl:                           2
% 7.88/1.52  pred_elim_cycles:                       3
% 7.88/1.52  merged_defs:                            18
% 7.88/1.52  merged_defs_ncl:                        0
% 7.88/1.52  bin_hyper_res:                          18
% 7.88/1.52  prep_cycles:                            4
% 7.88/1.52  pred_elim_time:                         0.014
% 7.88/1.52  splitting_time:                         0.
% 7.88/1.52  sem_filter_time:                        0.
% 7.88/1.52  monotx_time:                            0.
% 7.88/1.52  subtype_inf_time:                       0.
% 7.88/1.52  
% 7.88/1.52  ------ Problem properties
% 7.88/1.52  
% 7.88/1.52  clauses:                                20
% 7.88/1.52  conjectures:                            3
% 7.88/1.52  epr:                                    3
% 7.88/1.52  horn:                                   13
% 7.88/1.52  ground:                                 2
% 7.88/1.52  unary:                                  4
% 7.88/1.52  binary:                                 11
% 7.88/1.52  lits:                                   42
% 7.88/1.52  lits_eq:                                13
% 7.88/1.52  fd_pure:                                0
% 7.88/1.52  fd_pseudo:                              0
% 7.88/1.52  fd_cond:                                2
% 7.88/1.52  fd_pseudo_cond:                         3
% 7.88/1.52  ac_symbols:                             0
% 7.88/1.52  
% 7.88/1.52  ------ Propositional Solver
% 7.88/1.52  
% 7.88/1.52  prop_solver_calls:                      31
% 7.88/1.52  prop_fast_solver_calls:                 964
% 7.88/1.52  smt_solver_calls:                       0
% 7.88/1.52  smt_fast_solver_calls:                  0
% 7.88/1.52  prop_num_of_clauses:                    15039
% 7.88/1.52  prop_preprocess_simplified:             23566
% 7.88/1.52  prop_fo_subsumed:                       26
% 7.88/1.52  prop_solver_time:                       0.
% 7.88/1.52  smt_solver_time:                        0.
% 7.88/1.52  smt_fast_solver_time:                   0.
% 7.88/1.52  prop_fast_solver_time:                  0.
% 7.88/1.52  prop_unsat_core_time:                   0.001
% 7.88/1.52  
% 7.88/1.52  ------ QBF
% 7.88/1.52  
% 7.88/1.52  qbf_q_res:                              0
% 7.88/1.52  qbf_num_tautologies:                    0
% 7.88/1.52  qbf_prep_cycles:                        0
% 7.88/1.52  
% 7.88/1.52  ------ BMC1
% 7.88/1.52  
% 7.88/1.52  bmc1_current_bound:                     -1
% 7.88/1.52  bmc1_last_solved_bound:                 -1
% 7.88/1.52  bmc1_unsat_core_size:                   -1
% 7.88/1.52  bmc1_unsat_core_parents_size:           -1
% 7.88/1.52  bmc1_merge_next_fun:                    0
% 7.88/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.88/1.52  
% 7.88/1.52  ------ Instantiation
% 7.88/1.52  
% 7.88/1.52  inst_num_of_clauses:                    2947
% 7.88/1.52  inst_num_in_passive:                    1219
% 7.88/1.52  inst_num_in_active:                     782
% 7.88/1.52  inst_num_in_unprocessed:                946
% 7.88/1.52  inst_num_of_loops:                      980
% 7.88/1.52  inst_num_of_learning_restarts:          0
% 7.88/1.52  inst_num_moves_active_passive:          198
% 7.88/1.52  inst_lit_activity:                      0
% 7.88/1.52  inst_lit_activity_moves:                0
% 7.88/1.52  inst_num_tautologies:                   0
% 7.88/1.52  inst_num_prop_implied:                  0
% 7.88/1.52  inst_num_existing_simplified:           0
% 7.88/1.52  inst_num_eq_res_simplified:             0
% 7.88/1.52  inst_num_child_elim:                    0
% 7.88/1.52  inst_num_of_dismatching_blockings:      4096
% 7.88/1.52  inst_num_of_non_proper_insts:           4602
% 7.88/1.52  inst_num_of_duplicates:                 0
% 7.88/1.52  inst_inst_num_from_inst_to_res:         0
% 7.88/1.52  inst_dismatching_checking_time:         0.
% 7.88/1.52  
% 7.88/1.52  ------ Resolution
% 7.88/1.52  
% 7.88/1.52  res_num_of_clauses:                     0
% 7.88/1.52  res_num_in_passive:                     0
% 7.88/1.52  res_num_in_active:                      0
% 7.88/1.52  res_num_of_loops:                       99
% 7.88/1.52  res_forward_subset_subsumed:            190
% 7.88/1.52  res_backward_subset_subsumed:           0
% 7.88/1.52  res_forward_subsumed:                   0
% 7.88/1.52  res_backward_subsumed:                  0
% 7.88/1.52  res_forward_subsumption_resolution:     0
% 7.88/1.52  res_backward_subsumption_resolution:    0
% 7.88/1.52  res_clause_to_clause_subsumption:       13049
% 7.88/1.52  res_orphan_elimination:                 0
% 7.88/1.52  res_tautology_del:                      332
% 7.88/1.52  res_num_eq_res_simplified:              0
% 7.88/1.52  res_num_sel_changes:                    0
% 7.88/1.52  res_moves_from_active_to_pass:          0
% 7.88/1.52  
% 7.88/1.52  ------ Superposition
% 7.88/1.52  
% 7.88/1.52  sup_time_total:                         0.
% 7.88/1.52  sup_time_generating:                    0.
% 7.88/1.52  sup_time_sim_full:                      0.
% 7.88/1.52  sup_time_sim_immed:                     0.
% 7.88/1.52  
% 7.88/1.52  sup_num_of_clauses:                     1337
% 7.88/1.52  sup_num_in_active:                      140
% 7.88/1.52  sup_num_in_passive:                     1197
% 7.88/1.52  sup_num_of_loops:                       194
% 7.88/1.52  sup_fw_superposition:                   1880
% 7.88/1.52  sup_bw_superposition:                   2189
% 7.88/1.52  sup_immediate_simplified:               1919
% 7.88/1.52  sup_given_eliminated:                   4
% 7.88/1.52  comparisons_done:                       0
% 7.88/1.52  comparisons_avoided:                    115
% 7.88/1.52  
% 7.88/1.52  ------ Simplifications
% 7.88/1.52  
% 7.88/1.52  
% 7.88/1.52  sim_fw_subset_subsumed:                 696
% 7.88/1.52  sim_bw_subset_subsumed:                 304
% 7.88/1.52  sim_fw_subsumed:                        474
% 7.88/1.52  sim_bw_subsumed:                        27
% 7.88/1.52  sim_fw_subsumption_res:                 0
% 7.88/1.52  sim_bw_subsumption_res:                 0
% 7.88/1.52  sim_tautology_del:                      104
% 7.88/1.52  sim_eq_tautology_del:                   233
% 7.88/1.52  sim_eq_res_simp:                        13
% 7.88/1.52  sim_fw_demodulated:                     627
% 7.88/1.52  sim_bw_demodulated:                     29
% 7.88/1.52  sim_light_normalised:                   581
% 7.88/1.52  sim_joinable_taut:                      0
% 7.88/1.52  sim_joinable_simp:                      0
% 7.88/1.52  sim_ac_normalised:                      0
% 7.88/1.52  sim_smt_subsumption:                    0
% 7.88/1.52  
%------------------------------------------------------------------------------
