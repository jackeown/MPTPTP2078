%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:21 EST 2020

% Result     : Theorem 19.96s
% Output     : CNFRefutation 19.96s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 236 expanded)
%              Number of clauses        :   47 (  90 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 ( 470 expanded)
%              Number of equality atoms :  103 ( 200 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK2(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f40,f52])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f15,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f15])).

fof(f18,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f16])).

fof(f51,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14307,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_14302,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14306,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14444,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14302,c_14306])).

cnf(c_14470,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14307,c_14444])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14304,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_194,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1),k1_relat_1(X1))
    | ~ v1_xboole_0(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1),k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_194])).

cnf(c_14300,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X1),k1_relat_1(X1)) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_14424,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | r2_hidden(sK2(X0),k1_relat_1(X0)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14304,c_14300])).

cnf(c_2,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14305,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14893,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | r2_hidden(sK2(X0),X1) != iProver_top
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14424,c_14305])).

cnf(c_15108,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0),X0) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14470,c_14893])).

cnf(c_50,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14892,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14470,c_14424])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14399,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_6,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14376,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_14404,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14399,c_14376])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14303,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14524,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14404,c_14303])).

cnf(c_15107,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | r2_hidden(sK2(X0),k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14524,c_14893])).

cnf(c_15124,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15107])).

cnf(c_15133,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15108,c_50,c_14892,c_15124])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_183,plain,
    ( ~ v1_xboole_0(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_12])).

cnf(c_14301,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_14556,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14307,c_14301])).

cnf(c_14563,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_14556,c_14470])).

cnf(c_15140,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k3_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_15133,c_14563])).

cnf(c_15142,plain,
    ( k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15140,c_6])).

cnf(c_477,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2201,plain,
    ( X0 = X1
    | X1 != k1_xboole_0
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_2272,plain,
    ( k3_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2201])).

cnf(c_48,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15142,c_2272,c_0,c_48,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:46:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.96/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.96/3.00  
% 19.96/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.96/3.00  
% 19.96/3.00  ------  iProver source info
% 19.96/3.00  
% 19.96/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.96/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.96/3.00  git: non_committed_changes: false
% 19.96/3.00  git: last_make_outside_of_git: false
% 19.96/3.00  
% 19.96/3.00  ------ 
% 19.96/3.00  ------ Parsing...
% 19.96/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  ------ Proving...
% 19.96/3.00  ------ Problem Properties 
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  clauses                                 15
% 19.96/3.00  conjectures                             2
% 19.96/3.00  EPR                                     3
% 19.96/3.00  Horn                                    12
% 19.96/3.00  unary                                   5
% 19.96/3.00  binary                                  8
% 19.96/3.00  lits                                    27
% 19.96/3.00  lits eq                                 9
% 19.96/3.00  fd_pure                                 0
% 19.96/3.00  fd_pseudo                               0
% 19.96/3.00  fd_cond                                 2
% 19.96/3.00  fd_pseudo_cond                          0
% 19.96/3.00  AC symbols                              0
% 19.96/3.00  
% 19.96/3.00  ------ Input Options Time Limit: Unbounded
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 19.96/3.00  Current options:
% 19.96/3.00  ------ 
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  % SZS status Theorem for theBenchmark.p
% 19.96/3.00  
% 19.96/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.96/3.00  
% 19.96/3.00  fof(f1,axiom,(
% 19.96/3.00    v1_xboole_0(k1_xboole_0)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f34,plain,(
% 19.96/3.00    v1_xboole_0(k1_xboole_0)),
% 19.96/3.00    inference(cnf_transformation,[],[f1])).
% 19.96/3.00  
% 19.96/3.00  fof(f13,axiom,(
% 19.96/3.00    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f24,plain,(
% 19.96/3.00    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 19.96/3.00    inference(ennf_transformation,[],[f13])).
% 19.96/3.00  
% 19.96/3.00  fof(f49,plain,(
% 19.96/3.00    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f24])).
% 19.96/3.00  
% 19.96/3.00  fof(f2,axiom,(
% 19.96/3.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f19,plain,(
% 19.96/3.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 19.96/3.00    inference(ennf_transformation,[],[f2])).
% 19.96/3.00  
% 19.96/3.00  fof(f35,plain,(
% 19.96/3.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f19])).
% 19.96/3.00  
% 19.96/3.00  fof(f4,axiom,(
% 19.96/3.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f21,plain,(
% 19.96/3.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 19.96/3.00    inference(ennf_transformation,[],[f4])).
% 19.96/3.00  
% 19.96/3.00  fof(f29,plain,(
% 19.96/3.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 19.96/3.00    introduced(choice_axiom,[])).
% 19.96/3.00  
% 19.96/3.00  fof(f30,plain,(
% 19.96/3.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 19.96/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).
% 19.96/3.00  
% 19.96/3.00  fof(f39,plain,(
% 19.96/3.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 19.96/3.00    inference(cnf_transformation,[],[f30])).
% 19.96/3.00  
% 19.96/3.00  fof(f11,axiom,(
% 19.96/3.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f22,plain,(
% 19.96/3.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 19.96/3.00    inference(ennf_transformation,[],[f11])).
% 19.96/3.00  
% 19.96/3.00  fof(f47,plain,(
% 19.96/3.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f22])).
% 19.96/3.00  
% 19.96/3.00  fof(f14,axiom,(
% 19.96/3.00    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f25,plain,(
% 19.96/3.00    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 19.96/3.00    inference(ennf_transformation,[],[f14])).
% 19.96/3.00  
% 19.96/3.00  fof(f26,plain,(
% 19.96/3.00    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.96/3.00    inference(flattening,[],[f25])).
% 19.96/3.00  
% 19.96/3.00  fof(f32,plain,(
% 19.96/3.00    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK2(X1),k1_relat_1(X1)))),
% 19.96/3.00    introduced(choice_axiom,[])).
% 19.96/3.00  
% 19.96/3.00  fof(f33,plain,(
% 19.96/3.00    ! [X0,X1] : (r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.96/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f32])).
% 19.96/3.00  
% 19.96/3.00  fof(f50,plain,(
% 19.96/3.00    ( ! [X0,X1] : (r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f33])).
% 19.96/3.00  
% 19.96/3.00  fof(f3,axiom,(
% 19.96/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f17,plain,(
% 19.96/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.96/3.00    inference(rectify,[],[f3])).
% 19.96/3.00  
% 19.96/3.00  fof(f20,plain,(
% 19.96/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.96/3.00    inference(ennf_transformation,[],[f17])).
% 19.96/3.00  
% 19.96/3.00  fof(f27,plain,(
% 19.96/3.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.96/3.00    introduced(choice_axiom,[])).
% 19.96/3.00  
% 19.96/3.00  fof(f28,plain,(
% 19.96/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.96/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f27])).
% 19.96/3.00  
% 19.96/3.00  fof(f38,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f28])).
% 19.96/3.00  
% 19.96/3.00  fof(f6,axiom,(
% 19.96/3.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f41,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f6])).
% 19.96/3.00  
% 19.96/3.00  fof(f10,axiom,(
% 19.96/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f46,plain,(
% 19.96/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.96/3.00    inference(cnf_transformation,[],[f10])).
% 19.96/3.00  
% 19.96/3.00  fof(f9,axiom,(
% 19.96/3.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.01  
% 19.96/3.01  fof(f45,plain,(
% 19.96/3.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.96/3.01    inference(cnf_transformation,[],[f9])).
% 19.96/3.01  
% 19.96/3.01  fof(f52,plain,(
% 19.96/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 19.96/3.01    inference(definition_unfolding,[],[f46,f45])).
% 19.96/3.01  
% 19.96/3.01  fof(f54,plain,(
% 19.96/3.01    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 19.96/3.01    inference(definition_unfolding,[],[f41,f52])).
% 19.96/3.01  
% 19.96/3.01  fof(f7,axiom,(
% 19.96/3.01    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 19.96/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.01  
% 19.96/3.01  fof(f42,plain,(
% 19.96/3.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 19.96/3.01    inference(cnf_transformation,[],[f7])).
% 19.96/3.01  
% 19.96/3.01  fof(f55,plain,(
% 19.96/3.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 19.96/3.01    inference(definition_unfolding,[],[f42,f52])).
% 19.96/3.01  
% 19.96/3.01  fof(f5,axiom,(
% 19.96/3.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 19.96/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.01  
% 19.96/3.01  fof(f40,plain,(
% 19.96/3.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.96/3.01    inference(cnf_transformation,[],[f5])).
% 19.96/3.01  
% 19.96/3.01  fof(f53,plain,(
% 19.96/3.01    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 19.96/3.01    inference(definition_unfolding,[],[f40,f52])).
% 19.96/3.01  
% 19.96/3.01  fof(f8,axiom,(
% 19.96/3.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 19.96/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.01  
% 19.96/3.01  fof(f31,plain,(
% 19.96/3.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 19.96/3.01    inference(nnf_transformation,[],[f8])).
% 19.96/3.01  
% 19.96/3.01  fof(f44,plain,(
% 19.96/3.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 19.96/3.01    inference(cnf_transformation,[],[f31])).
% 19.96/3.01  
% 19.96/3.01  fof(f12,axiom,(
% 19.96/3.01    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 19.96/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.01  
% 19.96/3.01  fof(f23,plain,(
% 19.96/3.01    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 19.96/3.01    inference(ennf_transformation,[],[f12])).
% 19.96/3.01  
% 19.96/3.01  fof(f48,plain,(
% 19.96/3.01    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.96/3.01    inference(cnf_transformation,[],[f23])).
% 19.96/3.01  
% 19.96/3.01  fof(f56,plain,(
% 19.96/3.01    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.96/3.01    inference(definition_unfolding,[],[f48,f52])).
% 19.96/3.01  
% 19.96/3.01  fof(f15,conjecture,(
% 19.96/3.01    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 19.96/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.01  
% 19.96/3.01  fof(f16,negated_conjecture,(
% 19.96/3.01    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 19.96/3.01    inference(negated_conjecture,[],[f15])).
% 19.96/3.01  
% 19.96/3.01  fof(f18,plain,(
% 19.96/3.01    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 19.96/3.01    inference(flattening,[],[f16])).
% 19.96/3.01  
% 19.96/3.01  fof(f51,plain,(
% 19.96/3.01    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 19.96/3.01    inference(cnf_transformation,[],[f18])).
% 19.96/3.01  
% 19.96/3.01  cnf(c_0,plain,
% 19.96/3.01      ( v1_xboole_0(k1_xboole_0) ),
% 19.96/3.01      inference(cnf_transformation,[],[f34]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14307,plain,
% 19.96/3.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 19.96/3.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_13,plain,
% 19.96/3.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 19.96/3.01      inference(cnf_transformation,[],[f49]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14302,plain,
% 19.96/3.01      ( v1_xboole_0(X0) != iProver_top
% 19.96/3.01      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 19.96/3.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_1,plain,
% 19.96/3.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 19.96/3.01      inference(cnf_transformation,[],[f35]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14306,plain,
% 19.96/3.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 19.96/3.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14444,plain,
% 19.96/3.01      ( k1_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_14302,c_14306]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14470,plain,
% 19.96/3.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_14307,c_14444]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_5,plain,
% 19.96/3.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 19.96/3.01      inference(cnf_transformation,[],[f39]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14304,plain,
% 19.96/3.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 19.96/3.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_11,plain,
% 19.96/3.01      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 19.96/3.01      inference(cnf_transformation,[],[f47]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14,plain,
% 19.96/3.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 19.96/3.01      | r2_hidden(sK2(X1),k1_relat_1(X1))
% 19.96/3.01      | ~ v1_relat_1(X1) ),
% 19.96/3.01      inference(cnf_transformation,[],[f50]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_194,plain,
% 19.96/3.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 19.96/3.01      | r2_hidden(sK2(X1),k1_relat_1(X1))
% 19.96/3.01      | ~ v1_xboole_0(X2)
% 19.96/3.01      | X1 != X2 ),
% 19.96/3.01      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_195,plain,
% 19.96/3.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 19.96/3.01      | r2_hidden(sK2(X1),k1_relat_1(X1))
% 19.96/3.01      | ~ v1_xboole_0(X1) ),
% 19.96/3.01      inference(unflattening,[status(thm)],[c_194]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14300,plain,
% 19.96/3.01      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 19.96/3.01      | r2_hidden(sK2(X1),k1_relat_1(X1)) = iProver_top
% 19.96/3.01      | v1_xboole_0(X1) != iProver_top ),
% 19.96/3.01      inference(predicate_to_equality,[status(thm)],[c_195]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14424,plain,
% 19.96/3.01      ( k2_relat_1(X0) = k1_xboole_0
% 19.96/3.01      | r2_hidden(sK2(X0),k1_relat_1(X0)) = iProver_top
% 19.96/3.01      | v1_xboole_0(X0) != iProver_top ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_14304,c_14300]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_2,negated_conjecture,
% 19.96/3.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 19.96/3.01      inference(cnf_transformation,[],[f38]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14305,plain,
% 19.96/3.01      ( r2_hidden(X0,X1) != iProver_top
% 19.96/3.01      | r2_hidden(X0,X2) != iProver_top
% 19.96/3.01      | r1_xboole_0(X2,X1) != iProver_top ),
% 19.96/3.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14893,plain,
% 19.96/3.01      ( k2_relat_1(X0) = k1_xboole_0
% 19.96/3.01      | r2_hidden(sK2(X0),X1) != iProver_top
% 19.96/3.01      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 19.96/3.01      | v1_xboole_0(X0) != iProver_top ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_14424,c_14305]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_15108,plain,
% 19.96/3.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 19.96/3.01      | r2_hidden(sK2(k1_xboole_0),X0) != iProver_top
% 19.96/3.01      | r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 19.96/3.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_14470,c_14893]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_50,plain,
% 19.96/3.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 19.96/3.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14892,plain,
% 19.96/3.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 19.96/3.01      | r2_hidden(sK2(k1_xboole_0),k1_xboole_0) = iProver_top
% 19.96/3.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_14470,c_14424]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_7,plain,
% 19.96/3.01      ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 19.96/3.01      inference(cnf_transformation,[],[f54]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_8,plain,
% 19.96/3.01      ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
% 19.96/3.01      inference(cnf_transformation,[],[f55]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14399,plain,
% 19.96/3.01      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_6,plain,
% 19.96/3.01      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 19.96/3.01      inference(cnf_transformation,[],[f53]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14376,plain,
% 19.96/3.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14404,plain,
% 19.96/3.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.96/3.01      inference(light_normalisation,[status(thm)],[c_14399,c_14376]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_9,plain,
% 19.96/3.01      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 19.96/3.01      inference(cnf_transformation,[],[f44]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14303,plain,
% 19.96/3.01      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 19.96/3.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14524,plain,
% 19.96/3.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_14404,c_14303]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_15107,plain,
% 19.96/3.01      ( k2_relat_1(X0) = k1_xboole_0
% 19.96/3.01      | r2_hidden(sK2(X0),k1_xboole_0) != iProver_top
% 19.96/3.01      | v1_xboole_0(X0) != iProver_top ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_14524,c_14893]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_15124,plain,
% 19.96/3.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 19.96/3.01      | r2_hidden(sK2(k1_xboole_0),k1_xboole_0) != iProver_top
% 19.96/3.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.96/3.01      inference(instantiation,[status(thm)],[c_15107]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_15133,plain,
% 19.96/3.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.96/3.01      inference(global_propositional_subsumption,
% 19.96/3.01                [status(thm)],
% 19.96/3.01                [c_15108,c_50,c_14892,c_15124]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_12,plain,
% 19.96/3.01      ( ~ v1_relat_1(X0)
% 19.96/3.01      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 19.96/3.01      inference(cnf_transformation,[],[f56]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_183,plain,
% 19.96/3.01      ( ~ v1_xboole_0(X0)
% 19.96/3.01      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 19.96/3.01      inference(resolution,[status(thm)],[c_11,c_12]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14301,plain,
% 19.96/3.01      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 19.96/3.01      | v1_xboole_0(X0) != iProver_top ),
% 19.96/3.01      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14556,plain,
% 19.96/3.01      ( k3_tarski(k1_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0) ),
% 19.96/3.01      inference(superposition,[status(thm)],[c_14307,c_14301]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_14563,plain,
% 19.96/3.01      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0) ),
% 19.96/3.01      inference(light_normalisation,[status(thm)],[c_14556,c_14470]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_15140,plain,
% 19.96/3.01      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k3_relat_1(k1_xboole_0) ),
% 19.96/3.01      inference(demodulation,[status(thm)],[c_15133,c_14563]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_15142,plain,
% 19.96/3.01      ( k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.96/3.01      inference(demodulation,[status(thm)],[c_15140,c_6]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_477,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_2201,plain,
% 19.96/3.01      ( X0 = X1 | X1 != k1_xboole_0 | X0 != k1_xboole_0 ),
% 19.96/3.01      inference(instantiation,[status(thm)],[c_477]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_2272,plain,
% 19.96/3.01      ( k3_relat_1(k1_xboole_0) != k1_xboole_0
% 19.96/3.01      | k1_xboole_0 = k3_relat_1(k1_xboole_0)
% 19.96/3.01      | k1_xboole_0 != k1_xboole_0 ),
% 19.96/3.01      inference(instantiation,[status(thm)],[c_2201]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_48,plain,
% 19.96/3.01      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 19.96/3.01      inference(instantiation,[status(thm)],[c_1]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(c_15,negated_conjecture,
% 19.96/3.01      ( k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
% 19.96/3.01      inference(cnf_transformation,[],[f51]) ).
% 19.96/3.01  
% 19.96/3.01  cnf(contradiction,plain,
% 19.96/3.01      ( $false ),
% 19.96/3.01      inference(minisat,[status(thm)],[c_15142,c_2272,c_0,c_48,c_15]) ).
% 19.96/3.01  
% 19.96/3.01  
% 19.96/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.96/3.01  
% 19.96/3.01  ------                               Statistics
% 19.96/3.01  
% 19.96/3.01  ------ Selected
% 19.96/3.01  
% 19.96/3.01  total_time:                             2.27
% 19.96/3.01  
%------------------------------------------------------------------------------
