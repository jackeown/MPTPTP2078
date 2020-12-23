%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:05 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 558 expanded)
%              Number of clauses        :   22 (  49 expanded)
%              Number of leaves         :   13 ( 169 expanded)
%              Depth                    :   15
%              Number of atoms          :  173 ( 990 expanded)
%              Number of equality atoms :  105 ( 785 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
        & ( X0 != X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) )
   => ( ( sK1 = sK2
        | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK1) )
      & ( sK1 != sK2
        | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( sK1 = sK2
      | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK1) )
    & ( sK1 != sK2
      | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f38])).

fof(f68,plain,
    ( sK1 != sK2
    | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f70])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f85,plain,
    ( sK1 != sK2
    | k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f68,f72,f72,f72])).

fof(f69,plain,
    ( sK1 = sK2
    | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,
    ( sK1 = sK2
    | k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f69,f72,f72,f72])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f90,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f72])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f88,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f80])).

fof(f89,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f88])).

cnf(c_23,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_22,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK1 = sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_928,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1004,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | sK1 = sK2 ),
    inference(resolution,[status(thm)],[c_15,c_22])).

cnf(c_20,plain,
    ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1069,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1113,negated_conjecture,
    ( sK1 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_928,c_1004,c_1069])).

cnf(c_1116,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_928,c_1004,c_1069])).

cnf(c_1118,plain,
    ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1116,c_1113])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1120,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_1118,c_0])).

cnf(c_1121,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1120,c_1118])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_750,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7933,plain,
    ( r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1121,c_750])).

cnf(c_8030,plain,
    ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7933])).

cnf(c_18,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_35,plain,
    ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8030,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:16:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.05/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/1.00  
% 4.05/1.00  ------  iProver source info
% 4.05/1.00  
% 4.05/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.05/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/1.00  git: non_committed_changes: false
% 4.05/1.00  git: last_make_outside_of_git: false
% 4.05/1.00  
% 4.05/1.00  ------ 
% 4.05/1.00  
% 4.05/1.00  ------ Input Options
% 4.05/1.00  
% 4.05/1.00  --out_options                           all
% 4.05/1.00  --tptp_safe_out                         true
% 4.05/1.00  --problem_path                          ""
% 4.05/1.00  --include_path                          ""
% 4.05/1.00  --clausifier                            res/vclausify_rel
% 4.05/1.00  --clausifier_options                    --mode clausify
% 4.05/1.00  --stdin                                 false
% 4.05/1.00  --stats_out                             sel
% 4.05/1.00  
% 4.05/1.00  ------ General Options
% 4.05/1.00  
% 4.05/1.00  --fof                                   false
% 4.05/1.00  --time_out_real                         604.99
% 4.05/1.00  --time_out_virtual                      -1.
% 4.05/1.00  --symbol_type_check                     false
% 4.05/1.00  --clausify_out                          false
% 4.05/1.00  --sig_cnt_out                           false
% 4.05/1.00  --trig_cnt_out                          false
% 4.05/1.00  --trig_cnt_out_tolerance                1.
% 4.05/1.00  --trig_cnt_out_sk_spl                   false
% 4.05/1.00  --abstr_cl_out                          false
% 4.05/1.00  
% 4.05/1.00  ------ Global Options
% 4.05/1.00  
% 4.05/1.00  --schedule                              none
% 4.05/1.00  --add_important_lit                     false
% 4.05/1.00  --prop_solver_per_cl                    1000
% 4.05/1.00  --min_unsat_core                        false
% 4.05/1.00  --soft_assumptions                      false
% 4.05/1.00  --soft_lemma_size                       3
% 4.05/1.00  --prop_impl_unit_size                   0
% 4.05/1.00  --prop_impl_unit                        []
% 4.05/1.00  --share_sel_clauses                     true
% 4.05/1.00  --reset_solvers                         false
% 4.05/1.00  --bc_imp_inh                            [conj_cone]
% 4.05/1.00  --conj_cone_tolerance                   3.
% 4.05/1.00  --extra_neg_conj                        none
% 4.05/1.00  --large_theory_mode                     true
% 4.05/1.00  --prolific_symb_bound                   200
% 4.05/1.00  --lt_threshold                          2000
% 4.05/1.00  --clause_weak_htbl                      true
% 4.05/1.00  --gc_record_bc_elim                     false
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing Options
% 4.05/1.00  
% 4.05/1.00  --preprocessing_flag                    true
% 4.05/1.00  --time_out_prep_mult                    0.1
% 4.05/1.00  --splitting_mode                        input
% 4.05/1.00  --splitting_grd                         true
% 4.05/1.00  --splitting_cvd                         false
% 4.05/1.00  --splitting_cvd_svl                     false
% 4.05/1.00  --splitting_nvd                         32
% 4.05/1.00  --sub_typing                            true
% 4.05/1.00  --prep_gs_sim                           false
% 4.05/1.00  --prep_unflatten                        true
% 4.05/1.00  --prep_res_sim                          true
% 4.05/1.00  --prep_upred                            true
% 4.05/1.00  --prep_sem_filter                       exhaustive
% 4.05/1.00  --prep_sem_filter_out                   false
% 4.05/1.00  --pred_elim                             false
% 4.05/1.00  --res_sim_input                         true
% 4.05/1.00  --eq_ax_congr_red                       true
% 4.05/1.00  --pure_diseq_elim                       true
% 4.05/1.00  --brand_transform                       false
% 4.05/1.00  --non_eq_to_eq                          false
% 4.05/1.00  --prep_def_merge                        true
% 4.05/1.00  --prep_def_merge_prop_impl              false
% 4.05/1.00  --prep_def_merge_mbd                    true
% 4.05/1.00  --prep_def_merge_tr_red                 false
% 4.05/1.00  --prep_def_merge_tr_cl                  false
% 4.05/1.00  --smt_preprocessing                     true
% 4.05/1.00  --smt_ac_axioms                         fast
% 4.05/1.00  --preprocessed_out                      false
% 4.05/1.00  --preprocessed_stats                    false
% 4.05/1.00  
% 4.05/1.00  ------ Abstraction refinement Options
% 4.05/1.00  
% 4.05/1.00  --abstr_ref                             []
% 4.05/1.00  --abstr_ref_prep                        false
% 4.05/1.00  --abstr_ref_until_sat                   false
% 4.05/1.00  --abstr_ref_sig_restrict                funpre
% 4.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/1.00  --abstr_ref_under                       []
% 4.05/1.00  
% 4.05/1.00  ------ SAT Options
% 4.05/1.00  
% 4.05/1.00  --sat_mode                              false
% 4.05/1.00  --sat_fm_restart_options                ""
% 4.05/1.00  --sat_gr_def                            false
% 4.05/1.00  --sat_epr_types                         true
% 4.05/1.00  --sat_non_cyclic_types                  false
% 4.05/1.00  --sat_finite_models                     false
% 4.05/1.00  --sat_fm_lemmas                         false
% 4.05/1.00  --sat_fm_prep                           false
% 4.05/1.00  --sat_fm_uc_incr                        true
% 4.05/1.00  --sat_out_model                         small
% 4.05/1.00  --sat_out_clauses                       false
% 4.05/1.00  
% 4.05/1.00  ------ QBF Options
% 4.05/1.00  
% 4.05/1.00  --qbf_mode                              false
% 4.05/1.00  --qbf_elim_univ                         false
% 4.05/1.00  --qbf_dom_inst                          none
% 4.05/1.00  --qbf_dom_pre_inst                      false
% 4.05/1.00  --qbf_sk_in                             false
% 4.05/1.00  --qbf_pred_elim                         true
% 4.05/1.00  --qbf_split                             512
% 4.05/1.00  
% 4.05/1.00  ------ BMC1 Options
% 4.05/1.00  
% 4.05/1.00  --bmc1_incremental                      false
% 4.05/1.00  --bmc1_axioms                           reachable_all
% 4.05/1.00  --bmc1_min_bound                        0
% 4.05/1.00  --bmc1_max_bound                        -1
% 4.05/1.00  --bmc1_max_bound_default                -1
% 4.05/1.00  --bmc1_symbol_reachability              true
% 4.05/1.00  --bmc1_property_lemmas                  false
% 4.05/1.00  --bmc1_k_induction                      false
% 4.05/1.00  --bmc1_non_equiv_states                 false
% 4.05/1.00  --bmc1_deadlock                         false
% 4.05/1.00  --bmc1_ucm                              false
% 4.05/1.00  --bmc1_add_unsat_core                   none
% 4.05/1.00  --bmc1_unsat_core_children              false
% 4.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/1.00  --bmc1_out_stat                         full
% 4.05/1.00  --bmc1_ground_init                      false
% 4.05/1.00  --bmc1_pre_inst_next_state              false
% 4.05/1.00  --bmc1_pre_inst_state                   false
% 4.05/1.00  --bmc1_pre_inst_reach_state             false
% 4.05/1.00  --bmc1_out_unsat_core                   false
% 4.05/1.00  --bmc1_aig_witness_out                  false
% 4.05/1.00  --bmc1_verbose                          false
% 4.05/1.00  --bmc1_dump_clauses_tptp                false
% 4.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.05/1.00  --bmc1_dump_file                        -
% 4.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.05/1.00  --bmc1_ucm_extend_mode                  1
% 4.05/1.00  --bmc1_ucm_init_mode                    2
% 4.05/1.00  --bmc1_ucm_cone_mode                    none
% 4.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.05/1.00  --bmc1_ucm_relax_model                  4
% 4.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/1.00  --bmc1_ucm_layered_model                none
% 4.05/1.00  --bmc1_ucm_max_lemma_size               10
% 4.05/1.00  
% 4.05/1.00  ------ AIG Options
% 4.05/1.00  
% 4.05/1.00  --aig_mode                              false
% 4.05/1.00  
% 4.05/1.00  ------ Instantiation Options
% 4.05/1.00  
% 4.05/1.00  --instantiation_flag                    true
% 4.05/1.00  --inst_sos_flag                         false
% 4.05/1.00  --inst_sos_phase                        true
% 4.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel_side                     num_symb
% 4.05/1.00  --inst_solver_per_active                1400
% 4.05/1.00  --inst_solver_calls_frac                1.
% 4.05/1.00  --inst_passive_queue_type               priority_queues
% 4.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/1.00  --inst_passive_queues_freq              [25;2]
% 4.05/1.00  --inst_dismatching                      true
% 4.05/1.00  --inst_eager_unprocessed_to_passive     true
% 4.05/1.00  --inst_prop_sim_given                   true
% 4.05/1.00  --inst_prop_sim_new                     false
% 4.05/1.00  --inst_subs_new                         false
% 4.05/1.00  --inst_eq_res_simp                      false
% 4.05/1.00  --inst_subs_given                       false
% 4.05/1.00  --inst_orphan_elimination               true
% 4.05/1.00  --inst_learning_loop_flag               true
% 4.05/1.00  --inst_learning_start                   3000
% 4.05/1.00  --inst_learning_factor                  2
% 4.05/1.00  --inst_start_prop_sim_after_learn       3
% 4.05/1.00  --inst_sel_renew                        solver
% 4.05/1.00  --inst_lit_activity_flag                true
% 4.05/1.00  --inst_restr_to_given                   false
% 4.05/1.00  --inst_activity_threshold               500
% 4.05/1.00  --inst_out_proof                        true
% 4.05/1.00  
% 4.05/1.00  ------ Resolution Options
% 4.05/1.00  
% 4.05/1.00  --resolution_flag                       true
% 4.05/1.00  --res_lit_sel                           adaptive
% 4.05/1.00  --res_lit_sel_side                      none
% 4.05/1.00  --res_ordering                          kbo
% 4.05/1.00  --res_to_prop_solver                    active
% 4.05/1.00  --res_prop_simpl_new                    false
% 4.05/1.00  --res_prop_simpl_given                  true
% 4.05/1.00  --res_passive_queue_type                priority_queues
% 4.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/1.00  --res_passive_queues_freq               [15;5]
% 4.05/1.00  --res_forward_subs                      full
% 4.05/1.00  --res_backward_subs                     full
% 4.05/1.00  --res_forward_subs_resolution           true
% 4.05/1.00  --res_backward_subs_resolution          true
% 4.05/1.00  --res_orphan_elimination                true
% 4.05/1.00  --res_time_limit                        2.
% 4.05/1.00  --res_out_proof                         true
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Options
% 4.05/1.00  
% 4.05/1.00  --superposition_flag                    true
% 4.05/1.00  --sup_passive_queue_type                priority_queues
% 4.05/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/1.00  --sup_passive_queues_freq               [1;4]
% 4.05/1.00  --demod_completeness_check              fast
% 4.05/1.00  --demod_use_ground                      true
% 4.05/1.00  --sup_to_prop_solver                    passive
% 4.05/1.00  --sup_prop_simpl_new                    true
% 4.05/1.00  --sup_prop_simpl_given                  true
% 4.05/1.00  --sup_fun_splitting                     false
% 4.05/1.00  --sup_smt_interval                      50000
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Simplification Setup
% 4.05/1.00  
% 4.05/1.00  --sup_indices_passive                   []
% 4.05/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/1.00  --sup_full_bw                           [BwDemod]
% 4.05/1.00  --sup_immed_triv                        [TrivRules]
% 4.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/1.00  --sup_immed_bw_main                     []
% 4.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.05/1.00  
% 4.05/1.00  ------ Combination Options
% 4.05/1.00  
% 4.05/1.00  --comb_res_mult                         3
% 4.05/1.00  --comb_sup_mult                         2
% 4.05/1.00  --comb_inst_mult                        10
% 4.05/1.00  
% 4.05/1.00  ------ Debug Options
% 4.05/1.00  
% 4.05/1.00  --dbg_backtrace                         false
% 4.05/1.00  --dbg_dump_prop_clauses                 false
% 4.05/1.00  --dbg_dump_prop_clauses_file            -
% 4.05/1.00  --dbg_out_stat                          false
% 4.05/1.00  ------ Parsing...
% 4.05/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  ------ Proving...
% 4.05/1.00  ------ Problem Properties 
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  clauses                                 23
% 4.05/1.00  conjectures                             2
% 4.05/1.00  EPR                                     3
% 4.05/1.00  Horn                                    18
% 4.05/1.00  unary                                   9
% 4.05/1.00  binary                                  7
% 4.05/1.00  lits                                    44
% 4.05/1.00  lits eq                                 17
% 4.05/1.00  fd_pure                                 0
% 4.05/1.00  fd_pseudo                               0
% 4.05/1.00  fd_cond                                 0
% 4.05/1.00  fd_pseudo_cond                          3
% 4.05/1.00  AC symbols                              0
% 4.05/1.00  
% 4.05/1.00  ------ Input Options Time Limit: Unbounded
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ 
% 4.05/1.00  Current options:
% 4.05/1.00  ------ 
% 4.05/1.00  
% 4.05/1.00  ------ Input Options
% 4.05/1.00  
% 4.05/1.00  --out_options                           all
% 4.05/1.00  --tptp_safe_out                         true
% 4.05/1.00  --problem_path                          ""
% 4.05/1.00  --include_path                          ""
% 4.05/1.00  --clausifier                            res/vclausify_rel
% 4.05/1.00  --clausifier_options                    --mode clausify
% 4.05/1.00  --stdin                                 false
% 4.05/1.00  --stats_out                             sel
% 4.05/1.00  
% 4.05/1.00  ------ General Options
% 4.05/1.00  
% 4.05/1.00  --fof                                   false
% 4.05/1.00  --time_out_real                         604.99
% 4.05/1.00  --time_out_virtual                      -1.
% 4.05/1.00  --symbol_type_check                     false
% 4.05/1.00  --clausify_out                          false
% 4.05/1.00  --sig_cnt_out                           false
% 4.05/1.00  --trig_cnt_out                          false
% 4.05/1.00  --trig_cnt_out_tolerance                1.
% 4.05/1.00  --trig_cnt_out_sk_spl                   false
% 4.05/1.00  --abstr_cl_out                          false
% 4.05/1.00  
% 4.05/1.00  ------ Global Options
% 4.05/1.00  
% 4.05/1.00  --schedule                              none
% 4.05/1.00  --add_important_lit                     false
% 4.05/1.00  --prop_solver_per_cl                    1000
% 4.05/1.00  --min_unsat_core                        false
% 4.05/1.00  --soft_assumptions                      false
% 4.05/1.00  --soft_lemma_size                       3
% 4.05/1.00  --prop_impl_unit_size                   0
% 4.05/1.00  --prop_impl_unit                        []
% 4.05/1.00  --share_sel_clauses                     true
% 4.05/1.00  --reset_solvers                         false
% 4.05/1.00  --bc_imp_inh                            [conj_cone]
% 4.05/1.00  --conj_cone_tolerance                   3.
% 4.05/1.00  --extra_neg_conj                        none
% 4.05/1.00  --large_theory_mode                     true
% 4.05/1.00  --prolific_symb_bound                   200
% 4.05/1.00  --lt_threshold                          2000
% 4.05/1.00  --clause_weak_htbl                      true
% 4.05/1.00  --gc_record_bc_elim                     false
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing Options
% 4.05/1.00  
% 4.05/1.00  --preprocessing_flag                    true
% 4.05/1.00  --time_out_prep_mult                    0.1
% 4.05/1.00  --splitting_mode                        input
% 4.05/1.00  --splitting_grd                         true
% 4.05/1.00  --splitting_cvd                         false
% 4.05/1.00  --splitting_cvd_svl                     false
% 4.05/1.00  --splitting_nvd                         32
% 4.05/1.00  --sub_typing                            true
% 4.05/1.00  --prep_gs_sim                           false
% 4.05/1.00  --prep_unflatten                        true
% 4.05/1.00  --prep_res_sim                          true
% 4.05/1.00  --prep_upred                            true
% 4.05/1.00  --prep_sem_filter                       exhaustive
% 4.05/1.00  --prep_sem_filter_out                   false
% 4.05/1.00  --pred_elim                             false
% 4.05/1.00  --res_sim_input                         true
% 4.05/1.00  --eq_ax_congr_red                       true
% 4.05/1.00  --pure_diseq_elim                       true
% 4.05/1.00  --brand_transform                       false
% 4.05/1.00  --non_eq_to_eq                          false
% 4.05/1.00  --prep_def_merge                        true
% 4.05/1.00  --prep_def_merge_prop_impl              false
% 4.05/1.00  --prep_def_merge_mbd                    true
% 4.05/1.00  --prep_def_merge_tr_red                 false
% 4.05/1.00  --prep_def_merge_tr_cl                  false
% 4.05/1.00  --smt_preprocessing                     true
% 4.05/1.00  --smt_ac_axioms                         fast
% 4.05/1.00  --preprocessed_out                      false
% 4.05/1.00  --preprocessed_stats                    false
% 4.05/1.00  
% 4.05/1.00  ------ Abstraction refinement Options
% 4.05/1.00  
% 4.05/1.00  --abstr_ref                             []
% 4.05/1.00  --abstr_ref_prep                        false
% 4.05/1.00  --abstr_ref_until_sat                   false
% 4.05/1.00  --abstr_ref_sig_restrict                funpre
% 4.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/1.00  --abstr_ref_under                       []
% 4.05/1.00  
% 4.05/1.00  ------ SAT Options
% 4.05/1.00  
% 4.05/1.00  --sat_mode                              false
% 4.05/1.00  --sat_fm_restart_options                ""
% 4.05/1.00  --sat_gr_def                            false
% 4.05/1.00  --sat_epr_types                         true
% 4.05/1.00  --sat_non_cyclic_types                  false
% 4.05/1.00  --sat_finite_models                     false
% 4.05/1.00  --sat_fm_lemmas                         false
% 4.05/1.00  --sat_fm_prep                           false
% 4.05/1.00  --sat_fm_uc_incr                        true
% 4.05/1.00  --sat_out_model                         small
% 4.05/1.00  --sat_out_clauses                       false
% 4.05/1.00  
% 4.05/1.00  ------ QBF Options
% 4.05/1.00  
% 4.05/1.00  --qbf_mode                              false
% 4.05/1.00  --qbf_elim_univ                         false
% 4.05/1.00  --qbf_dom_inst                          none
% 4.05/1.00  --qbf_dom_pre_inst                      false
% 4.05/1.00  --qbf_sk_in                             false
% 4.05/1.00  --qbf_pred_elim                         true
% 4.05/1.00  --qbf_split                             512
% 4.05/1.00  
% 4.05/1.00  ------ BMC1 Options
% 4.05/1.00  
% 4.05/1.00  --bmc1_incremental                      false
% 4.05/1.00  --bmc1_axioms                           reachable_all
% 4.05/1.00  --bmc1_min_bound                        0
% 4.05/1.00  --bmc1_max_bound                        -1
% 4.05/1.00  --bmc1_max_bound_default                -1
% 4.05/1.00  --bmc1_symbol_reachability              true
% 4.05/1.00  --bmc1_property_lemmas                  false
% 4.05/1.00  --bmc1_k_induction                      false
% 4.05/1.00  --bmc1_non_equiv_states                 false
% 4.05/1.00  --bmc1_deadlock                         false
% 4.05/1.00  --bmc1_ucm                              false
% 4.05/1.00  --bmc1_add_unsat_core                   none
% 4.05/1.00  --bmc1_unsat_core_children              false
% 4.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/1.00  --bmc1_out_stat                         full
% 4.05/1.00  --bmc1_ground_init                      false
% 4.05/1.00  --bmc1_pre_inst_next_state              false
% 4.05/1.00  --bmc1_pre_inst_state                   false
% 4.05/1.00  --bmc1_pre_inst_reach_state             false
% 4.05/1.00  --bmc1_out_unsat_core                   false
% 4.05/1.00  --bmc1_aig_witness_out                  false
% 4.05/1.00  --bmc1_verbose                          false
% 4.05/1.00  --bmc1_dump_clauses_tptp                false
% 4.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.05/1.00  --bmc1_dump_file                        -
% 4.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.05/1.00  --bmc1_ucm_extend_mode                  1
% 4.05/1.00  --bmc1_ucm_init_mode                    2
% 4.05/1.00  --bmc1_ucm_cone_mode                    none
% 4.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.05/1.00  --bmc1_ucm_relax_model                  4
% 4.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/1.00  --bmc1_ucm_layered_model                none
% 4.05/1.00  --bmc1_ucm_max_lemma_size               10
% 4.05/1.00  
% 4.05/1.00  ------ AIG Options
% 4.05/1.00  
% 4.05/1.00  --aig_mode                              false
% 4.05/1.00  
% 4.05/1.00  ------ Instantiation Options
% 4.05/1.00  
% 4.05/1.00  --instantiation_flag                    true
% 4.05/1.00  --inst_sos_flag                         false
% 4.05/1.00  --inst_sos_phase                        true
% 4.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel_side                     num_symb
% 4.05/1.00  --inst_solver_per_active                1400
% 4.05/1.00  --inst_solver_calls_frac                1.
% 4.05/1.00  --inst_passive_queue_type               priority_queues
% 4.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/1.00  --inst_passive_queues_freq              [25;2]
% 4.05/1.00  --inst_dismatching                      true
% 4.05/1.00  --inst_eager_unprocessed_to_passive     true
% 4.05/1.00  --inst_prop_sim_given                   true
% 4.05/1.00  --inst_prop_sim_new                     false
% 4.05/1.00  --inst_subs_new                         false
% 4.05/1.00  --inst_eq_res_simp                      false
% 4.05/1.00  --inst_subs_given                       false
% 4.05/1.00  --inst_orphan_elimination               true
% 4.05/1.00  --inst_learning_loop_flag               true
% 4.05/1.00  --inst_learning_start                   3000
% 4.05/1.00  --inst_learning_factor                  2
% 4.05/1.00  --inst_start_prop_sim_after_learn       3
% 4.05/1.00  --inst_sel_renew                        solver
% 4.05/1.00  --inst_lit_activity_flag                true
% 4.05/1.00  --inst_restr_to_given                   false
% 4.05/1.00  --inst_activity_threshold               500
% 4.05/1.00  --inst_out_proof                        true
% 4.05/1.00  
% 4.05/1.00  ------ Resolution Options
% 4.05/1.00  
% 4.05/1.00  --resolution_flag                       true
% 4.05/1.00  --res_lit_sel                           adaptive
% 4.05/1.00  --res_lit_sel_side                      none
% 4.05/1.00  --res_ordering                          kbo
% 4.05/1.00  --res_to_prop_solver                    active
% 4.05/1.00  --res_prop_simpl_new                    false
% 4.05/1.00  --res_prop_simpl_given                  true
% 4.05/1.00  --res_passive_queue_type                priority_queues
% 4.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/1.00  --res_passive_queues_freq               [15;5]
% 4.05/1.00  --res_forward_subs                      full
% 4.05/1.00  --res_backward_subs                     full
% 4.05/1.00  --res_forward_subs_resolution           true
% 4.05/1.00  --res_backward_subs_resolution          true
% 4.05/1.00  --res_orphan_elimination                true
% 4.05/1.00  --res_time_limit                        2.
% 4.05/1.00  --res_out_proof                         true
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Options
% 4.05/1.00  
% 4.05/1.00  --superposition_flag                    true
% 4.05/1.00  --sup_passive_queue_type                priority_queues
% 4.05/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/1.00  --sup_passive_queues_freq               [1;4]
% 4.05/1.00  --demod_completeness_check              fast
% 4.05/1.00  --demod_use_ground                      true
% 4.05/1.00  --sup_to_prop_solver                    passive
% 4.05/1.00  --sup_prop_simpl_new                    true
% 4.05/1.00  --sup_prop_simpl_given                  true
% 4.05/1.00  --sup_fun_splitting                     false
% 4.05/1.00  --sup_smt_interval                      50000
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Simplification Setup
% 4.05/1.00  
% 4.05/1.00  --sup_indices_passive                   []
% 4.05/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/1.00  --sup_full_bw                           [BwDemod]
% 4.05/1.00  --sup_immed_triv                        [TrivRules]
% 4.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/1.00  --sup_immed_bw_main                     []
% 4.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.05/1.00  
% 4.05/1.00  ------ Combination Options
% 4.05/1.00  
% 4.05/1.00  --comb_res_mult                         3
% 4.05/1.00  --comb_sup_mult                         2
% 4.05/1.00  --comb_inst_mult                        10
% 4.05/1.00  
% 4.05/1.00  ------ Debug Options
% 4.05/1.00  
% 4.05/1.00  --dbg_backtrace                         false
% 4.05/1.00  --dbg_dump_prop_clauses                 false
% 4.05/1.00  --dbg_dump_prop_clauses_file            -
% 4.05/1.00  --dbg_out_stat                          false
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  % SZS status Theorem for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  fof(f21,conjecture,(
% 4.05/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f22,negated_conjecture,(
% 4.05/1.00    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 4.05/1.00    inference(negated_conjecture,[],[f21])).
% 4.05/1.00  
% 4.05/1.00  fof(f29,plain,(
% 4.05/1.00    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <~> X0 != X1)),
% 4.05/1.00    inference(ennf_transformation,[],[f22])).
% 4.05/1.00  
% 4.05/1.00  fof(f37,plain,(
% 4.05/1.00    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)))),
% 4.05/1.00    inference(nnf_transformation,[],[f29])).
% 4.05/1.00  
% 4.05/1.00  fof(f38,plain,(
% 4.05/1.00    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))) => ((sK1 = sK2 | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK1)) & (sK1 != sK2 | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f39,plain,(
% 4.05/1.00    (sK1 = sK2 | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK1)) & (sK1 != sK2 | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f38])).
% 4.05/1.00  
% 4.05/1.00  fof(f68,plain,(
% 4.05/1.00    sK1 != sK2 | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 4.05/1.00    inference(cnf_transformation,[],[f39])).
% 4.05/1.00  
% 4.05/1.00  fof(f15,axiom,(
% 4.05/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f62,plain,(
% 4.05/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f15])).
% 4.05/1.00  
% 4.05/1.00  fof(f16,axiom,(
% 4.05/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f63,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f16])).
% 4.05/1.00  
% 4.05/1.00  fof(f17,axiom,(
% 4.05/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f64,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f17])).
% 4.05/1.00  
% 4.05/1.00  fof(f18,axiom,(
% 4.05/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f65,plain,(
% 4.05/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f18])).
% 4.05/1.00  
% 4.05/1.00  fof(f70,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f64,f65])).
% 4.05/1.00  
% 4.05/1.00  fof(f71,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f63,f70])).
% 4.05/1.00  
% 4.05/1.00  fof(f72,plain,(
% 4.05/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f62,f71])).
% 4.05/1.00  
% 4.05/1.00  fof(f85,plain,(
% 4.05/1.00    sK1 != sK2 | k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 4.05/1.00    inference(definition_unfolding,[],[f68,f72,f72,f72])).
% 4.05/1.00  
% 4.05/1.00  fof(f69,plain,(
% 4.05/1.00    sK1 = sK2 | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK1)),
% 4.05/1.00    inference(cnf_transformation,[],[f39])).
% 4.05/1.00  
% 4.05/1.00  fof(f84,plain,(
% 4.05/1.00    sK1 = sK2 | k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 4.05/1.00    inference(definition_unfolding,[],[f69,f72,f72,f72])).
% 4.05/1.00  
% 4.05/1.00  fof(f14,axiom,(
% 4.05/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f33,plain,(
% 4.05/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.05/1.00    inference(nnf_transformation,[],[f14])).
% 4.05/1.00  
% 4.05/1.00  fof(f34,plain,(
% 4.05/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.05/1.00    inference(rectify,[],[f33])).
% 4.05/1.00  
% 4.05/1.00  fof(f35,plain,(
% 4.05/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f36,plain,(
% 4.05/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 4.05/1.00  
% 4.05/1.00  fof(f58,plain,(
% 4.05/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.05/1.00    inference(cnf_transformation,[],[f36])).
% 4.05/1.00  
% 4.05/1.00  fof(f81,plain,(
% 4.05/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 4.05/1.00    inference(definition_unfolding,[],[f58,f72])).
% 4.05/1.00  
% 4.05/1.00  fof(f90,plain,(
% 4.05/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 4.05/1.00    inference(equality_resolution,[],[f81])).
% 4.05/1.00  
% 4.05/1.00  fof(f12,axiom,(
% 4.05/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f23,plain,(
% 4.05/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 4.05/1.00    inference(unused_predicate_definition_removal,[],[f12])).
% 4.05/1.00  
% 4.05/1.00  fof(f26,plain,(
% 4.05/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 4.05/1.00    inference(ennf_transformation,[],[f23])).
% 4.05/1.00  
% 4.05/1.00  fof(f56,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f26])).
% 4.05/1.00  
% 4.05/1.00  fof(f19,axiom,(
% 4.05/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f27,plain,(
% 4.05/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 4.05/1.00    inference(ennf_transformation,[],[f19])).
% 4.05/1.00  
% 4.05/1.00  fof(f66,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f27])).
% 4.05/1.00  
% 4.05/1.00  fof(f82,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f66,f72])).
% 4.05/1.00  
% 4.05/1.00  fof(f4,axiom,(
% 4.05/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f48,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f4])).
% 4.05/1.00  
% 4.05/1.00  fof(f9,axiom,(
% 4.05/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f53,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f9])).
% 4.05/1.00  
% 4.05/1.00  fof(f73,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f48,f53])).
% 4.05/1.00  
% 4.05/1.00  fof(f2,axiom,(
% 4.05/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f24,plain,(
% 4.05/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 4.05/1.00    inference(ennf_transformation,[],[f2])).
% 4.05/1.00  
% 4.05/1.00  fof(f30,plain,(
% 4.05/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 4.05/1.00    inference(nnf_transformation,[],[f24])).
% 4.05/1.00  
% 4.05/1.00  fof(f42,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f30])).
% 4.05/1.00  
% 4.05/1.00  fof(f59,plain,(
% 4.05/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 4.05/1.00    inference(cnf_transformation,[],[f36])).
% 4.05/1.00  
% 4.05/1.00  fof(f80,plain,(
% 4.05/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 4.05/1.00    inference(definition_unfolding,[],[f59,f72])).
% 4.05/1.00  
% 4.05/1.00  fof(f88,plain,(
% 4.05/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 4.05/1.00    inference(equality_resolution,[],[f80])).
% 4.05/1.00  
% 4.05/1.00  fof(f89,plain,(
% 4.05/1.00    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 4.05/1.00    inference(equality_resolution,[],[f88])).
% 4.05/1.00  
% 4.05/1.00  cnf(c_23,negated_conjecture,
% 4.05/1.00      ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
% 4.05/1.00      | sK1 != sK2 ),
% 4.05/1.00      inference(cnf_transformation,[],[f85]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_22,negated_conjecture,
% 4.05/1.00      ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
% 4.05/1.00      | sK1 = sK2 ),
% 4.05/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_19,plain,
% 4.05/1.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 4.05/1.00      inference(cnf_transformation,[],[f90]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_928,plain,
% 4.05/1.00      ( ~ r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | sK1 = sK2 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_15,plain,
% 4.05/1.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1004,plain,
% 4.05/1.00      ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 4.05/1.00      | sK1 = sK2 ),
% 4.05/1.00      inference(resolution,[status(thm)],[c_15,c_22]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_20,plain,
% 4.05/1.00      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 4.05/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1069,plain,
% 4.05/1.00      ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 4.05/1.00      | r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1113,negated_conjecture,
% 4.05/1.00      ( sK1 = sK2 ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_22,c_928,c_1004,c_1069]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1116,negated_conjecture,
% 4.05/1.00      ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_23,c_928,c_1004,c_1069]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1118,plain,
% 4.05/1.00      ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 4.05/1.00      inference(light_normalisation,[status(thm)],[c_1116,c_1113]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_0,plain,
% 4.05/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 4.05/1.00      inference(cnf_transformation,[],[f73]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1120,plain,
% 4.05/1.00      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_1118,c_0]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1121,plain,
% 4.05/1.00      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 4.05/1.00      inference(light_normalisation,[status(thm)],[c_1120,c_1118]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_4,plain,
% 4.05/1.00      ( ~ r2_hidden(X0,X1)
% 4.05/1.00      | ~ r2_hidden(X0,X2)
% 4.05/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f42]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_750,plain,
% 4.05/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.05/1.00      | r2_hidden(X0,X2) != iProver_top
% 4.05/1.00      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_7933,plain,
% 4.05/1.00      ( r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_1121,c_750]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8030,plain,
% 4.05/1.00      ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_7933]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_18,plain,
% 4.05/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f89]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_33,plain,
% 4.05/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_35,plain,
% 4.05/1.00      ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_33]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(contradiction,plain,
% 4.05/1.00      ( $false ),
% 4.05/1.00      inference(minisat,[status(thm)],[c_8030,c_35]) ).
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  ------                               Statistics
% 4.05/1.00  
% 4.05/1.00  ------ Selected
% 4.05/1.00  
% 4.05/1.00  total_time:                             0.273
% 4.05/1.00  
%------------------------------------------------------------------------------
