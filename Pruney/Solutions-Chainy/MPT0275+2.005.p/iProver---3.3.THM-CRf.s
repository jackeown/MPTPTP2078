%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:24 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 441 expanded)
%              Number of clauses        :   44 ( 134 expanded)
%              Number of leaves         :   10 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          :  218 (1351 expanded)
%              Number of equality atoms :  105 ( 572 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK2,sK3)
        | ~ r2_hidden(sK1,sK3)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK3) )
      & ( ( r2_hidden(sK2,sK3)
          & r2_hidden(sK1,sK3) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r2_hidden(sK2,sK3)
      | ~ r2_hidden(sK1,sK3)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK3) )
    & ( ( r2_hidden(sK2,sK3)
        & r2_hidden(sK1,sK3) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f42])).

fof(f76,plain,
    ( r2_hidden(sK2,sK3)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,
    ( r2_hidden(sK2,sK3)
    | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(definition_unfolding,[],[f76,f59])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f77,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK1,sK3)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK1,sK3)
    | k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(definition_unfolding,[],[f77,f59])).

fof(f15,axiom,(
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
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) ) ),
    inference(definition_unfolding,[],[f64,f59])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(definition_unfolding,[],[f75,f59])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f71,f59])).

fof(f96,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X1)),X2) = k1_tarski(X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f83])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f68,f59])).

cnf(c_312,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_311,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2254,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_312,c_311])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK2,sK3)
    | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_11793,plain,
    ( r2_hidden(sK2,sK3)
    | k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2254,c_30])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK2,sK3)
    | k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_868,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | r2_hidden(sK1,sK3) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1427,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) != k1_xboole_0
    | r2_hidden(sK1,sK3) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_868])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X2),k1_tarski(X0)),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_11015,plain,
    ( r2_hidden(sK1,sK3)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_11016,plain,
    ( r2_hidden(sK1,sK3) = iProver_top
    | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11015])).

cnf(c_11796,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11793])).

cnf(c_867,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1425,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_867])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_883,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11725,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0
    | k2_xboole_0(k1_tarski(sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1425,c_883])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_866,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1426,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_866])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_xboole_0(k1_tarski(X2),k1_tarski(X0)),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2969,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,sK3)
    | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(X0)),sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_9815,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK2,sK3)
    | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) ),
    inference(instantiation,[status(thm)],[c_2969])).

cnf(c_9816,plain,
    ( r2_hidden(sK1,sK3) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9815])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1261,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
    | k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11019,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3)
    | k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_11020,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0
    | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11019])).

cnf(c_12128,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11725,c_1425,c_1426,c_9816,c_11020])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_889,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12136,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_12128,c_889])).

cnf(c_12252,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11793,c_1425,c_1426,c_1427,c_9816,c_11016,c_11020,c_11796,c_12136])).

cnf(c_12258,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(resolution,[status(thm)],[c_12252,c_5])).

cnf(c_12396,plain,
    ( r2_hidden(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_12258,c_18])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X0)),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_11026,plain,
    ( r2_hidden(sK1,sK3)
    | k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)),sK3) = k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X2)),X1) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_9776,plain,
    ( ~ r2_hidden(sK1,sK3)
    | k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(X0)),sK3) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_11025,plain,
    ( ~ r2_hidden(sK1,sK3)
    | k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)),sK3) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_9776])).

cnf(c_11027,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)),sK3) != k1_tarski(sK1)
    | r2_hidden(sK1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11025])).

cnf(c_33,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12396,c_12136,c_12128,c_11026,c_11027,c_11016,c_1427,c_29,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 0.82/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.82/1.03  
% 0.82/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.82/1.03  
% 0.82/1.03  ------  iProver source info
% 0.82/1.03  
% 0.82/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.82/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.82/1.03  git: non_committed_changes: false
% 0.82/1.03  git: last_make_outside_of_git: false
% 0.82/1.03  
% 0.82/1.03  ------ 
% 0.82/1.03  ------ Parsing...
% 0.82/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.82/1.03  
% 0.82/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 0.82/1.03  
% 0.82/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.82/1.03  
% 0.82/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.82/1.03  ------ Proving...
% 0.82/1.03  ------ Problem Properties 
% 0.82/1.03  
% 0.82/1.03  
% 0.82/1.03  clauses                                 32
% 0.82/1.03  conjectures                             3
% 0.82/1.03  EPR                                     0
% 0.82/1.03  Horn                                    24
% 0.82/1.03  unary                                   8
% 0.82/1.03  binary                                  17
% 0.82/1.03  lits                                    63
% 0.82/1.03  lits eq                                 27
% 0.82/1.03  fd_pure                                 0
% 0.82/1.03  fd_pseudo                               0
% 0.82/1.03  fd_cond                                 0
% 0.82/1.03  fd_pseudo_cond                          3
% 0.82/1.03  AC symbols                              0
% 0.82/1.03  
% 0.82/1.03  ------ Input Options Time Limit: Unbounded
% 0.82/1.03  
% 0.82/1.03  
% 0.82/1.03  ------ 
% 0.82/1.03  Current options:
% 0.82/1.03  ------ 
% 0.82/1.03  
% 0.82/1.03  
% 0.82/1.03  
% 0.82/1.03  
% 0.82/1.03  ------ Proving...
% 0.82/1.03  
% 0.82/1.03  
% 0.82/1.03  % SZS status Theorem for theBenchmark.p
% 0.82/1.03  
% 0.82/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.82/1.03  
% 0.82/1.03  fof(f20,conjecture,(
% 0.82/1.03    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.82/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/1.03  
% 0.82/1.03  fof(f21,negated_conjecture,(
% 0.82/1.03    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.82/1.03    inference(negated_conjecture,[],[f20])).
% 0.82/1.03  
% 0.82/1.03  fof(f27,plain,(
% 0.82/1.03    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.82/1.03    inference(ennf_transformation,[],[f21])).
% 0.82/1.03  
% 0.82/1.03  fof(f40,plain,(
% 0.82/1.03    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.82/1.03    inference(nnf_transformation,[],[f27])).
% 0.82/1.03  
% 0.82/1.03  fof(f41,plain,(
% 0.82/1.03    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.82/1.03    inference(flattening,[],[f40])).
% 0.82/1.03  
% 0.82/1.03  fof(f42,plain,(
% 0.82/1.03    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK2,sK3) | ~r2_hidden(sK1,sK3) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK3)) & ((r2_hidden(sK2,sK3) & r2_hidden(sK1,sK3)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK3)))),
% 0.82/1.03    introduced(choice_axiom,[])).
% 0.82/1.03  
% 0.82/1.03  fof(f43,plain,(
% 0.82/1.03    (~r2_hidden(sK2,sK3) | ~r2_hidden(sK1,sK3) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK3)) & ((r2_hidden(sK2,sK3) & r2_hidden(sK1,sK3)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK3))),
% 0.82/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f42])).
% 0.82/1.03  
% 0.82/1.03  fof(f76,plain,(
% 0.82/1.03    r2_hidden(sK2,sK3) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 0.82/1.03    inference(cnf_transformation,[],[f43])).
% 0.82/1.03  
% 0.82/1.03  fof(f12,axiom,(
% 0.82/1.03    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 0.82/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/1.03  
% 0.82/1.03  fof(f59,plain,(
% 0.82/1.03    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 0.82/1.03    inference(cnf_transformation,[],[f12])).
% 0.82/1.03  
% 0.82/1.03  fof(f91,plain,(
% 0.82/1.03    r2_hidden(sK2,sK3) | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),
% 0.82/1.03    inference(definition_unfolding,[],[f76,f59])).
% 0.82/1.03  
% 0.82/1.03  fof(f1,axiom,(
% 0.82/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.82/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/1.03  
% 0.82/1.03  fof(f44,plain,(
% 0.82/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.82/1.03    inference(cnf_transformation,[],[f1])).
% 0.82/1.03  
% 0.82/1.03  fof(f77,plain,(
% 0.82/1.03    ~r2_hidden(sK2,sK3) | ~r2_hidden(sK1,sK3) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 0.82/1.03    inference(cnf_transformation,[],[f43])).
% 0.82/1.03  
% 0.82/1.03  fof(f90,plain,(
% 0.82/1.03    ~r2_hidden(sK2,sK3) | ~r2_hidden(sK1,sK3) | k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),
% 0.82/1.03    inference(definition_unfolding,[],[f77,f59])).
% 0.82/1.03  
% 0.82/1.03  fof(f15,axiom,(
% 0.82/1.03    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.82/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/1.03  
% 0.82/1.03  fof(f34,plain,(
% 0.82/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.82/1.03    inference(nnf_transformation,[],[f15])).
% 0.82/1.03  
% 0.82/1.03  fof(f35,plain,(
% 0.82/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.82/1.03    inference(flattening,[],[f34])).
% 0.82/1.03  
% 0.82/1.03  fof(f64,plain,(
% 0.82/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.82/1.03    inference(cnf_transformation,[],[f35])).
% 0.82/1.03  
% 0.82/1.03  fof(f81,plain,(
% 0.82/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)) )),
% 0.82/1.03    inference(definition_unfolding,[],[f64,f59])).
% 0.82/1.03  
% 0.82/1.03  fof(f13,axiom,(
% 0.82/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.82/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/1.03  
% 0.82/1.03  fof(f24,plain,(
% 0.82/1.03    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.82/1.03    inference(ennf_transformation,[],[f13])).
% 0.82/1.03  
% 0.82/1.03  fof(f60,plain,(
% 0.82/1.03    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.82/1.03    inference(cnf_transformation,[],[f24])).
% 0.82/1.03  
% 0.82/1.03  fof(f75,plain,(
% 0.82/1.03    r2_hidden(sK1,sK3) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 0.82/1.03    inference(cnf_transformation,[],[f43])).
% 0.82/1.03  
% 0.82/1.03  fof(f92,plain,(
% 0.82/1.03    r2_hidden(sK1,sK3) | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),
% 0.82/1.03    inference(definition_unfolding,[],[f75,f59])).
% 0.82/1.03  
% 0.82/1.03  fof(f65,plain,(
% 0.82/1.03    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.82/1.03    inference(cnf_transformation,[],[f35])).
% 0.82/1.03  
% 0.82/1.03  fof(f80,plain,(
% 0.82/1.03    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.82/1.03    inference(definition_unfolding,[],[f65,f59])).
% 0.82/1.03  
% 0.82/1.03  fof(f5,axiom,(
% 0.82/1.03    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.82/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/1.03  
% 0.82/1.03  fof(f28,plain,(
% 0.82/1.03    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.82/1.03    inference(nnf_transformation,[],[f5])).
% 0.82/1.03  
% 0.82/1.03  fof(f49,plain,(
% 0.82/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.82/1.03    inference(cnf_transformation,[],[f28])).
% 0.82/1.03  
% 0.82/1.03  fof(f48,plain,(
% 0.82/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.82/1.03    inference(cnf_transformation,[],[f28])).
% 0.82/1.03  
% 0.82/1.03  fof(f18,axiom,(
% 0.82/1.03    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.82/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/1.03  
% 0.82/1.03  fof(f36,plain,(
% 0.82/1.03    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 0.82/1.03    inference(nnf_transformation,[],[f18])).
% 0.82/1.03  
% 0.82/1.03  fof(f37,plain,(
% 0.82/1.03    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 0.82/1.03    inference(flattening,[],[f36])).
% 0.82/1.03  
% 0.82/1.03  fof(f71,plain,(
% 0.82/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 0.82/1.03    inference(cnf_transformation,[],[f37])).
% 0.82/1.03  
% 0.82/1.03  fof(f83,plain,(
% 0.82/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) = k1_tarski(X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 0.82/1.03    inference(definition_unfolding,[],[f71,f59])).
% 0.82/1.03  
% 0.82/1.03  fof(f96,plain,(
% 0.82/1.03    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X1)),X2) = k1_tarski(X1) | r2_hidden(X1,X2)) )),
% 0.82/1.03    inference(equality_resolution,[],[f83])).
% 0.82/1.03  
% 0.82/1.03  fof(f68,plain,(
% 0.82/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 0.82/1.03    inference(cnf_transformation,[],[f37])).
% 0.82/1.03  
% 0.82/1.03  fof(f86,plain,(
% 0.82/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) != k1_tarski(X0)) )),
% 0.82/1.03    inference(definition_unfolding,[],[f68,f59])).
% 0.82/1.03  
% 0.82/1.03  cnf(c_312,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_311,plain,( X0 = X0 ),theory(equality) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_2254,plain,
% 0.82/1.03      ( X0 != X1 | X1 = X0 ),
% 0.82/1.03      inference(resolution,[status(thm)],[c_312,c_311]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_30,negated_conjecture,
% 0.82/1.03      ( r2_hidden(sK2,sK3)
% 0.82/1.03      | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
% 0.82/1.03      inference(cnf_transformation,[],[f91]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11793,plain,
% 0.82/1.03      ( r2_hidden(sK2,sK3)
% 0.82/1.03      | k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) = k1_xboole_0 ),
% 0.82/1.03      inference(resolution,[status(thm)],[c_2254,c_30]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_0,plain,
% 0.82/1.03      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 0.82/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_29,negated_conjecture,
% 0.82/1.03      ( ~ r2_hidden(sK1,sK3)
% 0.82/1.03      | ~ r2_hidden(sK2,sK3)
% 0.82/1.03      | k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
% 0.82/1.03      inference(cnf_transformation,[],[f90]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_868,plain,
% 0.82/1.03      ( k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 0.82/1.03      | r2_hidden(sK1,sK3) != iProver_top
% 0.82/1.03      | r2_hidden(sK2,sK3) != iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_1427,plain,
% 0.82/1.03      ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) != k1_xboole_0
% 0.82/1.03      | r2_hidden(sK1,sK3) != iProver_top
% 0.82/1.03      | r2_hidden(sK2,sK3) != iProver_top ),
% 0.82/1.03      inference(demodulation,[status(thm)],[c_0,c_868]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_18,plain,
% 0.82/1.03      ( r2_hidden(X0,X1)
% 0.82/1.03      | ~ r1_tarski(k2_xboole_0(k1_tarski(X2),k1_tarski(X0)),X1) ),
% 0.82/1.03      inference(cnf_transformation,[],[f81]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11015,plain,
% 0.82/1.03      ( r2_hidden(sK1,sK3)
% 0.82/1.03      | ~ r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) ),
% 0.82/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11016,plain,
% 0.82/1.03      ( r2_hidden(sK1,sK3) = iProver_top
% 0.82/1.03      | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) != iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_11015]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11796,plain,
% 0.82/1.03      ( k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) = k1_xboole_0
% 0.82/1.03      | r2_hidden(sK2,sK3) = iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_11793]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_867,plain,
% 0.82/1.03      ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 0.82/1.03      | r2_hidden(sK2,sK3) = iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_1425,plain,
% 0.82/1.03      ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0
% 0.82/1.03      | r2_hidden(sK2,sK3) = iProver_top ),
% 0.82/1.03      inference(demodulation,[status(thm)],[c_0,c_867]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_14,plain,
% 0.82/1.03      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 0.82/1.03      inference(cnf_transformation,[],[f60]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_883,plain,
% 0.82/1.03      ( k2_xboole_0(k1_tarski(X0),X1) = X1
% 0.82/1.03      | r2_hidden(X0,X1) != iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11725,plain,
% 0.82/1.03      ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0
% 0.82/1.03      | k2_xboole_0(k1_tarski(sK2),sK3) = sK3 ),
% 0.82/1.03      inference(superposition,[status(thm)],[c_1425,c_883]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_31,negated_conjecture,
% 0.82/1.03      ( r2_hidden(sK1,sK3)
% 0.82/1.03      | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
% 0.82/1.03      inference(cnf_transformation,[],[f92]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_866,plain,
% 0.82/1.03      ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 0.82/1.03      | r2_hidden(sK1,sK3) = iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_1426,plain,
% 0.82/1.03      ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0
% 0.82/1.03      | r2_hidden(sK1,sK3) = iProver_top ),
% 0.82/1.03      inference(demodulation,[status(thm)],[c_0,c_866]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_17,plain,
% 0.82/1.03      ( ~ r2_hidden(X0,X1)
% 0.82/1.03      | ~ r2_hidden(X2,X1)
% 0.82/1.03      | r1_tarski(k2_xboole_0(k1_tarski(X2),k1_tarski(X0)),X1) ),
% 0.82/1.03      inference(cnf_transformation,[],[f80]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_2969,plain,
% 0.82/1.03      ( ~ r2_hidden(X0,sK3)
% 0.82/1.03      | ~ r2_hidden(sK2,sK3)
% 0.82/1.03      | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(X0)),sK3) ),
% 0.82/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_9815,plain,
% 0.82/1.03      ( ~ r2_hidden(sK1,sK3)
% 0.82/1.03      | ~ r2_hidden(sK2,sK3)
% 0.82/1.03      | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) ),
% 0.82/1.03      inference(instantiation,[status(thm)],[c_2969]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_9816,plain,
% 0.82/1.03      ( r2_hidden(sK1,sK3) != iProver_top
% 0.82/1.03      | r2_hidden(sK2,sK3) != iProver_top
% 0.82/1.03      | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_9815]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_4,plain,
% 0.82/1.03      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 0.82/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_1261,plain,
% 0.82/1.03      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
% 0.82/1.03      | k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) = k1_xboole_0 ),
% 0.82/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11019,plain,
% 0.82/1.03      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3)
% 0.82/1.03      | k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0 ),
% 0.82/1.03      inference(instantiation,[status(thm)],[c_1261]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11020,plain,
% 0.82/1.03      ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0
% 0.82/1.03      | r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) != iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_11019]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_12128,plain,
% 0.82/1.03      ( k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = k1_xboole_0 ),
% 0.82/1.03      inference(global_propositional_subsumption,
% 0.82/1.03                [status(thm)],
% 0.82/1.03                [c_11725,c_1425,c_1426,c_9816,c_11020]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_5,plain,
% 0.82/1.03      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 0.82/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_889,plain,
% 0.82/1.03      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 0.82/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_12136,plain,
% 0.82/1.03      ( r1_tarski(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),sK3) = iProver_top ),
% 0.82/1.03      inference(superposition,[status(thm)],[c_12128,c_889]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_12252,plain,
% 0.82/1.03      ( k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) = k1_xboole_0 ),
% 0.82/1.03      inference(global_propositional_subsumption,
% 0.82/1.03                [status(thm)],
% 0.82/1.03                [c_11793,c_1425,c_1426,c_1427,c_9816,c_11016,c_11020,
% 0.82/1.03                 c_11796,c_12136]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_12258,plain,
% 0.82/1.03      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
% 0.82/1.03      inference(resolution,[status(thm)],[c_12252,c_5]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_12396,plain,
% 0.82/1.03      ( r2_hidden(sK2,sK3) ),
% 0.82/1.03      inference(resolution,[status(thm)],[c_12258,c_18]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_22,plain,
% 0.82/1.03      ( r2_hidden(X0,X1)
% 0.82/1.03      | k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X0)),X1) = k1_tarski(X0) ),
% 0.82/1.03      inference(cnf_transformation,[],[f96]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11026,plain,
% 0.82/1.03      ( r2_hidden(sK1,sK3)
% 0.82/1.03      | k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)),sK3) = k1_tarski(sK1) ),
% 0.82/1.03      inference(instantiation,[status(thm)],[c_22]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_25,plain,
% 0.82/1.03      ( ~ r2_hidden(X0,X1)
% 0.82/1.03      | k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X2)),X1) != k1_tarski(X0) ),
% 0.82/1.03      inference(cnf_transformation,[],[f86]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_9776,plain,
% 0.82/1.03      ( ~ r2_hidden(sK1,sK3)
% 0.82/1.03      | k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(X0)),sK3) != k1_tarski(sK1) ),
% 0.82/1.03      inference(instantiation,[status(thm)],[c_25]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11025,plain,
% 0.82/1.03      ( ~ r2_hidden(sK1,sK3)
% 0.82/1.03      | k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)),sK3) != k1_tarski(sK1) ),
% 0.82/1.03      inference(instantiation,[status(thm)],[c_9776]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_11027,plain,
% 0.82/1.03      ( k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)),sK3) != k1_tarski(sK1)
% 0.82/1.03      | r2_hidden(sK1,sK3) != iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_11025]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(c_33,plain,
% 0.82/1.03      ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 0.82/1.03      | r2_hidden(sK2,sK3) = iProver_top ),
% 0.82/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 0.82/1.03  
% 0.82/1.03  cnf(contradiction,plain,
% 0.82/1.03      ( $false ),
% 0.82/1.03      inference(minisat,
% 0.82/1.03                [status(thm)],
% 0.82/1.03                [c_12396,c_12136,c_12128,c_11026,c_11027,c_11016,c_1427,
% 0.82/1.03                 c_29,c_33]) ).
% 0.82/1.03  
% 0.82/1.03  
% 0.82/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.82/1.03  
% 0.82/1.03  ------                               Statistics
% 0.82/1.03  
% 0.82/1.03  ------ Selected
% 0.82/1.03  
% 0.82/1.03  total_time:                             0.399
% 0.82/1.03  
%------------------------------------------------------------------------------
