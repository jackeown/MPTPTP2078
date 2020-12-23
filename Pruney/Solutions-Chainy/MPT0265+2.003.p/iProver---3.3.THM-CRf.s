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
% DateTime   : Thu Dec  3 11:35:20 EST 2020

% Result     : Theorem 12.25s
% Output     : CNFRefutation 12.25s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 217 expanded)
%              Number of clauses        :   40 (  60 expanded)
%              Number of leaves         :   11 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  238 ( 712 expanded)
%              Number of equality atoms :  113 ( 340 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f79,f73])).

fof(f114,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(k2_tarski(X1,X1),X2) = k2_tarski(X1,X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f97])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f72,f73,f73])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK4,sK6),sK5) != k1_tarski(sK4)
      & ( sK4 = sK6
        | ~ r2_hidden(sK6,sK5) )
      & r2_hidden(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k3_xboole_0(k2_tarski(sK4,sK6),sK5) != k1_tarski(sK4)
    & ( sK4 = sK6
      | ~ r2_hidden(sK6,sK5) )
    & r2_hidden(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f43])).

fof(f81,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f78,f73])).

fof(f82,plain,
    ( sK4 = sK6
    | ~ r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    k3_xboole_0(k2_tarski(sK4,sK6),sK5) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f101,plain,(
    k4_xboole_0(k2_tarski(sK4,sK6),k4_xboole_0(k2_tarski(sK4,sK6),sK5)) != k2_tarski(sK4,sK4) ),
    inference(definition_unfolding,[],[f83,f66,f73])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_29,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X0),X1) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3820,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2))
    | k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(X1,X2)) = k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_16446,plain,
    ( r2_hidden(sK4,k4_xboole_0(sK5,X0))
    | k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK5,X0)) = k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_3820])).

cnf(c_64107,plain,
    ( r2_hidden(sK4,k4_xboole_0(sK5,sK5))
    | k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK5,sK5)) = k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_16446])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_20,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1669,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X1,X1)) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_20])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1670,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_2173,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(superposition,[status(thm)],[c_1670,c_0])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1294,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k2_tarski(X2,X0),X1) = k2_tarski(X2,X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1299,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X0)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5383,plain,
    ( k4_xboole_0(k2_tarski(X0,sK4),sK5) = k2_tarski(X0,X0)
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1299])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(sK6,sK5)
    | sK4 = sK6 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1295,plain,
    ( sK4 = sK6
    | r2_hidden(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6517,plain,
    ( k4_xboole_0(k2_tarski(sK6,sK4),sK5) = k2_tarski(sK6,sK6)
    | sK6 = sK4 ),
    inference(superposition,[status(thm)],[c_5383,c_1295])).

cnf(c_6543,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK6),sK5) = k2_tarski(sK6,sK6)
    | sK6 = sK4 ),
    inference(superposition,[status(thm)],[c_2173,c_6517])).

cnf(c_34,negated_conjecture,
    ( k4_xboole_0(k2_tarski(sK4,sK6),k4_xboole_0(k2_tarski(sK4,sK6),sK5)) != k2_tarski(sK4,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_7057,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK6),k2_tarski(sK6,sK6)) != k2_tarski(sK4,sK4)
    | sK6 = sK4 ),
    inference(superposition,[status(thm)],[c_6543,c_34])).

cnf(c_36372,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK6)) != k2_tarski(sK4,sK4)
    | sK6 = sK4 ),
    inference(demodulation,[status(thm)],[c_1669,c_7057])).

cnf(c_37,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1301,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),X1) = k2_tarski(X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1307,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_18459,plain,
    ( sK6 = sK4
    | r2_hidden(X0,k2_tarski(sK6,sK6)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6517,c_1307])).

cnf(c_19181,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(sK6,sK6)) = k2_tarski(X0,X0)
    | sK6 = sK4
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_18459])).

cnf(c_19208,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK6)) = k2_tarski(sK4,sK4)
    | sK6 = sK4
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19181])).

cnf(c_36659,plain,
    ( sK6 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36372,c_37,c_19208])).

cnf(c_36673,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(k2_tarski(sK4,sK4),sK5)) != k2_tarski(sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_36659,c_34])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1296,plain,
    ( k2_xboole_0(k2_tarski(X0,X1),X2) = X2
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1872,plain,
    ( k2_xboole_0(k2_tarski(sK4,X0),sK5) = sK5
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1296])).

cnf(c_2506,plain,
    ( k2_xboole_0(k2_tarski(sK4,sK4),sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1294,c_1872])).

cnf(c_2549,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),sK5) = k4_xboole_0(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_2506,c_20])).

cnf(c_36675,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK5,sK5)) != k2_tarski(sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_36673,c_2549])).

cnf(c_1568,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(X0,sK5))
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6485,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(sK5,sK5))
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_64107,c_36675,c_6485,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:08:01 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 12.25/2.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.25/2.03  
% 12.25/2.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.25/2.03  
% 12.25/2.03  ------  iProver source info
% 12.25/2.03  
% 12.25/2.03  git: date: 2020-06-30 10:37:57 +0100
% 12.25/2.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.25/2.03  git: non_committed_changes: false
% 12.25/2.03  git: last_make_outside_of_git: false
% 12.25/2.03  
% 12.25/2.03  ------ 
% 12.25/2.03  
% 12.25/2.03  ------ Input Options
% 12.25/2.03  
% 12.25/2.03  --out_options                           all
% 12.25/2.03  --tptp_safe_out                         true
% 12.25/2.03  --problem_path                          ""
% 12.25/2.03  --include_path                          ""
% 12.25/2.03  --clausifier                            res/vclausify_rel
% 12.25/2.03  --clausifier_options                    --mode clausify
% 12.25/2.03  --stdin                                 false
% 12.25/2.03  --stats_out                             all
% 12.25/2.03  
% 12.25/2.03  ------ General Options
% 12.25/2.03  
% 12.25/2.03  --fof                                   false
% 12.25/2.03  --time_out_real                         305.
% 12.25/2.03  --time_out_virtual                      -1.
% 12.25/2.03  --symbol_type_check                     false
% 12.25/2.03  --clausify_out                          false
% 12.25/2.03  --sig_cnt_out                           false
% 12.25/2.03  --trig_cnt_out                          false
% 12.25/2.03  --trig_cnt_out_tolerance                1.
% 12.25/2.03  --trig_cnt_out_sk_spl                   false
% 12.25/2.03  --abstr_cl_out                          false
% 12.25/2.03  
% 12.25/2.03  ------ Global Options
% 12.25/2.03  
% 12.25/2.03  --schedule                              default
% 12.25/2.03  --add_important_lit                     false
% 12.25/2.03  --prop_solver_per_cl                    1000
% 12.25/2.03  --min_unsat_core                        false
% 12.25/2.03  --soft_assumptions                      false
% 12.25/2.03  --soft_lemma_size                       3
% 12.25/2.03  --prop_impl_unit_size                   0
% 12.25/2.03  --prop_impl_unit                        []
% 12.25/2.03  --share_sel_clauses                     true
% 12.25/2.03  --reset_solvers                         false
% 12.25/2.03  --bc_imp_inh                            [conj_cone]
% 12.25/2.03  --conj_cone_tolerance                   3.
% 12.25/2.03  --extra_neg_conj                        none
% 12.25/2.03  --large_theory_mode                     true
% 12.25/2.03  --prolific_symb_bound                   200
% 12.25/2.03  --lt_threshold                          2000
% 12.25/2.03  --clause_weak_htbl                      true
% 12.25/2.03  --gc_record_bc_elim                     false
% 12.25/2.03  
% 12.25/2.03  ------ Preprocessing Options
% 12.25/2.03  
% 12.25/2.03  --preprocessing_flag                    true
% 12.25/2.03  --time_out_prep_mult                    0.1
% 12.25/2.03  --splitting_mode                        input
% 12.25/2.03  --splitting_grd                         true
% 12.25/2.03  --splitting_cvd                         false
% 12.25/2.03  --splitting_cvd_svl                     false
% 12.25/2.03  --splitting_nvd                         32
% 12.25/2.03  --sub_typing                            true
% 12.25/2.03  --prep_gs_sim                           true
% 12.25/2.03  --prep_unflatten                        true
% 12.25/2.03  --prep_res_sim                          true
% 12.25/2.03  --prep_upred                            true
% 12.25/2.03  --prep_sem_filter                       exhaustive
% 12.25/2.03  --prep_sem_filter_out                   false
% 12.25/2.03  --pred_elim                             true
% 12.25/2.03  --res_sim_input                         true
% 12.25/2.03  --eq_ax_congr_red                       true
% 12.25/2.03  --pure_diseq_elim                       true
% 12.25/2.03  --brand_transform                       false
% 12.25/2.03  --non_eq_to_eq                          false
% 12.25/2.03  --prep_def_merge                        true
% 12.25/2.03  --prep_def_merge_prop_impl              false
% 12.25/2.03  --prep_def_merge_mbd                    true
% 12.25/2.03  --prep_def_merge_tr_red                 false
% 12.25/2.03  --prep_def_merge_tr_cl                  false
% 12.25/2.03  --smt_preprocessing                     true
% 12.25/2.03  --smt_ac_axioms                         fast
% 12.25/2.03  --preprocessed_out                      false
% 12.25/2.03  --preprocessed_stats                    false
% 12.25/2.03  
% 12.25/2.03  ------ Abstraction refinement Options
% 12.25/2.03  
% 12.25/2.03  --abstr_ref                             []
% 12.25/2.03  --abstr_ref_prep                        false
% 12.25/2.03  --abstr_ref_until_sat                   false
% 12.25/2.03  --abstr_ref_sig_restrict                funpre
% 12.25/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 12.25/2.03  --abstr_ref_under                       []
% 12.25/2.03  
% 12.25/2.03  ------ SAT Options
% 12.25/2.03  
% 12.25/2.03  --sat_mode                              false
% 12.25/2.03  --sat_fm_restart_options                ""
% 12.25/2.03  --sat_gr_def                            false
% 12.25/2.03  --sat_epr_types                         true
% 12.25/2.03  --sat_non_cyclic_types                  false
% 12.25/2.03  --sat_finite_models                     false
% 12.25/2.03  --sat_fm_lemmas                         false
% 12.25/2.03  --sat_fm_prep                           false
% 12.25/2.03  --sat_fm_uc_incr                        true
% 12.25/2.03  --sat_out_model                         small
% 12.25/2.03  --sat_out_clauses                       false
% 12.25/2.03  
% 12.25/2.03  ------ QBF Options
% 12.25/2.03  
% 12.25/2.03  --qbf_mode                              false
% 12.25/2.03  --qbf_elim_univ                         false
% 12.25/2.03  --qbf_dom_inst                          none
% 12.25/2.03  --qbf_dom_pre_inst                      false
% 12.25/2.03  --qbf_sk_in                             false
% 12.25/2.03  --qbf_pred_elim                         true
% 12.25/2.03  --qbf_split                             512
% 12.25/2.03  
% 12.25/2.03  ------ BMC1 Options
% 12.25/2.03  
% 12.25/2.03  --bmc1_incremental                      false
% 12.25/2.03  --bmc1_axioms                           reachable_all
% 12.25/2.03  --bmc1_min_bound                        0
% 12.25/2.03  --bmc1_max_bound                        -1
% 12.25/2.03  --bmc1_max_bound_default                -1
% 12.25/2.03  --bmc1_symbol_reachability              true
% 12.25/2.03  --bmc1_property_lemmas                  false
% 12.25/2.03  --bmc1_k_induction                      false
% 12.25/2.03  --bmc1_non_equiv_states                 false
% 12.25/2.03  --bmc1_deadlock                         false
% 12.25/2.03  --bmc1_ucm                              false
% 12.25/2.03  --bmc1_add_unsat_core                   none
% 12.25/2.03  --bmc1_unsat_core_children              false
% 12.25/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 12.25/2.03  --bmc1_out_stat                         full
% 12.25/2.03  --bmc1_ground_init                      false
% 12.25/2.03  --bmc1_pre_inst_next_state              false
% 12.25/2.03  --bmc1_pre_inst_state                   false
% 12.25/2.03  --bmc1_pre_inst_reach_state             false
% 12.25/2.03  --bmc1_out_unsat_core                   false
% 12.25/2.03  --bmc1_aig_witness_out                  false
% 12.25/2.03  --bmc1_verbose                          false
% 12.25/2.03  --bmc1_dump_clauses_tptp                false
% 12.25/2.03  --bmc1_dump_unsat_core_tptp             false
% 12.25/2.03  --bmc1_dump_file                        -
% 12.25/2.03  --bmc1_ucm_expand_uc_limit              128
% 12.25/2.03  --bmc1_ucm_n_expand_iterations          6
% 12.25/2.03  --bmc1_ucm_extend_mode                  1
% 12.25/2.03  --bmc1_ucm_init_mode                    2
% 12.25/2.03  --bmc1_ucm_cone_mode                    none
% 12.25/2.03  --bmc1_ucm_reduced_relation_type        0
% 12.25/2.03  --bmc1_ucm_relax_model                  4
% 12.25/2.03  --bmc1_ucm_full_tr_after_sat            true
% 12.25/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 12.25/2.03  --bmc1_ucm_layered_model                none
% 12.25/2.03  --bmc1_ucm_max_lemma_size               10
% 12.25/2.03  
% 12.25/2.03  ------ AIG Options
% 12.25/2.03  
% 12.25/2.03  --aig_mode                              false
% 12.25/2.03  
% 12.25/2.03  ------ Instantiation Options
% 12.25/2.03  
% 12.25/2.03  --instantiation_flag                    true
% 12.25/2.03  --inst_sos_flag                         false
% 12.25/2.03  --inst_sos_phase                        true
% 12.25/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.25/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.25/2.03  --inst_lit_sel_side                     num_symb
% 12.25/2.03  --inst_solver_per_active                1400
% 12.25/2.03  --inst_solver_calls_frac                1.
% 12.25/2.03  --inst_passive_queue_type               priority_queues
% 12.25/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.25/2.03  --inst_passive_queues_freq              [25;2]
% 12.25/2.03  --inst_dismatching                      true
% 12.25/2.03  --inst_eager_unprocessed_to_passive     true
% 12.25/2.03  --inst_prop_sim_given                   true
% 12.25/2.03  --inst_prop_sim_new                     false
% 12.25/2.03  --inst_subs_new                         false
% 12.25/2.03  --inst_eq_res_simp                      false
% 12.25/2.03  --inst_subs_given                       false
% 12.25/2.03  --inst_orphan_elimination               true
% 12.25/2.03  --inst_learning_loop_flag               true
% 12.25/2.03  --inst_learning_start                   3000
% 12.25/2.03  --inst_learning_factor                  2
% 12.25/2.03  --inst_start_prop_sim_after_learn       3
% 12.25/2.03  --inst_sel_renew                        solver
% 12.25/2.03  --inst_lit_activity_flag                true
% 12.25/2.03  --inst_restr_to_given                   false
% 12.25/2.03  --inst_activity_threshold               500
% 12.25/2.03  --inst_out_proof                        true
% 12.25/2.03  
% 12.25/2.03  ------ Resolution Options
% 12.25/2.03  
% 12.25/2.03  --resolution_flag                       true
% 12.25/2.03  --res_lit_sel                           adaptive
% 12.25/2.03  --res_lit_sel_side                      none
% 12.25/2.03  --res_ordering                          kbo
% 12.25/2.03  --res_to_prop_solver                    active
% 12.25/2.03  --res_prop_simpl_new                    false
% 12.25/2.03  --res_prop_simpl_given                  true
% 12.25/2.03  --res_passive_queue_type                priority_queues
% 12.25/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.25/2.03  --res_passive_queues_freq               [15;5]
% 12.25/2.03  --res_forward_subs                      full
% 12.25/2.03  --res_backward_subs                     full
% 12.25/2.03  --res_forward_subs_resolution           true
% 12.25/2.03  --res_backward_subs_resolution          true
% 12.25/2.03  --res_orphan_elimination                true
% 12.25/2.03  --res_time_limit                        2.
% 12.25/2.03  --res_out_proof                         true
% 12.25/2.03  
% 12.25/2.03  ------ Superposition Options
% 12.25/2.03  
% 12.25/2.03  --superposition_flag                    true
% 12.25/2.03  --sup_passive_queue_type                priority_queues
% 12.25/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.25/2.03  --sup_passive_queues_freq               [8;1;4]
% 12.25/2.03  --demod_completeness_check              fast
% 12.25/2.03  --demod_use_ground                      true
% 12.25/2.03  --sup_to_prop_solver                    passive
% 12.25/2.03  --sup_prop_simpl_new                    true
% 12.25/2.03  --sup_prop_simpl_given                  true
% 12.25/2.03  --sup_fun_splitting                     false
% 12.25/2.03  --sup_smt_interval                      50000
% 12.25/2.03  
% 12.25/2.03  ------ Superposition Simplification Setup
% 12.25/2.03  
% 12.25/2.03  --sup_indices_passive                   []
% 12.25/2.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.25/2.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.25/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.25/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 12.25/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.25/2.03  --sup_full_bw                           [BwDemod]
% 12.25/2.03  --sup_immed_triv                        [TrivRules]
% 12.25/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.25/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.25/2.03  --sup_immed_bw_main                     []
% 12.25/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.25/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 12.25/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.25/2.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.25/2.03  
% 12.25/2.03  ------ Combination Options
% 12.25/2.03  
% 12.25/2.03  --comb_res_mult                         3
% 12.25/2.03  --comb_sup_mult                         2
% 12.25/2.03  --comb_inst_mult                        10
% 12.25/2.03  
% 12.25/2.03  ------ Debug Options
% 12.25/2.03  
% 12.25/2.03  --dbg_backtrace                         false
% 12.25/2.03  --dbg_dump_prop_clauses                 false
% 12.25/2.03  --dbg_dump_prop_clauses_file            -
% 12.25/2.03  --dbg_out_stat                          false
% 12.25/2.03  ------ Parsing...
% 12.25/2.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.25/2.03  
% 12.25/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 12.25/2.03  
% 12.25/2.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.25/2.03  
% 12.25/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.25/2.03  ------ Proving...
% 12.25/2.03  ------ Problem Properties 
% 12.25/2.03  
% 12.25/2.03  
% 12.25/2.03  clauses                                 36
% 12.25/2.03  conjectures                             3
% 12.25/2.03  EPR                                     2
% 12.25/2.03  Horn                                    24
% 12.25/2.03  unary                                   8
% 12.25/2.03  binary                                  11
% 12.25/2.03  lits                                    84
% 12.25/2.03  lits eq                                 28
% 12.25/2.03  fd_pure                                 0
% 12.25/2.03  fd_pseudo                               0
% 12.25/2.03  fd_cond                                 0
% 12.25/2.03  fd_pseudo_cond                          12
% 12.25/2.03  AC symbols                              0
% 12.25/2.03  
% 12.25/2.03  ------ Schedule dynamic 5 is on 
% 12.25/2.03  
% 12.25/2.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.25/2.03  
% 12.25/2.03  
% 12.25/2.03  ------ 
% 12.25/2.03  Current options:
% 12.25/2.03  ------ 
% 12.25/2.03  
% 12.25/2.03  ------ Input Options
% 12.25/2.03  
% 12.25/2.03  --out_options                           all
% 12.25/2.03  --tptp_safe_out                         true
% 12.25/2.03  --problem_path                          ""
% 12.25/2.03  --include_path                          ""
% 12.25/2.03  --clausifier                            res/vclausify_rel
% 12.25/2.03  --clausifier_options                    --mode clausify
% 12.25/2.03  --stdin                                 false
% 12.25/2.03  --stats_out                             all
% 12.25/2.03  
% 12.25/2.03  ------ General Options
% 12.25/2.03  
% 12.25/2.03  --fof                                   false
% 12.25/2.03  --time_out_real                         305.
% 12.25/2.03  --time_out_virtual                      -1.
% 12.25/2.03  --symbol_type_check                     false
% 12.25/2.03  --clausify_out                          false
% 12.25/2.03  --sig_cnt_out                           false
% 12.25/2.03  --trig_cnt_out                          false
% 12.25/2.03  --trig_cnt_out_tolerance                1.
% 12.25/2.03  --trig_cnt_out_sk_spl                   false
% 12.25/2.03  --abstr_cl_out                          false
% 12.25/2.03  
% 12.25/2.03  ------ Global Options
% 12.25/2.03  
% 12.25/2.03  --schedule                              default
% 12.25/2.03  --add_important_lit                     false
% 12.25/2.03  --prop_solver_per_cl                    1000
% 12.25/2.03  --min_unsat_core                        false
% 12.25/2.03  --soft_assumptions                      false
% 12.25/2.03  --soft_lemma_size                       3
% 12.25/2.03  --prop_impl_unit_size                   0
% 12.25/2.03  --prop_impl_unit                        []
% 12.25/2.03  --share_sel_clauses                     true
% 12.25/2.03  --reset_solvers                         false
% 12.25/2.03  --bc_imp_inh                            [conj_cone]
% 12.25/2.03  --conj_cone_tolerance                   3.
% 12.25/2.03  --extra_neg_conj                        none
% 12.25/2.03  --large_theory_mode                     true
% 12.25/2.03  --prolific_symb_bound                   200
% 12.25/2.03  --lt_threshold                          2000
% 12.25/2.03  --clause_weak_htbl                      true
% 12.25/2.03  --gc_record_bc_elim                     false
% 12.25/2.03  
% 12.25/2.03  ------ Preprocessing Options
% 12.25/2.03  
% 12.25/2.03  --preprocessing_flag                    true
% 12.25/2.03  --time_out_prep_mult                    0.1
% 12.25/2.03  --splitting_mode                        input
% 12.25/2.03  --splitting_grd                         true
% 12.25/2.03  --splitting_cvd                         false
% 12.25/2.03  --splitting_cvd_svl                     false
% 12.25/2.03  --splitting_nvd                         32
% 12.25/2.03  --sub_typing                            true
% 12.25/2.03  --prep_gs_sim                           true
% 12.25/2.03  --prep_unflatten                        true
% 12.25/2.03  --prep_res_sim                          true
% 12.25/2.03  --prep_upred                            true
% 12.25/2.03  --prep_sem_filter                       exhaustive
% 12.25/2.03  --prep_sem_filter_out                   false
% 12.25/2.03  --pred_elim                             true
% 12.25/2.03  --res_sim_input                         true
% 12.25/2.03  --eq_ax_congr_red                       true
% 12.25/2.03  --pure_diseq_elim                       true
% 12.25/2.03  --brand_transform                       false
% 12.25/2.03  --non_eq_to_eq                          false
% 12.25/2.03  --prep_def_merge                        true
% 12.25/2.03  --prep_def_merge_prop_impl              false
% 12.25/2.03  --prep_def_merge_mbd                    true
% 12.25/2.03  --prep_def_merge_tr_red                 false
% 12.25/2.03  --prep_def_merge_tr_cl                  false
% 12.25/2.03  --smt_preprocessing                     true
% 12.25/2.03  --smt_ac_axioms                         fast
% 12.25/2.03  --preprocessed_out                      false
% 12.25/2.03  --preprocessed_stats                    false
% 12.25/2.03  
% 12.25/2.03  ------ Abstraction refinement Options
% 12.25/2.03  
% 12.25/2.03  --abstr_ref                             []
% 12.25/2.03  --abstr_ref_prep                        false
% 12.25/2.03  --abstr_ref_until_sat                   false
% 12.25/2.03  --abstr_ref_sig_restrict                funpre
% 12.25/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 12.25/2.03  --abstr_ref_under                       []
% 12.25/2.03  
% 12.25/2.03  ------ SAT Options
% 12.25/2.03  
% 12.25/2.03  --sat_mode                              false
% 12.25/2.03  --sat_fm_restart_options                ""
% 12.25/2.03  --sat_gr_def                            false
% 12.25/2.03  --sat_epr_types                         true
% 12.25/2.03  --sat_non_cyclic_types                  false
% 12.25/2.03  --sat_finite_models                     false
% 12.25/2.03  --sat_fm_lemmas                         false
% 12.25/2.03  --sat_fm_prep                           false
% 12.25/2.03  --sat_fm_uc_incr                        true
% 12.25/2.03  --sat_out_model                         small
% 12.25/2.03  --sat_out_clauses                       false
% 12.25/2.03  
% 12.25/2.03  ------ QBF Options
% 12.25/2.03  
% 12.25/2.03  --qbf_mode                              false
% 12.25/2.03  --qbf_elim_univ                         false
% 12.25/2.03  --qbf_dom_inst                          none
% 12.25/2.03  --qbf_dom_pre_inst                      false
% 12.25/2.03  --qbf_sk_in                             false
% 12.25/2.03  --qbf_pred_elim                         true
% 12.25/2.03  --qbf_split                             512
% 12.25/2.03  
% 12.25/2.03  ------ BMC1 Options
% 12.25/2.03  
% 12.25/2.03  --bmc1_incremental                      false
% 12.25/2.03  --bmc1_axioms                           reachable_all
% 12.25/2.03  --bmc1_min_bound                        0
% 12.25/2.03  --bmc1_max_bound                        -1
% 12.25/2.03  --bmc1_max_bound_default                -1
% 12.25/2.03  --bmc1_symbol_reachability              true
% 12.25/2.03  --bmc1_property_lemmas                  false
% 12.25/2.03  --bmc1_k_induction                      false
% 12.25/2.03  --bmc1_non_equiv_states                 false
% 12.25/2.03  --bmc1_deadlock                         false
% 12.25/2.03  --bmc1_ucm                              false
% 12.25/2.03  --bmc1_add_unsat_core                   none
% 12.25/2.03  --bmc1_unsat_core_children              false
% 12.25/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 12.25/2.03  --bmc1_out_stat                         full
% 12.25/2.03  --bmc1_ground_init                      false
% 12.25/2.03  --bmc1_pre_inst_next_state              false
% 12.25/2.03  --bmc1_pre_inst_state                   false
% 12.25/2.03  --bmc1_pre_inst_reach_state             false
% 12.25/2.03  --bmc1_out_unsat_core                   false
% 12.25/2.03  --bmc1_aig_witness_out                  false
% 12.25/2.03  --bmc1_verbose                          false
% 12.25/2.03  --bmc1_dump_clauses_tptp                false
% 12.25/2.03  --bmc1_dump_unsat_core_tptp             false
% 12.25/2.03  --bmc1_dump_file                        -
% 12.25/2.03  --bmc1_ucm_expand_uc_limit              128
% 12.25/2.03  --bmc1_ucm_n_expand_iterations          6
% 12.25/2.03  --bmc1_ucm_extend_mode                  1
% 12.25/2.03  --bmc1_ucm_init_mode                    2
% 12.25/2.03  --bmc1_ucm_cone_mode                    none
% 12.25/2.03  --bmc1_ucm_reduced_relation_type        0
% 12.25/2.03  --bmc1_ucm_relax_model                  4
% 12.25/2.03  --bmc1_ucm_full_tr_after_sat            true
% 12.25/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 12.25/2.03  --bmc1_ucm_layered_model                none
% 12.25/2.03  --bmc1_ucm_max_lemma_size               10
% 12.25/2.03  
% 12.25/2.03  ------ AIG Options
% 12.25/2.03  
% 12.25/2.03  --aig_mode                              false
% 12.25/2.03  
% 12.25/2.03  ------ Instantiation Options
% 12.25/2.03  
% 12.25/2.03  --instantiation_flag                    true
% 12.25/2.03  --inst_sos_flag                         false
% 12.25/2.03  --inst_sos_phase                        true
% 12.25/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.25/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.25/2.03  --inst_lit_sel_side                     none
% 12.25/2.03  --inst_solver_per_active                1400
% 12.25/2.03  --inst_solver_calls_frac                1.
% 12.25/2.03  --inst_passive_queue_type               priority_queues
% 12.25/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.25/2.03  --inst_passive_queues_freq              [25;2]
% 12.25/2.03  --inst_dismatching                      true
% 12.25/2.03  --inst_eager_unprocessed_to_passive     true
% 12.25/2.03  --inst_prop_sim_given                   true
% 12.25/2.03  --inst_prop_sim_new                     false
% 12.25/2.03  --inst_subs_new                         false
% 12.25/2.03  --inst_eq_res_simp                      false
% 12.25/2.03  --inst_subs_given                       false
% 12.25/2.03  --inst_orphan_elimination               true
% 12.25/2.03  --inst_learning_loop_flag               true
% 12.25/2.03  --inst_learning_start                   3000
% 12.25/2.03  --inst_learning_factor                  2
% 12.25/2.03  --inst_start_prop_sim_after_learn       3
% 12.25/2.03  --inst_sel_renew                        solver
% 12.25/2.03  --inst_lit_activity_flag                true
% 12.25/2.03  --inst_restr_to_given                   false
% 12.25/2.03  --inst_activity_threshold               500
% 12.25/2.03  --inst_out_proof                        true
% 12.25/2.03  
% 12.25/2.03  ------ Resolution Options
% 12.25/2.03  
% 12.25/2.03  --resolution_flag                       false
% 12.25/2.03  --res_lit_sel                           adaptive
% 12.25/2.03  --res_lit_sel_side                      none
% 12.25/2.03  --res_ordering                          kbo
% 12.25/2.03  --res_to_prop_solver                    active
% 12.25/2.03  --res_prop_simpl_new                    false
% 12.25/2.03  --res_prop_simpl_given                  true
% 12.25/2.03  --res_passive_queue_type                priority_queues
% 12.25/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.25/2.03  --res_passive_queues_freq               [15;5]
% 12.25/2.03  --res_forward_subs                      full
% 12.25/2.03  --res_backward_subs                     full
% 12.25/2.03  --res_forward_subs_resolution           true
% 12.25/2.03  --res_backward_subs_resolution          true
% 12.25/2.03  --res_orphan_elimination                true
% 12.25/2.03  --res_time_limit                        2.
% 12.25/2.03  --res_out_proof                         true
% 12.25/2.03  
% 12.25/2.03  ------ Superposition Options
% 12.25/2.03  
% 12.25/2.03  --superposition_flag                    true
% 12.25/2.03  --sup_passive_queue_type                priority_queues
% 12.25/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.25/2.03  --sup_passive_queues_freq               [8;1;4]
% 12.25/2.03  --demod_completeness_check              fast
% 12.25/2.03  --demod_use_ground                      true
% 12.25/2.03  --sup_to_prop_solver                    passive
% 12.25/2.03  --sup_prop_simpl_new                    true
% 12.25/2.03  --sup_prop_simpl_given                  true
% 12.25/2.03  --sup_fun_splitting                     false
% 12.25/2.03  --sup_smt_interval                      50000
% 12.25/2.03  
% 12.25/2.03  ------ Superposition Simplification Setup
% 12.25/2.03  
% 12.25/2.03  --sup_indices_passive                   []
% 12.25/2.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.25/2.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.25/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.25/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 12.25/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.25/2.03  --sup_full_bw                           [BwDemod]
% 12.25/2.03  --sup_immed_triv                        [TrivRules]
% 12.25/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.25/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.25/2.03  --sup_immed_bw_main                     []
% 12.25/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.25/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 12.25/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.25/2.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.25/2.03  
% 12.25/2.03  ------ Combination Options
% 12.25/2.03  
% 12.25/2.03  --comb_res_mult                         3
% 12.25/2.03  --comb_sup_mult                         2
% 12.25/2.03  --comb_inst_mult                        10
% 12.25/2.03  
% 12.25/2.03  ------ Debug Options
% 12.25/2.03  
% 12.25/2.03  --dbg_backtrace                         false
% 12.25/2.03  --dbg_dump_prop_clauses                 false
% 12.25/2.03  --dbg_dump_prop_clauses_file            -
% 12.25/2.03  --dbg_out_stat                          false
% 12.25/2.03  
% 12.25/2.03  
% 12.25/2.03  
% 12.25/2.03  
% 12.25/2.03  ------ Proving...
% 12.25/2.03  
% 12.25/2.03  
% 12.25/2.03  % SZS status Theorem for theBenchmark.p
% 12.25/2.03  
% 12.25/2.03  % SZS output start CNFRefutation for theBenchmark.p
% 12.25/2.03  
% 12.25/2.03  fof(f13,axiom,(
% 12.25/2.03    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 12.25/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.25/2.03  
% 12.25/2.03  fof(f41,plain,(
% 12.25/2.03    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 12.25/2.03    inference(nnf_transformation,[],[f13])).
% 12.25/2.03  
% 12.25/2.03  fof(f42,plain,(
% 12.25/2.03    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 12.25/2.03    inference(flattening,[],[f41])).
% 12.25/2.03  
% 12.25/2.03  fof(f79,plain,(
% 12.25/2.03    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 12.25/2.03    inference(cnf_transformation,[],[f42])).
% 12.25/2.03  
% 12.25/2.03  fof(f11,axiom,(
% 12.25/2.03    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 12.25/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.25/2.03  
% 12.25/2.03  fof(f73,plain,(
% 12.25/2.03    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 12.25/2.03    inference(cnf_transformation,[],[f11])).
% 12.25/2.03  
% 12.25/2.03  fof(f97,plain,(
% 12.25/2.03    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 12.25/2.03    inference(definition_unfolding,[],[f79,f73])).
% 12.25/2.03  
% 12.25/2.03  fof(f114,plain,(
% 12.25/2.03    ( ! [X2,X1] : (k4_xboole_0(k2_tarski(X1,X1),X2) = k2_tarski(X1,X1) | r2_hidden(X1,X2)) )),
% 12.25/2.03    inference(equality_resolution,[],[f97])).
% 12.25/2.03  
% 12.25/2.03  fof(f10,axiom,(
% 12.25/2.03    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 12.25/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.25/2.03  
% 12.25/2.03  fof(f72,plain,(
% 12.25/2.03    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 12.25/2.03    inference(cnf_transformation,[],[f10])).
% 12.25/2.03  
% 12.25/2.03  fof(f84,plain,(
% 12.25/2.03    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X0,X1)) )),
% 12.25/2.03    inference(definition_unfolding,[],[f72,f73,f73])).
% 12.25/2.03  
% 12.25/2.03  fof(f5,axiom,(
% 12.25/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 12.25/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.25/2.03  
% 12.25/2.03  fof(f64,plain,(
% 12.25/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 12.25/2.03    inference(cnf_transformation,[],[f5])).
% 12.25/2.03  
% 12.25/2.03  fof(f1,axiom,(
% 12.25/2.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.25/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.25/2.03  
% 12.25/2.03  fof(f45,plain,(
% 12.25/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.25/2.03    inference(cnf_transformation,[],[f1])).
% 12.25/2.03  
% 12.25/2.03  fof(f15,conjecture,(
% 12.25/2.03    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 12.25/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.25/2.03  
% 12.25/2.03  fof(f16,negated_conjecture,(
% 12.25/2.03    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 12.25/2.03    inference(negated_conjecture,[],[f15])).
% 12.25/2.03  
% 12.25/2.03  fof(f19,plain,(
% 12.25/2.03    ? [X0,X1,X2] : ((k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 12.25/2.03    inference(ennf_transformation,[],[f16])).
% 12.25/2.03  
% 12.25/2.03  fof(f20,plain,(
% 12.25/2.03    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 12.25/2.03    inference(flattening,[],[f19])).
% 12.25/2.03  
% 12.25/2.03  fof(f43,plain,(
% 12.25/2.03    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k3_xboole_0(k2_tarski(sK4,sK6),sK5) != k1_tarski(sK4) & (sK4 = sK6 | ~r2_hidden(sK6,sK5)) & r2_hidden(sK4,sK5))),
% 12.25/2.03    introduced(choice_axiom,[])).
% 12.25/2.03  
% 12.25/2.03  fof(f44,plain,(
% 12.25/2.03    k3_xboole_0(k2_tarski(sK4,sK6),sK5) != k1_tarski(sK4) & (sK4 = sK6 | ~r2_hidden(sK6,sK5)) & r2_hidden(sK4,sK5)),
% 12.25/2.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f43])).
% 12.25/2.03  
% 12.25/2.03  fof(f81,plain,(
% 12.25/2.03    r2_hidden(sK4,sK5)),
% 12.25/2.03    inference(cnf_transformation,[],[f44])).
% 12.25/2.03  
% 12.25/2.03  fof(f78,plain,(
% 12.25/2.03    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 12.25/2.03    inference(cnf_transformation,[],[f42])).
% 12.25/2.03  
% 12.25/2.03  fof(f98,plain,(
% 12.25/2.03    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 12.25/2.03    inference(definition_unfolding,[],[f78,f73])).
% 12.25/2.03  
% 12.25/2.03  fof(f82,plain,(
% 12.25/2.03    sK4 = sK6 | ~r2_hidden(sK6,sK5)),
% 12.25/2.03    inference(cnf_transformation,[],[f44])).
% 12.25/2.03  
% 12.25/2.03  fof(f83,plain,(
% 12.25/2.03    k3_xboole_0(k2_tarski(sK4,sK6),sK5) != k1_tarski(sK4)),
% 12.25/2.03    inference(cnf_transformation,[],[f44])).
% 12.25/2.03  
% 12.25/2.03  fof(f7,axiom,(
% 12.25/2.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.25/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.25/2.03  
% 12.25/2.03  fof(f66,plain,(
% 12.25/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.25/2.03    inference(cnf_transformation,[],[f7])).
% 12.25/2.03  
% 12.25/2.03  fof(f101,plain,(
% 12.25/2.03    k4_xboole_0(k2_tarski(sK4,sK6),k4_xboole_0(k2_tarski(sK4,sK6),sK5)) != k2_tarski(sK4,sK4)),
% 12.25/2.03    inference(definition_unfolding,[],[f83,f66,f73])).
% 12.25/2.03  
% 12.25/2.03  fof(f4,axiom,(
% 12.25/2.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 12.25/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.25/2.03  
% 12.25/2.03  fof(f31,plain,(
% 12.25/2.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.25/2.03    inference(nnf_transformation,[],[f4])).
% 12.25/2.03  
% 12.25/2.03  fof(f32,plain,(
% 12.25/2.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.25/2.03    inference(flattening,[],[f31])).
% 12.25/2.03  
% 12.25/2.03  fof(f33,plain,(
% 12.25/2.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.25/2.03    inference(rectify,[],[f32])).
% 12.25/2.03  
% 12.25/2.03  fof(f34,plain,(
% 12.25/2.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 12.25/2.03    introduced(choice_axiom,[])).
% 12.25/2.03  
% 12.25/2.03  fof(f35,plain,(
% 12.25/2.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.25/2.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 12.25/2.03  
% 12.25/2.03  fof(f59,plain,(
% 12.25/2.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 12.25/2.03    inference(cnf_transformation,[],[f35])).
% 12.25/2.03  
% 12.25/2.03  fof(f109,plain,(
% 12.25/2.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 12.25/2.03    inference(equality_resolution,[],[f59])).
% 12.25/2.03  
% 12.25/2.03  fof(f14,axiom,(
% 12.25/2.03    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 12.25/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.25/2.03  
% 12.25/2.03  fof(f17,plain,(
% 12.25/2.03    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 12.25/2.03    inference(ennf_transformation,[],[f14])).
% 12.25/2.03  
% 12.25/2.03  fof(f18,plain,(
% 12.25/2.03    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 12.25/2.03    inference(flattening,[],[f17])).
% 12.25/2.03  
% 12.25/2.03  fof(f80,plain,(
% 12.25/2.03    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 12.25/2.03    inference(cnf_transformation,[],[f18])).
% 12.25/2.03  
% 12.25/2.03  cnf(c_29,plain,
% 12.25/2.03      ( r2_hidden(X0,X1)
% 12.25/2.03      | k4_xboole_0(k2_tarski(X0,X0),X1) = k2_tarski(X0,X0) ),
% 12.25/2.03      inference(cnf_transformation,[],[f114]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_3820,plain,
% 12.25/2.03      ( r2_hidden(X0,k4_xboole_0(X1,X2))
% 12.25/2.03      | k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(X1,X2)) = k2_tarski(X0,X0) ),
% 12.25/2.03      inference(instantiation,[status(thm)],[c_29]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_16446,plain,
% 12.25/2.03      ( r2_hidden(sK4,k4_xboole_0(sK5,X0))
% 12.25/2.03      | k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK5,X0)) = k2_tarski(sK4,sK4) ),
% 12.25/2.03      inference(instantiation,[status(thm)],[c_3820]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_64107,plain,
% 12.25/2.03      ( r2_hidden(sK4,k4_xboole_0(sK5,sK5))
% 12.25/2.03      | k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK5,sK5)) = k2_tarski(sK4,sK4) ),
% 12.25/2.03      inference(instantiation,[status(thm)],[c_16446]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_0,plain,
% 12.25/2.03      ( k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X0,X1) ),
% 12.25/2.03      inference(cnf_transformation,[],[f84]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_20,plain,
% 12.25/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 12.25/2.03      inference(cnf_transformation,[],[f64]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1669,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X1,X1)) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_0,c_20]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1,plain,
% 12.25/2.03      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 12.25/2.03      inference(cnf_transformation,[],[f45]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1670,plain,
% 12.25/2.03      ( k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X1,X0) ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_2173,plain,
% 12.25/2.03      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_1670,c_0]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_36,negated_conjecture,
% 12.25/2.03      ( r2_hidden(sK4,sK5) ),
% 12.25/2.03      inference(cnf_transformation,[],[f81]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1294,plain,
% 12.25/2.03      ( r2_hidden(sK4,sK5) = iProver_top ),
% 12.25/2.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_30,plain,
% 12.25/2.03      ( ~ r2_hidden(X0,X1)
% 12.25/2.03      | r2_hidden(X2,X1)
% 12.25/2.03      | k4_xboole_0(k2_tarski(X2,X0),X1) = k2_tarski(X2,X2) ),
% 12.25/2.03      inference(cnf_transformation,[],[f98]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1299,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X0)
% 12.25/2.03      | r2_hidden(X1,X2) != iProver_top
% 12.25/2.03      | r2_hidden(X0,X2) = iProver_top ),
% 12.25/2.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_5383,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(X0,sK4),sK5) = k2_tarski(X0,X0)
% 12.25/2.03      | r2_hidden(X0,sK5) = iProver_top ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_1294,c_1299]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_35,negated_conjecture,
% 12.25/2.03      ( ~ r2_hidden(sK6,sK5) | sK4 = sK6 ),
% 12.25/2.03      inference(cnf_transformation,[],[f82]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1295,plain,
% 12.25/2.03      ( sK4 = sK6 | r2_hidden(sK6,sK5) != iProver_top ),
% 12.25/2.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_6517,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(sK6,sK4),sK5) = k2_tarski(sK6,sK6)
% 12.25/2.03      | sK6 = sK4 ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_5383,c_1295]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_6543,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(sK4,sK6),sK5) = k2_tarski(sK6,sK6)
% 12.25/2.03      | sK6 = sK4 ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_2173,c_6517]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_34,negated_conjecture,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(sK4,sK6),k4_xboole_0(k2_tarski(sK4,sK6),sK5)) != k2_tarski(sK4,sK4) ),
% 12.25/2.03      inference(cnf_transformation,[],[f101]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_7057,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(sK4,sK6),k2_tarski(sK6,sK6)) != k2_tarski(sK4,sK4)
% 12.25/2.03      | sK6 = sK4 ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_6543,c_34]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_36372,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK6)) != k2_tarski(sK4,sK4)
% 12.25/2.03      | sK6 = sK4 ),
% 12.25/2.03      inference(demodulation,[status(thm)],[c_1669,c_7057]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_37,plain,
% 12.25/2.03      ( r2_hidden(sK4,sK5) = iProver_top ),
% 12.25/2.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1301,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(X0,X0),X1) = k2_tarski(X0,X0)
% 12.25/2.03      | r2_hidden(X0,X1) = iProver_top ),
% 12.25/2.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_18,plain,
% 12.25/2.03      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 12.25/2.03      inference(cnf_transformation,[],[f109]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1307,plain,
% 12.25/2.03      ( r2_hidden(X0,X1) != iProver_top
% 12.25/2.03      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 12.25/2.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_18459,plain,
% 12.25/2.03      ( sK6 = sK4
% 12.25/2.03      | r2_hidden(X0,k2_tarski(sK6,sK6)) != iProver_top
% 12.25/2.03      | r2_hidden(X0,sK5) != iProver_top ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_6517,c_1307]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_19181,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(sK6,sK6)) = k2_tarski(X0,X0)
% 12.25/2.03      | sK6 = sK4
% 12.25/2.03      | r2_hidden(X0,sK5) != iProver_top ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_1301,c_18459]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_19208,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK6)) = k2_tarski(sK4,sK4)
% 12.25/2.03      | sK6 = sK4
% 12.25/2.03      | r2_hidden(sK4,sK5) != iProver_top ),
% 12.25/2.03      inference(instantiation,[status(thm)],[c_19181]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_36659,plain,
% 12.25/2.03      ( sK6 = sK4 ),
% 12.25/2.03      inference(global_propositional_subsumption,
% 12.25/2.03                [status(thm)],
% 12.25/2.03                [c_36372,c_37,c_19208]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_36673,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(k2_tarski(sK4,sK4),sK5)) != k2_tarski(sK4,sK4) ),
% 12.25/2.03      inference(demodulation,[status(thm)],[c_36659,c_34]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_33,plain,
% 12.25/2.03      ( ~ r2_hidden(X0,X1)
% 12.25/2.03      | ~ r2_hidden(X2,X1)
% 12.25/2.03      | k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ),
% 12.25/2.03      inference(cnf_transformation,[],[f80]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1296,plain,
% 12.25/2.03      ( k2_xboole_0(k2_tarski(X0,X1),X2) = X2
% 12.25/2.03      | r2_hidden(X0,X2) != iProver_top
% 12.25/2.03      | r2_hidden(X1,X2) != iProver_top ),
% 12.25/2.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1872,plain,
% 12.25/2.03      ( k2_xboole_0(k2_tarski(sK4,X0),sK5) = sK5
% 12.25/2.03      | r2_hidden(X0,sK5) != iProver_top ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_1294,c_1296]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_2506,plain,
% 12.25/2.03      ( k2_xboole_0(k2_tarski(sK4,sK4),sK5) = sK5 ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_1294,c_1872]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_2549,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(sK4,sK4),sK5) = k4_xboole_0(sK5,sK5) ),
% 12.25/2.03      inference(superposition,[status(thm)],[c_2506,c_20]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_36675,plain,
% 12.25/2.03      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK5,sK5)) != k2_tarski(sK4,sK4) ),
% 12.25/2.03      inference(light_normalisation,[status(thm)],[c_36673,c_2549]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_1568,plain,
% 12.25/2.03      ( ~ r2_hidden(sK4,k4_xboole_0(X0,sK5)) | ~ r2_hidden(sK4,sK5) ),
% 12.25/2.03      inference(instantiation,[status(thm)],[c_18]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(c_6485,plain,
% 12.25/2.03      ( ~ r2_hidden(sK4,k4_xboole_0(sK5,sK5)) | ~ r2_hidden(sK4,sK5) ),
% 12.25/2.03      inference(instantiation,[status(thm)],[c_1568]) ).
% 12.25/2.03  
% 12.25/2.03  cnf(contradiction,plain,
% 12.25/2.03      ( $false ),
% 12.25/2.03      inference(minisat,[status(thm)],[c_64107,c_36675,c_6485,c_36]) ).
% 12.25/2.03  
% 12.25/2.03  
% 12.25/2.03  % SZS output end CNFRefutation for theBenchmark.p
% 12.25/2.03  
% 12.25/2.03  ------                               Statistics
% 12.25/2.03  
% 12.25/2.03  ------ General
% 12.25/2.03  
% 12.25/2.03  abstr_ref_over_cycles:                  0
% 12.25/2.03  abstr_ref_under_cycles:                 0
% 12.25/2.03  gc_basic_clause_elim:                   0
% 12.25/2.03  forced_gc_time:                         0
% 12.25/2.03  parsing_time:                           0.009
% 12.25/2.03  unif_index_cands_time:                  0.
% 12.25/2.03  unif_index_add_time:                    0.
% 12.25/2.03  orderings_time:                         0.
% 12.25/2.03  out_proof_time:                         0.011
% 12.25/2.03  total_time:                             1.499
% 12.25/2.03  num_of_symbols:                         42
% 12.25/2.03  num_of_terms:                           60807
% 12.25/2.03  
% 12.25/2.03  ------ Preprocessing
% 12.25/2.03  
% 12.25/2.03  num_of_splits:                          0
% 12.25/2.03  num_of_split_atoms:                     0
% 12.25/2.03  num_of_reused_defs:                     0
% 12.25/2.03  num_eq_ax_congr_red:                    33
% 12.25/2.03  num_of_sem_filtered_clauses:            1
% 12.25/2.03  num_of_subtypes:                        0
% 12.25/2.03  monotx_restored_types:                  0
% 12.25/2.03  sat_num_of_epr_types:                   0
% 12.25/2.03  sat_num_of_non_cyclic_types:            0
% 12.25/2.03  sat_guarded_non_collapsed_types:        0
% 12.25/2.03  num_pure_diseq_elim:                    0
% 12.25/2.03  simp_replaced_by:                       0
% 12.25/2.03  res_preprocessed:                       157
% 12.25/2.03  prep_upred:                             0
% 12.25/2.03  prep_unflattend:                        0
% 12.25/2.03  smt_new_axioms:                         0
% 12.25/2.03  pred_elim_cands:                        1
% 12.25/2.03  pred_elim:                              0
% 12.25/2.03  pred_elim_cl:                           0
% 12.25/2.03  pred_elim_cycles:                       2
% 12.25/2.03  merged_defs:                            8
% 12.25/2.03  merged_defs_ncl:                        0
% 12.25/2.03  bin_hyper_res:                          8
% 12.25/2.03  prep_cycles:                            4
% 12.25/2.03  pred_elim_time:                         0.001
% 12.25/2.03  splitting_time:                         0.
% 12.25/2.03  sem_filter_time:                        0.
% 12.25/2.03  monotx_time:                            0.
% 12.25/2.03  subtype_inf_time:                       0.
% 12.25/2.03  
% 12.25/2.03  ------ Problem properties
% 12.25/2.03  
% 12.25/2.03  clauses:                                36
% 12.25/2.03  conjectures:                            3
% 12.25/2.03  epr:                                    2
% 12.25/2.03  horn:                                   24
% 12.25/2.03  ground:                                 3
% 12.25/2.03  unary:                                  8
% 12.25/2.03  binary:                                 11
% 12.25/2.03  lits:                                   84
% 12.25/2.03  lits_eq:                                28
% 12.25/2.03  fd_pure:                                0
% 12.25/2.03  fd_pseudo:                              0
% 12.25/2.03  fd_cond:                                0
% 12.25/2.03  fd_pseudo_cond:                         12
% 12.25/2.03  ac_symbols:                             0
% 12.25/2.03  
% 12.25/2.03  ------ Propositional Solver
% 12.25/2.03  
% 12.25/2.03  prop_solver_calls:                      30
% 12.25/2.03  prop_fast_solver_calls:                 1203
% 12.25/2.03  smt_solver_calls:                       0
% 12.25/2.03  smt_fast_solver_calls:                  0
% 12.25/2.03  prop_num_of_clauses:                    17851
% 12.25/2.03  prop_preprocess_simplified:             25079
% 12.25/2.03  prop_fo_subsumed:                       8
% 12.25/2.03  prop_solver_time:                       0.
% 12.25/2.03  smt_solver_time:                        0.
% 12.25/2.03  smt_fast_solver_time:                   0.
% 12.25/2.03  prop_fast_solver_time:                  0.
% 12.25/2.03  prop_unsat_core_time:                   0.001
% 12.25/2.03  
% 12.25/2.03  ------ QBF
% 12.25/2.03  
% 12.25/2.03  qbf_q_res:                              0
% 12.25/2.03  qbf_num_tautologies:                    0
% 12.25/2.03  qbf_prep_cycles:                        0
% 12.25/2.03  
% 12.25/2.03  ------ BMC1
% 12.25/2.03  
% 12.25/2.03  bmc1_current_bound:                     -1
% 12.25/2.03  bmc1_last_solved_bound:                 -1
% 12.25/2.03  bmc1_unsat_core_size:                   -1
% 12.25/2.03  bmc1_unsat_core_parents_size:           -1
% 12.25/2.03  bmc1_merge_next_fun:                    0
% 12.25/2.03  bmc1_unsat_core_clauses_time:           0.
% 12.25/2.03  
% 12.25/2.03  ------ Instantiation
% 12.25/2.03  
% 12.25/2.03  inst_num_of_clauses:                    3198
% 12.25/2.03  inst_num_in_passive:                    824
% 12.25/2.03  inst_num_in_active:                     808
% 12.25/2.03  inst_num_in_unprocessed:                1569
% 12.25/2.03  inst_num_of_loops:                      1198
% 12.25/2.03  inst_num_of_learning_restarts:          0
% 12.25/2.03  inst_num_moves_active_passive:          388
% 12.25/2.03  inst_lit_activity:                      0
% 12.25/2.03  inst_lit_activity_moves:                1
% 12.25/2.03  inst_num_tautologies:                   0
% 12.25/2.03  inst_num_prop_implied:                  0
% 12.25/2.03  inst_num_existing_simplified:           0
% 12.25/2.03  inst_num_eq_res_simplified:             0
% 12.25/2.03  inst_num_child_elim:                    0
% 12.25/2.03  inst_num_of_dismatching_blockings:      4024
% 12.25/2.03  inst_num_of_non_proper_insts:           3514
% 12.25/2.03  inst_num_of_duplicates:                 0
% 12.25/2.03  inst_inst_num_from_inst_to_res:         0
% 12.25/2.03  inst_dismatching_checking_time:         0.
% 12.25/2.03  
% 12.25/2.03  ------ Resolution
% 12.25/2.03  
% 12.25/2.03  res_num_of_clauses:                     0
% 12.25/2.03  res_num_in_passive:                     0
% 12.25/2.03  res_num_in_active:                      0
% 12.25/2.03  res_num_of_loops:                       161
% 12.25/2.03  res_forward_subset_subsumed:            192
% 12.25/2.03  res_backward_subset_subsumed:           10
% 12.25/2.03  res_forward_subsumed:                   0
% 12.25/2.03  res_backward_subsumed:                  0
% 12.25/2.03  res_forward_subsumption_resolution:     0
% 12.25/2.03  res_backward_subsumption_resolution:    0
% 12.25/2.03  res_clause_to_clause_subsumption:       57773
% 12.25/2.03  res_orphan_elimination:                 0
% 12.25/2.03  res_tautology_del:                      190
% 12.25/2.03  res_num_eq_res_simplified:              0
% 12.25/2.03  res_num_sel_changes:                    0
% 12.25/2.03  res_moves_from_active_to_pass:          0
% 12.25/2.03  
% 12.25/2.03  ------ Superposition
% 12.25/2.03  
% 12.25/2.03  sup_time_total:                         0.
% 12.25/2.03  sup_time_generating:                    0.
% 12.25/2.03  sup_time_sim_full:                      0.
% 12.25/2.03  sup_time_sim_immed:                     0.
% 12.25/2.03  
% 12.25/2.03  sup_num_of_clauses:                     4087
% 12.25/2.03  sup_num_in_active:                      206
% 12.25/2.03  sup_num_in_passive:                     3881
% 12.25/2.03  sup_num_of_loops:                       238
% 12.25/2.03  sup_fw_superposition:                   5901
% 12.25/2.03  sup_bw_superposition:                   4986
% 12.25/2.03  sup_immediate_simplified:               3434
% 12.25/2.03  sup_given_eliminated:                   1
% 12.25/2.03  comparisons_done:                       0
% 12.25/2.03  comparisons_avoided:                    182
% 12.25/2.03  
% 12.25/2.03  ------ Simplifications
% 12.25/2.03  
% 12.25/2.03  
% 12.25/2.03  sim_fw_subset_subsumed:                 367
% 12.25/2.03  sim_bw_subset_subsumed:                 39
% 12.25/2.03  sim_fw_subsumed:                        642
% 12.25/2.03  sim_bw_subsumed:                        107
% 12.25/2.03  sim_fw_subsumption_res:                 3
% 12.25/2.03  sim_bw_subsumption_res:                 1
% 12.25/2.03  sim_tautology_del:                      59
% 12.25/2.03  sim_eq_tautology_del:                   432
% 12.25/2.03  sim_eq_res_simp:                        9
% 12.25/2.03  sim_fw_demodulated:                     1427
% 12.25/2.03  sim_bw_demodulated:                     118
% 12.25/2.03  sim_light_normalised:                   1134
% 12.25/2.03  sim_joinable_taut:                      0
% 12.25/2.03  sim_joinable_simp:                      0
% 12.25/2.03  sim_ac_normalised:                      0
% 12.25/2.03  sim_smt_subsumption:                    0
% 12.25/2.03  
%------------------------------------------------------------------------------
