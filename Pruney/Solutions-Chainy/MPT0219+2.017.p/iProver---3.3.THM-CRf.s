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
% DateTime   : Thu Dec  3 11:29:12 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 118 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  232 ( 363 expanded)
%              Number of equality atoms :  175 ( 268 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f51,f36,f53,f53])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f31])).

fof(f60,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) = k2_tarski(sK2,sK2) ),
    inference(definition_unfolding,[],[f60,f36,f53,f53,f53])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f64])).

fof(f84,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f85,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f84])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f93,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f91,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f80])).

fof(f92,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f91])).

fof(f61,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) = k2_tarski(sK2,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1752,plain,
    ( k2_tarski(sK2,sK3) = k2_tarski(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1,c_21])).

cnf(c_18,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_10,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_889,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4608,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_889])).

cnf(c_4612,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1752,c_4608])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1053,plain,
    ( ~ r2_hidden(sK3,k2_tarski(X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1054,plain,
    ( sK3 = X0
    | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_1056,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_688,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1005,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_1006,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_28,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_20,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4612,c_1056,c_1006,c_28,c_25,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:49:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 1.93/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.00  
% 1.93/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.93/1.00  
% 1.93/1.00  ------  iProver source info
% 1.93/1.00  
% 1.93/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.93/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.93/1.00  git: non_committed_changes: false
% 1.93/1.00  git: last_make_outside_of_git: false
% 1.93/1.00  
% 1.93/1.00  ------ 
% 1.93/1.00  
% 1.93/1.00  ------ Input Options
% 1.93/1.00  
% 1.93/1.00  --out_options                           all
% 1.93/1.00  --tptp_safe_out                         true
% 1.93/1.00  --problem_path                          ""
% 1.93/1.00  --include_path                          ""
% 1.93/1.00  --clausifier                            res/vclausify_rel
% 1.93/1.00  --clausifier_options                    --mode clausify
% 1.93/1.00  --stdin                                 false
% 1.93/1.00  --stats_out                             all
% 1.93/1.00  
% 1.93/1.00  ------ General Options
% 1.93/1.00  
% 1.93/1.00  --fof                                   false
% 1.93/1.00  --time_out_real                         305.
% 1.93/1.00  --time_out_virtual                      -1.
% 1.93/1.00  --symbol_type_check                     false
% 1.93/1.00  --clausify_out                          false
% 1.93/1.00  --sig_cnt_out                           false
% 1.93/1.00  --trig_cnt_out                          false
% 1.93/1.00  --trig_cnt_out_tolerance                1.
% 1.93/1.00  --trig_cnt_out_sk_spl                   false
% 1.93/1.00  --abstr_cl_out                          false
% 1.93/1.00  
% 1.93/1.00  ------ Global Options
% 1.93/1.00  
% 1.93/1.00  --schedule                              default
% 1.93/1.00  --add_important_lit                     false
% 1.93/1.00  --prop_solver_per_cl                    1000
% 1.93/1.00  --min_unsat_core                        false
% 1.93/1.00  --soft_assumptions                      false
% 1.93/1.00  --soft_lemma_size                       3
% 1.93/1.00  --prop_impl_unit_size                   0
% 1.93/1.00  --prop_impl_unit                        []
% 1.93/1.00  --share_sel_clauses                     true
% 1.93/1.00  --reset_solvers                         false
% 1.93/1.00  --bc_imp_inh                            [conj_cone]
% 1.93/1.00  --conj_cone_tolerance                   3.
% 1.93/1.00  --extra_neg_conj                        none
% 1.93/1.00  --large_theory_mode                     true
% 1.93/1.00  --prolific_symb_bound                   200
% 1.93/1.00  --lt_threshold                          2000
% 1.93/1.00  --clause_weak_htbl                      true
% 1.93/1.00  --gc_record_bc_elim                     false
% 1.93/1.00  
% 1.93/1.00  ------ Preprocessing Options
% 1.93/1.00  
% 1.93/1.00  --preprocessing_flag                    true
% 1.93/1.00  --time_out_prep_mult                    0.1
% 1.93/1.00  --splitting_mode                        input
% 1.93/1.00  --splitting_grd                         true
% 1.93/1.00  --splitting_cvd                         false
% 1.93/1.00  --splitting_cvd_svl                     false
% 1.93/1.00  --splitting_nvd                         32
% 1.93/1.00  --sub_typing                            true
% 1.93/1.00  --prep_gs_sim                           true
% 1.93/1.00  --prep_unflatten                        true
% 1.93/1.00  --prep_res_sim                          true
% 1.93/1.00  --prep_upred                            true
% 1.93/1.00  --prep_sem_filter                       exhaustive
% 1.93/1.00  --prep_sem_filter_out                   false
% 1.93/1.00  --pred_elim                             true
% 1.93/1.00  --res_sim_input                         true
% 1.93/1.00  --eq_ax_congr_red                       true
% 1.93/1.00  --pure_diseq_elim                       true
% 1.93/1.00  --brand_transform                       false
% 1.93/1.00  --non_eq_to_eq                          false
% 1.93/1.00  --prep_def_merge                        true
% 1.93/1.00  --prep_def_merge_prop_impl              false
% 1.93/1.00  --prep_def_merge_mbd                    true
% 1.93/1.00  --prep_def_merge_tr_red                 false
% 1.93/1.00  --prep_def_merge_tr_cl                  false
% 1.93/1.00  --smt_preprocessing                     true
% 1.93/1.00  --smt_ac_axioms                         fast
% 1.93/1.00  --preprocessed_out                      false
% 1.93/1.00  --preprocessed_stats                    false
% 1.93/1.00  
% 1.93/1.00  ------ Abstraction refinement Options
% 1.93/1.00  
% 1.93/1.00  --abstr_ref                             []
% 1.93/1.00  --abstr_ref_prep                        false
% 1.93/1.00  --abstr_ref_until_sat                   false
% 1.93/1.00  --abstr_ref_sig_restrict                funpre
% 1.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/1.00  --abstr_ref_under                       []
% 1.93/1.00  
% 1.93/1.00  ------ SAT Options
% 1.93/1.00  
% 1.93/1.00  --sat_mode                              false
% 1.93/1.00  --sat_fm_restart_options                ""
% 1.93/1.00  --sat_gr_def                            false
% 1.93/1.00  --sat_epr_types                         true
% 1.93/1.00  --sat_non_cyclic_types                  false
% 1.93/1.00  --sat_finite_models                     false
% 1.93/1.00  --sat_fm_lemmas                         false
% 1.93/1.00  --sat_fm_prep                           false
% 1.93/1.00  --sat_fm_uc_incr                        true
% 1.93/1.00  --sat_out_model                         small
% 1.93/1.00  --sat_out_clauses                       false
% 1.93/1.00  
% 1.93/1.00  ------ QBF Options
% 1.93/1.00  
% 1.93/1.00  --qbf_mode                              false
% 1.93/1.00  --qbf_elim_univ                         false
% 1.93/1.00  --qbf_dom_inst                          none
% 1.93/1.00  --qbf_dom_pre_inst                      false
% 1.93/1.00  --qbf_sk_in                             false
% 1.93/1.00  --qbf_pred_elim                         true
% 1.93/1.00  --qbf_split                             512
% 1.93/1.00  
% 1.93/1.00  ------ BMC1 Options
% 1.93/1.00  
% 1.93/1.00  --bmc1_incremental                      false
% 1.93/1.00  --bmc1_axioms                           reachable_all
% 1.93/1.00  --bmc1_min_bound                        0
% 1.93/1.00  --bmc1_max_bound                        -1
% 1.93/1.00  --bmc1_max_bound_default                -1
% 1.93/1.00  --bmc1_symbol_reachability              true
% 1.93/1.00  --bmc1_property_lemmas                  false
% 1.93/1.00  --bmc1_k_induction                      false
% 1.93/1.00  --bmc1_non_equiv_states                 false
% 1.93/1.00  --bmc1_deadlock                         false
% 1.93/1.00  --bmc1_ucm                              false
% 1.93/1.00  --bmc1_add_unsat_core                   none
% 1.93/1.00  --bmc1_unsat_core_children              false
% 1.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/1.00  --bmc1_out_stat                         full
% 1.93/1.00  --bmc1_ground_init                      false
% 1.93/1.00  --bmc1_pre_inst_next_state              false
% 1.93/1.00  --bmc1_pre_inst_state                   false
% 1.93/1.00  --bmc1_pre_inst_reach_state             false
% 1.93/1.00  --bmc1_out_unsat_core                   false
% 1.93/1.00  --bmc1_aig_witness_out                  false
% 1.93/1.00  --bmc1_verbose                          false
% 1.93/1.00  --bmc1_dump_clauses_tptp                false
% 1.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.93/1.00  --bmc1_dump_file                        -
% 1.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.93/1.00  --bmc1_ucm_extend_mode                  1
% 1.93/1.00  --bmc1_ucm_init_mode                    2
% 1.93/1.00  --bmc1_ucm_cone_mode                    none
% 1.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.93/1.00  --bmc1_ucm_relax_model                  4
% 1.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/1.00  --bmc1_ucm_layered_model                none
% 1.93/1.00  --bmc1_ucm_max_lemma_size               10
% 1.93/1.00  
% 1.93/1.00  ------ AIG Options
% 1.93/1.00  
% 1.93/1.00  --aig_mode                              false
% 1.93/1.00  
% 1.93/1.00  ------ Instantiation Options
% 1.93/1.00  
% 1.93/1.00  --instantiation_flag                    true
% 1.93/1.00  --inst_sos_flag                         false
% 1.93/1.00  --inst_sos_phase                        true
% 1.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/1.00  --inst_lit_sel_side                     num_symb
% 1.93/1.00  --inst_solver_per_active                1400
% 1.93/1.00  --inst_solver_calls_frac                1.
% 1.93/1.00  --inst_passive_queue_type               priority_queues
% 1.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/1.00  --inst_passive_queues_freq              [25;2]
% 1.93/1.00  --inst_dismatching                      true
% 1.93/1.00  --inst_eager_unprocessed_to_passive     true
% 1.93/1.00  --inst_prop_sim_given                   true
% 1.93/1.00  --inst_prop_sim_new                     false
% 1.93/1.00  --inst_subs_new                         false
% 1.93/1.00  --inst_eq_res_simp                      false
% 1.93/1.00  --inst_subs_given                       false
% 1.93/1.00  --inst_orphan_elimination               true
% 1.93/1.00  --inst_learning_loop_flag               true
% 1.93/1.00  --inst_learning_start                   3000
% 1.93/1.00  --inst_learning_factor                  2
% 1.93/1.00  --inst_start_prop_sim_after_learn       3
% 1.93/1.00  --inst_sel_renew                        solver
% 1.93/1.00  --inst_lit_activity_flag                true
% 1.93/1.00  --inst_restr_to_given                   false
% 1.93/1.00  --inst_activity_threshold               500
% 1.93/1.00  --inst_out_proof                        true
% 1.93/1.00  
% 1.93/1.00  ------ Resolution Options
% 1.93/1.00  
% 1.93/1.00  --resolution_flag                       true
% 1.93/1.00  --res_lit_sel                           adaptive
% 1.93/1.00  --res_lit_sel_side                      none
% 1.93/1.00  --res_ordering                          kbo
% 1.93/1.00  --res_to_prop_solver                    active
% 1.93/1.00  --res_prop_simpl_new                    false
% 1.93/1.00  --res_prop_simpl_given                  true
% 1.93/1.00  --res_passive_queue_type                priority_queues
% 1.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/1.00  --res_passive_queues_freq               [15;5]
% 1.93/1.00  --res_forward_subs                      full
% 1.93/1.00  --res_backward_subs                     full
% 1.93/1.00  --res_forward_subs_resolution           true
% 1.93/1.00  --res_backward_subs_resolution          true
% 1.93/1.00  --res_orphan_elimination                true
% 1.93/1.00  --res_time_limit                        2.
% 1.93/1.00  --res_out_proof                         true
% 1.93/1.00  
% 1.93/1.00  ------ Superposition Options
% 1.93/1.00  
% 1.93/1.00  --superposition_flag                    true
% 1.93/1.00  --sup_passive_queue_type                priority_queues
% 1.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.93/1.00  --demod_completeness_check              fast
% 1.93/1.00  --demod_use_ground                      true
% 1.93/1.00  --sup_to_prop_solver                    passive
% 1.93/1.00  --sup_prop_simpl_new                    true
% 1.93/1.00  --sup_prop_simpl_given                  true
% 1.93/1.00  --sup_fun_splitting                     false
% 1.93/1.00  --sup_smt_interval                      50000
% 1.93/1.00  
% 1.93/1.00  ------ Superposition Simplification Setup
% 1.93/1.00  
% 1.93/1.00  --sup_indices_passive                   []
% 1.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.00  --sup_full_bw                           [BwDemod]
% 1.93/1.00  --sup_immed_triv                        [TrivRules]
% 1.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.00  --sup_immed_bw_main                     []
% 1.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/1.00  
% 1.93/1.00  ------ Combination Options
% 1.93/1.00  
% 1.93/1.00  --comb_res_mult                         3
% 1.93/1.00  --comb_sup_mult                         2
% 1.93/1.00  --comb_inst_mult                        10
% 1.93/1.00  
% 1.93/1.00  ------ Debug Options
% 1.93/1.00  
% 1.93/1.00  --dbg_backtrace                         false
% 1.93/1.00  --dbg_dump_prop_clauses                 false
% 1.93/1.00  --dbg_dump_prop_clauses_file            -
% 1.93/1.00  --dbg_out_stat                          false
% 1.93/1.00  ------ Parsing...
% 1.93/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.93/1.00  
% 1.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.93/1.00  
% 1.93/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.93/1.00  
% 1.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.93/1.00  ------ Proving...
% 1.93/1.00  ------ Problem Properties 
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  clauses                                 22
% 1.93/1.00  conjectures                             2
% 1.93/1.00  EPR                                     1
% 1.93/1.00  Horn                                    19
% 1.93/1.00  unary                                   14
% 1.93/1.00  binary                                  1
% 1.93/1.00  lits                                    40
% 1.93/1.00  lits eq                                 28
% 1.93/1.00  fd_pure                                 0
% 1.93/1.00  fd_pseudo                               0
% 1.93/1.00  fd_cond                                 0
% 1.93/1.00  fd_pseudo_cond                          6
% 1.93/1.00  AC symbols                              0
% 1.93/1.00  
% 1.93/1.00  ------ Schedule dynamic 5 is on 
% 1.93/1.00  
% 1.93/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  ------ 
% 1.93/1.00  Current options:
% 1.93/1.00  ------ 
% 1.93/1.00  
% 1.93/1.00  ------ Input Options
% 1.93/1.00  
% 1.93/1.00  --out_options                           all
% 1.93/1.00  --tptp_safe_out                         true
% 1.93/1.00  --problem_path                          ""
% 1.93/1.00  --include_path                          ""
% 1.93/1.00  --clausifier                            res/vclausify_rel
% 1.93/1.00  --clausifier_options                    --mode clausify
% 1.93/1.00  --stdin                                 false
% 1.93/1.00  --stats_out                             all
% 1.93/1.00  
% 1.93/1.00  ------ General Options
% 1.93/1.00  
% 1.93/1.00  --fof                                   false
% 1.93/1.00  --time_out_real                         305.
% 1.93/1.00  --time_out_virtual                      -1.
% 1.93/1.00  --symbol_type_check                     false
% 1.93/1.00  --clausify_out                          false
% 1.93/1.00  --sig_cnt_out                           false
% 1.93/1.00  --trig_cnt_out                          false
% 1.93/1.00  --trig_cnt_out_tolerance                1.
% 1.93/1.00  --trig_cnt_out_sk_spl                   false
% 1.93/1.00  --abstr_cl_out                          false
% 1.93/1.00  
% 1.93/1.00  ------ Global Options
% 1.93/1.00  
% 1.93/1.00  --schedule                              default
% 1.93/1.00  --add_important_lit                     false
% 1.93/1.00  --prop_solver_per_cl                    1000
% 1.93/1.00  --min_unsat_core                        false
% 1.93/1.00  --soft_assumptions                      false
% 1.93/1.00  --soft_lemma_size                       3
% 1.93/1.00  --prop_impl_unit_size                   0
% 1.93/1.00  --prop_impl_unit                        []
% 1.93/1.00  --share_sel_clauses                     true
% 1.93/1.00  --reset_solvers                         false
% 1.93/1.00  --bc_imp_inh                            [conj_cone]
% 1.93/1.00  --conj_cone_tolerance                   3.
% 1.93/1.00  --extra_neg_conj                        none
% 1.93/1.00  --large_theory_mode                     true
% 1.93/1.00  --prolific_symb_bound                   200
% 1.93/1.00  --lt_threshold                          2000
% 1.93/1.00  --clause_weak_htbl                      true
% 1.93/1.00  --gc_record_bc_elim                     false
% 1.93/1.00  
% 1.93/1.00  ------ Preprocessing Options
% 1.93/1.00  
% 1.93/1.00  --preprocessing_flag                    true
% 1.93/1.00  --time_out_prep_mult                    0.1
% 1.93/1.00  --splitting_mode                        input
% 1.93/1.00  --splitting_grd                         true
% 1.93/1.00  --splitting_cvd                         false
% 1.93/1.00  --splitting_cvd_svl                     false
% 1.93/1.00  --splitting_nvd                         32
% 1.93/1.00  --sub_typing                            true
% 1.93/1.00  --prep_gs_sim                           true
% 1.93/1.00  --prep_unflatten                        true
% 1.93/1.00  --prep_res_sim                          true
% 1.93/1.00  --prep_upred                            true
% 1.93/1.00  --prep_sem_filter                       exhaustive
% 1.93/1.00  --prep_sem_filter_out                   false
% 1.93/1.00  --pred_elim                             true
% 1.93/1.00  --res_sim_input                         true
% 1.93/1.00  --eq_ax_congr_red                       true
% 1.93/1.00  --pure_diseq_elim                       true
% 1.93/1.00  --brand_transform                       false
% 1.93/1.00  --non_eq_to_eq                          false
% 1.93/1.00  --prep_def_merge                        true
% 1.93/1.00  --prep_def_merge_prop_impl              false
% 1.93/1.00  --prep_def_merge_mbd                    true
% 1.93/1.00  --prep_def_merge_tr_red                 false
% 1.93/1.00  --prep_def_merge_tr_cl                  false
% 1.93/1.00  --smt_preprocessing                     true
% 1.93/1.00  --smt_ac_axioms                         fast
% 1.93/1.00  --preprocessed_out                      false
% 1.93/1.00  --preprocessed_stats                    false
% 1.93/1.00  
% 1.93/1.00  ------ Abstraction refinement Options
% 1.93/1.00  
% 1.93/1.00  --abstr_ref                             []
% 1.93/1.00  --abstr_ref_prep                        false
% 1.93/1.00  --abstr_ref_until_sat                   false
% 1.93/1.00  --abstr_ref_sig_restrict                funpre
% 1.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/1.00  --abstr_ref_under                       []
% 1.93/1.00  
% 1.93/1.00  ------ SAT Options
% 1.93/1.00  
% 1.93/1.00  --sat_mode                              false
% 1.93/1.00  --sat_fm_restart_options                ""
% 1.93/1.00  --sat_gr_def                            false
% 1.93/1.00  --sat_epr_types                         true
% 1.93/1.00  --sat_non_cyclic_types                  false
% 1.93/1.00  --sat_finite_models                     false
% 1.93/1.00  --sat_fm_lemmas                         false
% 1.93/1.00  --sat_fm_prep                           false
% 1.93/1.00  --sat_fm_uc_incr                        true
% 1.93/1.00  --sat_out_model                         small
% 1.93/1.00  --sat_out_clauses                       false
% 1.93/1.00  
% 1.93/1.00  ------ QBF Options
% 1.93/1.00  
% 1.93/1.00  --qbf_mode                              false
% 1.93/1.00  --qbf_elim_univ                         false
% 1.93/1.00  --qbf_dom_inst                          none
% 1.93/1.00  --qbf_dom_pre_inst                      false
% 1.93/1.00  --qbf_sk_in                             false
% 1.93/1.00  --qbf_pred_elim                         true
% 1.93/1.00  --qbf_split                             512
% 1.93/1.00  
% 1.93/1.00  ------ BMC1 Options
% 1.93/1.00  
% 1.93/1.00  --bmc1_incremental                      false
% 1.93/1.00  --bmc1_axioms                           reachable_all
% 1.93/1.00  --bmc1_min_bound                        0
% 1.93/1.00  --bmc1_max_bound                        -1
% 1.93/1.00  --bmc1_max_bound_default                -1
% 1.93/1.00  --bmc1_symbol_reachability              true
% 1.93/1.00  --bmc1_property_lemmas                  false
% 1.93/1.00  --bmc1_k_induction                      false
% 1.93/1.00  --bmc1_non_equiv_states                 false
% 1.93/1.00  --bmc1_deadlock                         false
% 1.93/1.00  --bmc1_ucm                              false
% 1.93/1.00  --bmc1_add_unsat_core                   none
% 1.93/1.00  --bmc1_unsat_core_children              false
% 1.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/1.00  --bmc1_out_stat                         full
% 1.93/1.00  --bmc1_ground_init                      false
% 1.93/1.00  --bmc1_pre_inst_next_state              false
% 1.93/1.00  --bmc1_pre_inst_state                   false
% 1.93/1.00  --bmc1_pre_inst_reach_state             false
% 1.93/1.00  --bmc1_out_unsat_core                   false
% 1.93/1.00  --bmc1_aig_witness_out                  false
% 1.93/1.00  --bmc1_verbose                          false
% 1.93/1.00  --bmc1_dump_clauses_tptp                false
% 1.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.93/1.00  --bmc1_dump_file                        -
% 1.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.93/1.00  --bmc1_ucm_extend_mode                  1
% 1.93/1.00  --bmc1_ucm_init_mode                    2
% 1.93/1.00  --bmc1_ucm_cone_mode                    none
% 1.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.93/1.00  --bmc1_ucm_relax_model                  4
% 1.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/1.00  --bmc1_ucm_layered_model                none
% 1.93/1.00  --bmc1_ucm_max_lemma_size               10
% 1.93/1.00  
% 1.93/1.00  ------ AIG Options
% 1.93/1.00  
% 1.93/1.00  --aig_mode                              false
% 1.93/1.00  
% 1.93/1.00  ------ Instantiation Options
% 1.93/1.00  
% 1.93/1.00  --instantiation_flag                    true
% 1.93/1.00  --inst_sos_flag                         false
% 1.93/1.00  --inst_sos_phase                        true
% 1.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/1.00  --inst_lit_sel_side                     none
% 1.93/1.00  --inst_solver_per_active                1400
% 1.93/1.00  --inst_solver_calls_frac                1.
% 1.93/1.00  --inst_passive_queue_type               priority_queues
% 1.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/1.00  --inst_passive_queues_freq              [25;2]
% 1.93/1.00  --inst_dismatching                      true
% 1.93/1.00  --inst_eager_unprocessed_to_passive     true
% 1.93/1.00  --inst_prop_sim_given                   true
% 1.93/1.00  --inst_prop_sim_new                     false
% 1.93/1.00  --inst_subs_new                         false
% 1.93/1.00  --inst_eq_res_simp                      false
% 1.93/1.00  --inst_subs_given                       false
% 1.93/1.00  --inst_orphan_elimination               true
% 1.93/1.00  --inst_learning_loop_flag               true
% 1.93/1.00  --inst_learning_start                   3000
% 1.93/1.00  --inst_learning_factor                  2
% 1.93/1.00  --inst_start_prop_sim_after_learn       3
% 1.93/1.00  --inst_sel_renew                        solver
% 1.93/1.00  --inst_lit_activity_flag                true
% 1.93/1.00  --inst_restr_to_given                   false
% 1.93/1.00  --inst_activity_threshold               500
% 1.93/1.00  --inst_out_proof                        true
% 1.93/1.00  
% 1.93/1.00  ------ Resolution Options
% 1.93/1.00  
% 1.93/1.00  --resolution_flag                       false
% 1.93/1.00  --res_lit_sel                           adaptive
% 1.93/1.00  --res_lit_sel_side                      none
% 1.93/1.00  --res_ordering                          kbo
% 1.93/1.00  --res_to_prop_solver                    active
% 1.93/1.00  --res_prop_simpl_new                    false
% 1.93/1.00  --res_prop_simpl_given                  true
% 1.93/1.00  --res_passive_queue_type                priority_queues
% 1.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/1.00  --res_passive_queues_freq               [15;5]
% 1.93/1.00  --res_forward_subs                      full
% 1.93/1.00  --res_backward_subs                     full
% 1.93/1.00  --res_forward_subs_resolution           true
% 1.93/1.00  --res_backward_subs_resolution          true
% 1.93/1.00  --res_orphan_elimination                true
% 1.93/1.00  --res_time_limit                        2.
% 1.93/1.00  --res_out_proof                         true
% 1.93/1.00  
% 1.93/1.00  ------ Superposition Options
% 1.93/1.00  
% 1.93/1.00  --superposition_flag                    true
% 1.93/1.00  --sup_passive_queue_type                priority_queues
% 1.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.93/1.00  --demod_completeness_check              fast
% 1.93/1.00  --demod_use_ground                      true
% 1.93/1.00  --sup_to_prop_solver                    passive
% 1.93/1.00  --sup_prop_simpl_new                    true
% 1.93/1.00  --sup_prop_simpl_given                  true
% 1.93/1.00  --sup_fun_splitting                     false
% 1.93/1.00  --sup_smt_interval                      50000
% 1.93/1.00  
% 1.93/1.00  ------ Superposition Simplification Setup
% 1.93/1.00  
% 1.93/1.00  --sup_indices_passive                   []
% 1.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.00  --sup_full_bw                           [BwDemod]
% 1.93/1.00  --sup_immed_triv                        [TrivRules]
% 1.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.00  --sup_immed_bw_main                     []
% 1.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/1.00  
% 1.93/1.00  ------ Combination Options
% 1.93/1.00  
% 1.93/1.00  --comb_res_mult                         3
% 1.93/1.00  --comb_sup_mult                         2
% 1.93/1.00  --comb_inst_mult                        10
% 1.93/1.00  
% 1.93/1.00  ------ Debug Options
% 1.93/1.00  
% 1.93/1.00  --dbg_backtrace                         false
% 1.93/1.00  --dbg_dump_prop_clauses                 false
% 1.93/1.00  --dbg_dump_prop_clauses_file            -
% 1.93/1.00  --dbg_out_stat                          false
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  ------ Proving...
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  % SZS status Theorem for theBenchmark.p
% 1.93/1.00  
% 1.93/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.93/1.00  
% 1.93/1.00  fof(f9,axiom,(
% 1.93/1.00    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f51,plain,(
% 1.93/1.00    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f9])).
% 1.93/1.00  
% 1.93/1.00  fof(f4,axiom,(
% 1.93/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f36,plain,(
% 1.93/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.93/1.00    inference(cnf_transformation,[],[f4])).
% 1.93/1.00  
% 1.93/1.00  fof(f11,axiom,(
% 1.93/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f53,plain,(
% 1.93/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f11])).
% 1.93/1.00  
% 1.93/1.00  fof(f66,plain,(
% 1.93/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1)) )),
% 1.93/1.00    inference(definition_unfolding,[],[f51,f36,f53,f53])).
% 1.93/1.00  
% 1.93/1.00  fof(f18,conjecture,(
% 1.93/1.00    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f19,negated_conjecture,(
% 1.93/1.00    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 1.93/1.00    inference(negated_conjecture,[],[f18])).
% 1.93/1.00  
% 1.93/1.00  fof(f21,plain,(
% 1.93/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 1.93/1.00    inference(ennf_transformation,[],[f19])).
% 1.93/1.00  
% 1.93/1.00  fof(f31,plain,(
% 1.93/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 1.93/1.00    introduced(choice_axiom,[])).
% 1.93/1.00  
% 1.93/1.00  fof(f32,plain,(
% 1.93/1.00    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 1.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f31])).
% 1.93/1.00  
% 1.93/1.00  fof(f60,plain,(
% 1.93/1.00    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 1.93/1.00    inference(cnf_transformation,[],[f32])).
% 1.93/1.00  
% 1.93/1.00  fof(f83,plain,(
% 1.93/1.00    k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) = k2_tarski(sK2,sK2)),
% 1.93/1.00    inference(definition_unfolding,[],[f60,f36,f53,f53,f53])).
% 1.93/1.00  
% 1.93/1.00  fof(f12,axiom,(
% 1.93/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f54,plain,(
% 1.93/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f12])).
% 1.93/1.00  
% 1.93/1.00  fof(f13,axiom,(
% 1.93/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f55,plain,(
% 1.93/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f13])).
% 1.93/1.00  
% 1.93/1.00  fof(f14,axiom,(
% 1.93/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f56,plain,(
% 1.93/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f14])).
% 1.93/1.00  
% 1.93/1.00  fof(f15,axiom,(
% 1.93/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f57,plain,(
% 1.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f15])).
% 1.93/1.00  
% 1.93/1.00  fof(f16,axiom,(
% 1.93/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f58,plain,(
% 1.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f16])).
% 1.93/1.00  
% 1.93/1.00  fof(f62,plain,(
% 1.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.93/1.00    inference(definition_unfolding,[],[f57,f58])).
% 1.93/1.00  
% 1.93/1.00  fof(f63,plain,(
% 1.93/1.00    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.93/1.00    inference(definition_unfolding,[],[f56,f62])).
% 1.93/1.00  
% 1.93/1.00  fof(f64,plain,(
% 1.93/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.93/1.00    inference(definition_unfolding,[],[f55,f63])).
% 1.93/1.00  
% 1.93/1.00  fof(f82,plain,(
% 1.93/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.93/1.00    inference(definition_unfolding,[],[f54,f64])).
% 1.93/1.00  
% 1.93/1.00  fof(f7,axiom,(
% 1.93/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f20,plain,(
% 1.93/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.93/1.00    inference(ennf_transformation,[],[f7])).
% 1.93/1.00  
% 1.93/1.00  fof(f22,plain,(
% 1.93/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.93/1.00    inference(nnf_transformation,[],[f20])).
% 1.93/1.00  
% 1.93/1.00  fof(f23,plain,(
% 1.93/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.93/1.00    inference(flattening,[],[f22])).
% 1.93/1.00  
% 1.93/1.00  fof(f24,plain,(
% 1.93/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.93/1.00    inference(rectify,[],[f23])).
% 1.93/1.00  
% 1.93/1.00  fof(f25,plain,(
% 1.93/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 1.93/1.00    introduced(choice_axiom,[])).
% 1.93/1.00  
% 1.93/1.00  fof(f26,plain,(
% 1.93/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 1.93/1.00  
% 1.93/1.00  fof(f42,plain,(
% 1.93/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.93/1.00    inference(cnf_transformation,[],[f26])).
% 1.93/1.00  
% 1.93/1.00  fof(f74,plain,(
% 1.93/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.93/1.00    inference(definition_unfolding,[],[f42,f64])).
% 1.93/1.00  
% 1.93/1.00  fof(f84,plain,(
% 1.93/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 1.93/1.00    inference(equality_resolution,[],[f74])).
% 1.93/1.00  
% 1.93/1.00  fof(f85,plain,(
% 1.93/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 1.93/1.00    inference(equality_resolution,[],[f84])).
% 1.93/1.00  
% 1.93/1.00  fof(f8,axiom,(
% 1.93/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f27,plain,(
% 1.93/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.93/1.00    inference(nnf_transformation,[],[f8])).
% 1.93/1.00  
% 1.93/1.00  fof(f28,plain,(
% 1.93/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.93/1.00    inference(rectify,[],[f27])).
% 1.93/1.00  
% 1.93/1.00  fof(f29,plain,(
% 1.93/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 1.93/1.00    introduced(choice_axiom,[])).
% 1.93/1.00  
% 1.93/1.00  fof(f30,plain,(
% 1.93/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 1.93/1.00  
% 1.93/1.00  fof(f47,plain,(
% 1.93/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.93/1.00    inference(cnf_transformation,[],[f30])).
% 1.93/1.00  
% 1.93/1.00  fof(f81,plain,(
% 1.93/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 1.93/1.00    inference(definition_unfolding,[],[f47,f53])).
% 1.93/1.00  
% 1.93/1.00  fof(f93,plain,(
% 1.93/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 1.93/1.00    inference(equality_resolution,[],[f81])).
% 1.93/1.00  
% 1.93/1.00  fof(f48,plain,(
% 1.93/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.93/1.00    inference(cnf_transformation,[],[f30])).
% 1.93/1.00  
% 1.93/1.00  fof(f80,plain,(
% 1.93/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 1.93/1.00    inference(definition_unfolding,[],[f48,f53])).
% 1.93/1.00  
% 1.93/1.00  fof(f91,plain,(
% 1.93/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 1.93/1.00    inference(equality_resolution,[],[f80])).
% 1.93/1.00  
% 1.93/1.00  fof(f92,plain,(
% 1.93/1.00    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 1.93/1.00    inference(equality_resolution,[],[f91])).
% 1.93/1.00  
% 1.93/1.00  fof(f61,plain,(
% 1.93/1.00    sK2 != sK3),
% 1.93/1.00    inference(cnf_transformation,[],[f32])).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1,plain,
% 1.93/1.00      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_21,negated_conjecture,
% 1.93/1.00      ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) = k2_tarski(sK2,sK2) ),
% 1.93/1.00      inference(cnf_transformation,[],[f83]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1752,plain,
% 1.93/1.00      ( k2_tarski(sK2,sK3) = k2_tarski(sK2,sK2) ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_1,c_21]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_18,plain,
% 1.93/1.00      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_10,plain,
% 1.93/1.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 1.93/1.00      inference(cnf_transformation,[],[f85]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_889,plain,
% 1.93/1.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_4608,plain,
% 1.93/1.00      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_18,c_889]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_4612,plain,
% 1.93/1.00      ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_1752,c_4608]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_17,plain,
% 1.93/1.00      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 1.93/1.00      inference(cnf_transformation,[],[f93]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1053,plain,
% 1.93/1.00      ( ~ r2_hidden(sK3,k2_tarski(X0,X0)) | sK3 = X0 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1054,plain,
% 1.93/1.00      ( sK3 = X0 | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1053]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1056,plain,
% 1.93/1.00      ( sK3 = sK2 | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1054]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_688,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1005,plain,
% 1.93/1.00      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_688]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1006,plain,
% 1.93/1.00      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1005]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_16,plain,
% 1.93/1.00      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 1.93/1.00      inference(cnf_transformation,[],[f92]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_28,plain,
% 1.93/1.00      ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_25,plain,
% 1.93/1.00      ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2)) | sK2 = sK2 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_20,negated_conjecture,
% 1.93/1.00      ( sK2 != sK3 ),
% 1.93/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(contradiction,plain,
% 1.93/1.00      ( $false ),
% 1.93/1.00      inference(minisat,
% 1.93/1.00                [status(thm)],
% 1.93/1.00                [c_4612,c_1056,c_1006,c_28,c_25,c_20]) ).
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.93/1.00  
% 1.93/1.00  ------                               Statistics
% 1.93/1.00  
% 1.93/1.00  ------ General
% 1.93/1.00  
% 1.93/1.00  abstr_ref_over_cycles:                  0
% 1.93/1.00  abstr_ref_under_cycles:                 0
% 1.93/1.00  gc_basic_clause_elim:                   0
% 1.93/1.00  forced_gc_time:                         0
% 1.93/1.00  parsing_time:                           0.008
% 1.93/1.00  unif_index_cands_time:                  0.
% 1.93/1.00  unif_index_add_time:                    0.
% 1.93/1.00  orderings_time:                         0.
% 1.93/1.00  out_proof_time:                         0.005
% 1.93/1.00  total_time:                             0.173
% 1.93/1.00  num_of_symbols:                         41
% 1.93/1.00  num_of_terms:                           7345
% 1.93/1.00  
% 1.93/1.00  ------ Preprocessing
% 1.93/1.00  
% 1.93/1.00  num_of_splits:                          0
% 1.93/1.00  num_of_split_atoms:                     0
% 1.93/1.00  num_of_reused_defs:                     0
% 1.93/1.00  num_eq_ax_congr_red:                    42
% 1.93/1.00  num_of_sem_filtered_clauses:            1
% 1.93/1.00  num_of_subtypes:                        0
% 1.93/1.00  monotx_restored_types:                  0
% 1.93/1.00  sat_num_of_epr_types:                   0
% 1.93/1.00  sat_num_of_non_cyclic_types:            0
% 1.93/1.00  sat_guarded_non_collapsed_types:        0
% 1.93/1.00  num_pure_diseq_elim:                    0
% 1.93/1.00  simp_replaced_by:                       0
% 1.93/1.00  res_preprocessed:                       79
% 1.93/1.00  prep_upred:                             0
% 1.93/1.00  prep_unflattend:                        36
% 1.93/1.00  smt_new_axioms:                         0
% 1.93/1.00  pred_elim_cands:                        1
% 1.93/1.00  pred_elim:                              0
% 1.93/1.00  pred_elim_cl:                           0
% 1.93/1.00  pred_elim_cycles:                       1
% 1.93/1.00  merged_defs:                            0
% 1.93/1.00  merged_defs_ncl:                        0
% 1.93/1.00  bin_hyper_res:                          0
% 1.93/1.00  prep_cycles:                            3
% 1.93/1.00  pred_elim_time:                         0.008
% 1.93/1.00  splitting_time:                         0.
% 1.93/1.00  sem_filter_time:                        0.
% 1.93/1.00  monotx_time:                            0.
% 1.93/1.00  subtype_inf_time:                       0.
% 1.93/1.00  
% 1.93/1.00  ------ Problem properties
% 1.93/1.00  
% 1.93/1.00  clauses:                                22
% 1.93/1.00  conjectures:                            2
% 1.93/1.00  epr:                                    1
% 1.93/1.00  horn:                                   19
% 1.93/1.00  ground:                                 2
% 1.93/1.00  unary:                                  14
% 1.93/1.00  binary:                                 1
% 1.93/1.00  lits:                                   40
% 1.93/1.00  lits_eq:                                28
% 1.93/1.00  fd_pure:                                0
% 1.93/1.00  fd_pseudo:                              0
% 1.93/1.00  fd_cond:                                0
% 1.93/1.00  fd_pseudo_cond:                         6
% 1.93/1.00  ac_symbols:                             0
% 1.93/1.00  
% 1.93/1.00  ------ Propositional Solver
% 1.93/1.00  
% 1.93/1.00  prop_solver_calls:                      23
% 1.93/1.00  prop_fast_solver_calls:                 469
% 1.93/1.00  smt_solver_calls:                       0
% 1.93/1.00  smt_fast_solver_calls:                  0
% 1.93/1.00  prop_num_of_clauses:                    1945
% 1.93/1.00  prop_preprocess_simplified:             6377
% 1.93/1.00  prop_fo_subsumed:                       0
% 1.93/1.00  prop_solver_time:                       0.
% 1.93/1.00  smt_solver_time:                        0.
% 1.93/1.00  smt_fast_solver_time:                   0.
% 1.93/1.00  prop_fast_solver_time:                  0.
% 1.93/1.00  prop_unsat_core_time:                   0.
% 1.93/1.00  
% 1.93/1.00  ------ QBF
% 1.93/1.00  
% 1.93/1.00  qbf_q_res:                              0
% 1.93/1.00  qbf_num_tautologies:                    0
% 1.93/1.00  qbf_prep_cycles:                        0
% 1.93/1.00  
% 1.93/1.00  ------ BMC1
% 1.93/1.00  
% 1.93/1.00  bmc1_current_bound:                     -1
% 1.93/1.00  bmc1_last_solved_bound:                 -1
% 1.93/1.00  bmc1_unsat_core_size:                   -1
% 1.93/1.00  bmc1_unsat_core_parents_size:           -1
% 1.93/1.00  bmc1_merge_next_fun:                    0
% 1.93/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.93/1.00  
% 1.93/1.00  ------ Instantiation
% 1.93/1.00  
% 1.93/1.00  inst_num_of_clauses:                    605
% 1.93/1.00  inst_num_in_passive:                    433
% 1.93/1.00  inst_num_in_active:                     151
% 1.93/1.00  inst_num_in_unprocessed:                21
% 1.93/1.00  inst_num_of_loops:                      180
% 1.93/1.00  inst_num_of_learning_restarts:          0
% 1.93/1.00  inst_num_moves_active_passive:          28
% 1.93/1.00  inst_lit_activity:                      0
% 1.93/1.00  inst_lit_activity_moves:                0
% 1.93/1.00  inst_num_tautologies:                   0
% 1.93/1.00  inst_num_prop_implied:                  0
% 1.93/1.00  inst_num_existing_simplified:           0
% 1.93/1.00  inst_num_eq_res_simplified:             0
% 1.93/1.00  inst_num_child_elim:                    0
% 1.93/1.00  inst_num_of_dismatching_blockings:      131
% 1.93/1.00  inst_num_of_non_proper_insts:           493
% 1.93/1.00  inst_num_of_duplicates:                 0
% 1.93/1.00  inst_inst_num_from_inst_to_res:         0
% 1.93/1.00  inst_dismatching_checking_time:         0.
% 1.93/1.00  
% 1.93/1.00  ------ Resolution
% 1.93/1.00  
% 1.93/1.00  res_num_of_clauses:                     0
% 1.93/1.00  res_num_in_passive:                     0
% 1.93/1.00  res_num_in_active:                      0
% 1.93/1.00  res_num_of_loops:                       82
% 1.93/1.00  res_forward_subset_subsumed:            44
% 1.93/1.00  res_backward_subset_subsumed:           0
% 1.93/1.00  res_forward_subsumed:                   0
% 1.93/1.00  res_backward_subsumed:                  0
% 1.93/1.00  res_forward_subsumption_resolution:     0
% 1.93/1.00  res_backward_subsumption_resolution:    0
% 1.93/1.00  res_clause_to_clause_subsumption:       415
% 1.93/1.00  res_orphan_elimination:                 0
% 1.93/1.00  res_tautology_del:                      12
% 1.93/1.00  res_num_eq_res_simplified:              0
% 1.93/1.00  res_num_sel_changes:                    0
% 1.93/1.00  res_moves_from_active_to_pass:          0
% 1.93/1.00  
% 1.93/1.00  ------ Superposition
% 1.93/1.00  
% 1.93/1.00  sup_time_total:                         0.
% 1.93/1.00  sup_time_generating:                    0.
% 1.93/1.00  sup_time_sim_full:                      0.
% 1.93/1.00  sup_time_sim_immed:                     0.
% 1.93/1.00  
% 1.93/1.00  sup_num_of_clauses:                     108
% 1.93/1.00  sup_num_in_active:                      35
% 1.93/1.00  sup_num_in_passive:                     73
% 1.93/1.00  sup_num_of_loops:                       35
% 1.93/1.00  sup_fw_superposition:                   74
% 1.93/1.00  sup_bw_superposition:                   85
% 1.93/1.00  sup_immediate_simplified:               51
% 1.93/1.00  sup_given_eliminated:                   1
% 1.93/1.00  comparisons_done:                       0
% 1.93/1.00  comparisons_avoided:                    2
% 1.93/1.00  
% 1.93/1.00  ------ Simplifications
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  sim_fw_subset_subsumed:                 0
% 1.93/1.00  sim_bw_subset_subsumed:                 0
% 1.93/1.00  sim_fw_subsumed:                        9
% 1.93/1.00  sim_bw_subsumed:                        2
% 1.93/1.00  sim_fw_subsumption_res:                 0
% 1.93/1.00  sim_bw_subsumption_res:                 0
% 1.93/1.00  sim_tautology_del:                      0
% 1.93/1.00  sim_eq_tautology_del:                   2
% 1.93/1.00  sim_eq_res_simp:                        0
% 1.93/1.00  sim_fw_demodulated:                     36
% 1.93/1.00  sim_bw_demodulated:                     5
% 1.93/1.00  sim_light_normalised:                   16
% 1.93/1.00  sim_joinable_taut:                      0
% 1.93/1.00  sim_joinable_simp:                      0
% 1.93/1.00  sim_ac_normalised:                      0
% 1.93/1.00  sim_smt_subsumption:                    0
% 1.93/1.00  
%------------------------------------------------------------------------------
