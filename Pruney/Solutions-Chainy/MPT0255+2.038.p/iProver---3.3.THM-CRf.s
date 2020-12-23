%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:21 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 106 expanded)
%              Number of clauses        :   27 (  28 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  205 ( 310 expanded)
%              Number of equality atoms :  112 ( 191 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
   => k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f29])).

fof(f53,plain,(
    k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f65,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f53,f55,f54])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f70,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f63])).

fof(f71,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f70])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
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

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f19])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1298,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19,c_11])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_891,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1644,plain,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_891])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_894,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2778,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1644,c_894])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_889,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3201,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2778,c_889])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_883,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3207,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3201,c_883])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2304,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2309,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2304])).

cnf(c_2311,plain,
    ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2309])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1570,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X2))
    | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2303,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))
    | ~ r2_hidden(X0,k1_xboole_0)
    | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_2305,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2303])).

cnf(c_2307,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,k1_xboole_0) != iProver_top
    | r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2305])).

cnf(c_23,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_25,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3207,c_2311,c_2307,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:05:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.06/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/1.01  
% 3.06/1.01  ------  iProver source info
% 3.06/1.01  
% 3.06/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.06/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/1.01  git: non_committed_changes: false
% 3.06/1.01  git: last_make_outside_of_git: false
% 3.06/1.01  
% 3.06/1.01  ------ 
% 3.06/1.01  ------ Parsing...
% 3.06/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/1.01  ------ Proving...
% 3.06/1.01  ------ Problem Properties 
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  clauses                                 19
% 3.06/1.01  conjectures                             1
% 3.06/1.01  EPR                                     5
% 3.06/1.01  Horn                                    15
% 3.06/1.01  unary                                   8
% 3.06/1.01  binary                                  5
% 3.06/1.01  lits                                    37
% 3.06/1.01  lits eq                                 16
% 3.06/1.01  fd_pure                                 0
% 3.06/1.01  fd_pseudo                               0
% 3.06/1.01  fd_cond                                 0
% 3.06/1.01  fd_pseudo_cond                          4
% 3.06/1.01  AC symbols                              0
% 3.06/1.01  
% 3.06/1.01  ------ Input Options Time Limit: Unbounded
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  ------ 
% 3.06/1.01  Current options:
% 3.06/1.01  ------ 
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  ------ Proving...
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  % SZS status Theorem for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  fof(f13,conjecture,(
% 3.06/1.01    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f14,negated_conjecture,(
% 3.06/1.01    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 3.06/1.01    inference(negated_conjecture,[],[f13])).
% 3.06/1.01  
% 3.06/1.01  fof(f18,plain,(
% 3.06/1.01    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0),
% 3.06/1.01    inference(ennf_transformation,[],[f14])).
% 3.06/1.01  
% 3.06/1.01  fof(f29,plain,(
% 3.06/1.01    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 => k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f30,plain,(
% 3.06/1.01    k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 3.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f29])).
% 3.06/1.01  
% 3.06/1.01  fof(f53,plain,(
% 3.06/1.01    k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 3.06/1.01    inference(cnf_transformation,[],[f30])).
% 3.06/1.01  
% 3.06/1.01  fof(f12,axiom,(
% 3.06/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f52,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f12])).
% 3.06/1.01  
% 3.06/1.01  fof(f55,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.06/1.01    inference(definition_unfolding,[],[f52,f54])).
% 3.06/1.01  
% 3.06/1.01  fof(f10,axiom,(
% 3.06/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f50,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f10])).
% 3.06/1.01  
% 3.06/1.01  fof(f11,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f51,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f11])).
% 3.06/1.01  
% 3.06/1.01  fof(f54,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.06/1.01    inference(definition_unfolding,[],[f50,f51])).
% 3.06/1.01  
% 3.06/1.01  fof(f65,plain,(
% 3.06/1.01    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3),sK4))),
% 3.06/1.01    inference(definition_unfolding,[],[f53,f55,f54])).
% 3.06/1.01  
% 3.06/1.01  fof(f7,axiom,(
% 3.06/1.01    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f42,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 3.06/1.01    inference(cnf_transformation,[],[f7])).
% 3.06/1.01  
% 3.06/1.01  fof(f58,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0) )),
% 3.06/1.01    inference(definition_unfolding,[],[f42,f55])).
% 3.06/1.01  
% 3.06/1.01  fof(f4,axiom,(
% 3.06/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f23,plain,(
% 3.06/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.06/1.01    inference(nnf_transformation,[],[f4])).
% 3.06/1.01  
% 3.06/1.01  fof(f38,plain,(
% 3.06/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.06/1.01    inference(cnf_transformation,[],[f23])).
% 3.06/1.01  
% 3.06/1.01  fof(f3,axiom,(
% 3.06/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f21,plain,(
% 3.06/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/1.01    inference(nnf_transformation,[],[f3])).
% 3.06/1.01  
% 3.06/1.01  fof(f22,plain,(
% 3.06/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/1.01    inference(flattening,[],[f21])).
% 3.06/1.01  
% 3.06/1.01  fof(f37,plain,(
% 3.06/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f22])).
% 3.06/1.01  
% 3.06/1.01  fof(f6,axiom,(
% 3.06/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f41,plain,(
% 3.06/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f6])).
% 3.06/1.01  
% 3.06/1.01  fof(f9,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f24,plain,(
% 3.06/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.06/1.01    inference(nnf_transformation,[],[f9])).
% 3.06/1.01  
% 3.06/1.01  fof(f25,plain,(
% 3.06/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.06/1.01    inference(flattening,[],[f24])).
% 3.06/1.01  
% 3.06/1.01  fof(f26,plain,(
% 3.06/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.06/1.01    inference(rectify,[],[f25])).
% 3.06/1.01  
% 3.06/1.01  fof(f27,plain,(
% 3.06/1.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f28,plain,(
% 3.06/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 3.06/1.01  
% 3.06/1.01  fof(f45,plain,(
% 3.06/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.06/1.01    inference(cnf_transformation,[],[f28])).
% 3.06/1.01  
% 3.06/1.01  fof(f63,plain,(
% 3.06/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.06/1.01    inference(definition_unfolding,[],[f45,f54])).
% 3.06/1.01  
% 3.06/1.01  fof(f70,plain,(
% 3.06/1.01    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.06/1.01    inference(equality_resolution,[],[f63])).
% 3.06/1.01  
% 3.06/1.01  fof(f71,plain,(
% 3.06/1.01    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.06/1.01    inference(equality_resolution,[],[f70])).
% 3.06/1.01  
% 3.06/1.01  fof(f8,axiom,(
% 3.06/1.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f43,plain,(
% 3.06/1.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f8])).
% 3.06/1.01  
% 3.06/1.01  fof(f2,axiom,(
% 3.06/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f15,plain,(
% 3.06/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.06/1.01    inference(rectify,[],[f2])).
% 3.06/1.01  
% 3.06/1.01  fof(f16,plain,(
% 3.06/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.06/1.01    inference(ennf_transformation,[],[f15])).
% 3.06/1.01  
% 3.06/1.01  fof(f19,plain,(
% 3.06/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f20,plain,(
% 3.06/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f19])).
% 3.06/1.01  
% 3.06/1.01  fof(f34,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f20])).
% 3.06/1.01  
% 3.06/1.01  cnf(c_19,negated_conjecture,
% 3.06/1.01      ( k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3),sK4)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_11,plain,
% 3.06/1.01      ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 ),
% 3.06/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1298,plain,
% 3.06/1.01      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k1_xboole_0) = k1_xboole_0 ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_19,c_11]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8,plain,
% 3.06/1.01      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.06/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_891,plain,
% 3.06/1.01      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 3.06/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1644,plain,
% 3.06/1.01      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k1_xboole_0) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1298,c_891]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4,plain,
% 3.06/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.06/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_894,plain,
% 3.06/1.01      ( X0 = X1
% 3.06/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.06/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2778,plain,
% 3.06/1.01      ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0
% 3.06/1.01      | r1_tarski(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1644,c_894]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_10,plain,
% 3.06/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_889,plain,
% 3.06/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3201,plain,
% 3.06/1.01      ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0 ),
% 3.06/1.01      inference(forward_subsumption_resolution,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_2778,c_889]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_17,plain,
% 3.06/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_883,plain,
% 3.06/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3207,plain,
% 3.06/1.01      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_3201,c_883]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_12,plain,
% 3.06/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2304,plain,
% 3.06/1.01      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_xboole_0) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2309,plain,
% 3.06/1.01      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_xboole_0) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_2304]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2311,plain,
% 3.06/1.01      ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) = iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_2309]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1,plain,
% 3.06/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.06/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1570,plain,
% 3.06/1.01      ( ~ r2_hidden(X0,X1)
% 3.06/1.01      | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X2))
% 3.06/1.01      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2303,plain,
% 3.06/1.01      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))
% 3.06/1.01      | ~ r2_hidden(X0,k1_xboole_0)
% 3.06/1.01      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_xboole_0) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_1570]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2305,plain,
% 3.06/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) != iProver_top
% 3.06/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.06/1.01      | r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_xboole_0) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_2303]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2307,plain,
% 3.06/1.01      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.06/1.01      | r2_hidden(sK2,k1_xboole_0) != iProver_top
% 3.06/1.01      | r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) != iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_2305]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_23,plain,
% 3.06/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_25,plain,
% 3.06/1.01      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(contradiction,plain,
% 3.06/1.01      ( $false ),
% 3.06/1.01      inference(minisat,[status(thm)],[c_3207,c_2311,c_2307,c_25]) ).
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  ------                               Statistics
% 3.06/1.01  
% 3.06/1.01  ------ Selected
% 3.06/1.01  
% 3.06/1.01  total_time:                             0.135
% 3.06/1.01  
%------------------------------------------------------------------------------
