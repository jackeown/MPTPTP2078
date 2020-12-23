%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:10 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 118 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  232 ( 363 expanded)
%              Number of equality atoms :  175 ( 268 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f37])).

fof(f70,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,(
    k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK2) ),
    inference(definition_unfolding,[],[f70,f72,f63,f63,f63])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f61,f72,f63,f63])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f96,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f97,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f96])).

fof(f10,axiom,(
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
    inference(nnf_transformation,[],[f10])).

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
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f63])).

fof(f105,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f103,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f89])).

fof(f104,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f103])).

fof(f71,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_25,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2247,plain,
    ( k2_tarski(sK2,sK3) = k2_tarski(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_25,c_0])).

cnf(c_22,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_14,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1610,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2961,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1610])).

cnf(c_3263,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2247,c_2961])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1728,plain,
    ( ~ r2_hidden(sK3,k2_tarski(X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1729,plain,
    ( sK3 = X0
    | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1728])).

cnf(c_1731,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_1350,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1670,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_1671,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_32,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_29,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_24,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3263,c_1731,c_1671,c_32,c_29,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.38/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.01  
% 3.38/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.38/1.01  
% 3.38/1.01  ------  iProver source info
% 3.38/1.01  
% 3.38/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.38/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.38/1.01  git: non_committed_changes: false
% 3.38/1.01  git: last_make_outside_of_git: false
% 3.38/1.01  
% 3.38/1.01  ------ 
% 3.38/1.01  ------ Parsing...
% 3.38/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.38/1.01  
% 3.38/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.38/1.01  
% 3.38/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.38/1.01  
% 3.38/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.38/1.01  ------ Proving...
% 3.38/1.01  ------ Problem Properties 
% 3.38/1.01  
% 3.38/1.01  
% 3.38/1.01  clauses                                 25
% 3.38/1.01  conjectures                             2
% 3.38/1.01  EPR                                     3
% 3.38/1.01  Horn                                    22
% 3.38/1.01  unary                                   15
% 3.38/1.01  binary                                  2
% 3.38/1.01  lits                                    46
% 3.38/1.01  lits eq                                 30
% 3.38/1.01  fd_pure                                 0
% 3.38/1.01  fd_pseudo                               0
% 3.38/1.01  fd_cond                                 0
% 3.38/1.01  fd_pseudo_cond                          7
% 3.38/1.01  AC symbols                              0
% 3.38/1.01  
% 3.38/1.01  ------ Input Options Time Limit: Unbounded
% 3.38/1.01  
% 3.38/1.01  
% 3.38/1.01  ------ 
% 3.38/1.01  Current options:
% 3.38/1.01  ------ 
% 3.38/1.01  
% 3.38/1.01  
% 3.38/1.01  
% 3.38/1.01  
% 3.38/1.01  ------ Proving...
% 3.38/1.01  
% 3.38/1.01  
% 3.38/1.01  % SZS status Theorem for theBenchmark.p
% 3.38/1.01  
% 3.38/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.38/1.01  
% 3.38/1.01  fof(f20,conjecture,(
% 3.38/1.01    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f21,negated_conjecture,(
% 3.38/1.01    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.38/1.01    inference(negated_conjecture,[],[f20])).
% 3.38/1.01  
% 3.38/1.01  fof(f25,plain,(
% 3.38/1.01    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.38/1.01    inference(ennf_transformation,[],[f21])).
% 3.38/1.01  
% 3.38/1.01  fof(f37,plain,(
% 3.38/1.01    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 3.38/1.01    introduced(choice_axiom,[])).
% 3.38/1.01  
% 3.38/1.01  fof(f38,plain,(
% 3.38/1.01    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f37])).
% 3.38/1.01  
% 3.38/1.01  fof(f70,plain,(
% 3.38/1.01    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.38/1.01    inference(cnf_transformation,[],[f38])).
% 3.38/1.01  
% 3.38/1.01  fof(f8,axiom,(
% 3.38/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f48,plain,(
% 3.38/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.38/1.01    inference(cnf_transformation,[],[f8])).
% 3.38/1.01  
% 3.38/1.01  fof(f5,axiom,(
% 3.38/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f45,plain,(
% 3.38/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.38/1.01    inference(cnf_transformation,[],[f5])).
% 3.38/1.01  
% 3.38/1.01  fof(f72,plain,(
% 3.38/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.38/1.01    inference(definition_unfolding,[],[f48,f45])).
% 3.38/1.01  
% 3.38/1.01  fof(f13,axiom,(
% 3.38/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f63,plain,(
% 3.38/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.38/1.01    inference(cnf_transformation,[],[f13])).
% 3.38/1.01  
% 3.38/1.01  fof(f93,plain,(
% 3.38/1.01    k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK2)),
% 3.38/1.01    inference(definition_unfolding,[],[f70,f72,f63,f63,f63])).
% 3.38/1.01  
% 3.38/1.01  fof(f11,axiom,(
% 3.38/1.01    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f61,plain,(
% 3.38/1.01    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.38/1.01    inference(cnf_transformation,[],[f11])).
% 3.38/1.01  
% 3.38/1.01  fof(f75,plain,(
% 3.38/1.01    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1)) )),
% 3.38/1.01    inference(definition_unfolding,[],[f61,f72,f63,f63])).
% 3.38/1.01  
% 3.38/1.01  fof(f14,axiom,(
% 3.38/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f64,plain,(
% 3.38/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.38/1.01    inference(cnf_transformation,[],[f14])).
% 3.38/1.01  
% 3.38/1.01  fof(f15,axiom,(
% 3.38/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f65,plain,(
% 3.38/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.38/1.01    inference(cnf_transformation,[],[f15])).
% 3.38/1.01  
% 3.38/1.01  fof(f16,axiom,(
% 3.38/1.01    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f66,plain,(
% 3.38/1.01    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.38/1.01    inference(cnf_transformation,[],[f16])).
% 3.38/1.01  
% 3.38/1.01  fof(f17,axiom,(
% 3.38/1.01    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f67,plain,(
% 3.38/1.01    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.38/1.01    inference(cnf_transformation,[],[f17])).
% 3.38/1.01  
% 3.38/1.01  fof(f73,plain,(
% 3.38/1.01    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.38/1.01    inference(definition_unfolding,[],[f66,f67])).
% 3.38/1.01  
% 3.38/1.01  fof(f74,plain,(
% 3.38/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.38/1.01    inference(definition_unfolding,[],[f65,f73])).
% 3.38/1.01  
% 3.38/1.01  fof(f91,plain,(
% 3.38/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.38/1.01    inference(definition_unfolding,[],[f64,f74])).
% 3.38/1.01  
% 3.38/1.01  fof(f9,axiom,(
% 3.38/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f24,plain,(
% 3.38/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.38/1.01    inference(ennf_transformation,[],[f9])).
% 3.38/1.01  
% 3.38/1.01  fof(f28,plain,(
% 3.38/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/1.01    inference(nnf_transformation,[],[f24])).
% 3.38/1.01  
% 3.38/1.01  fof(f29,plain,(
% 3.38/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/1.01    inference(flattening,[],[f28])).
% 3.38/1.01  
% 3.38/1.01  fof(f30,plain,(
% 3.38/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/1.01    inference(rectify,[],[f29])).
% 3.38/1.01  
% 3.38/1.01  fof(f31,plain,(
% 3.38/1.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.38/1.01    introduced(choice_axiom,[])).
% 3.38/1.01  
% 3.38/1.01  fof(f32,plain,(
% 3.38/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.38/1.01  
% 3.38/1.01  fof(f52,plain,(
% 3.38/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.38/1.01    inference(cnf_transformation,[],[f32])).
% 3.38/1.01  
% 3.38/1.01  fof(f83,plain,(
% 3.38/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 3.38/1.01    inference(definition_unfolding,[],[f52,f74])).
% 3.38/1.01  
% 3.38/1.01  fof(f96,plain,(
% 3.38/1.01    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3) )),
% 3.38/1.01    inference(equality_resolution,[],[f83])).
% 3.38/1.01  
% 3.38/1.01  fof(f97,plain,(
% 3.38/1.01    ( ! [X0,X5,X1] : (r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5))) )),
% 3.38/1.01    inference(equality_resolution,[],[f96])).
% 3.38/1.01  
% 3.38/1.01  fof(f10,axiom,(
% 3.38/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f33,plain,(
% 3.38/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.38/1.01    inference(nnf_transformation,[],[f10])).
% 3.38/1.01  
% 3.38/1.01  fof(f34,plain,(
% 3.38/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.38/1.01    inference(rectify,[],[f33])).
% 3.38/1.01  
% 3.38/1.01  fof(f35,plain,(
% 3.38/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.38/1.01    introduced(choice_axiom,[])).
% 3.38/1.01  
% 3.38/1.01  fof(f36,plain,(
% 3.38/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 3.38/1.01  
% 3.38/1.01  fof(f57,plain,(
% 3.38/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.38/1.01    inference(cnf_transformation,[],[f36])).
% 3.38/1.01  
% 3.38/1.01  fof(f90,plain,(
% 3.38/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 3.38/1.01    inference(definition_unfolding,[],[f57,f63])).
% 3.38/1.01  
% 3.38/1.01  fof(f105,plain,(
% 3.38/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 3.38/1.01    inference(equality_resolution,[],[f90])).
% 3.38/1.01  
% 3.38/1.01  fof(f58,plain,(
% 3.38/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.38/1.01    inference(cnf_transformation,[],[f36])).
% 3.38/1.01  
% 3.38/1.01  fof(f89,plain,(
% 3.38/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 3.38/1.01    inference(definition_unfolding,[],[f58,f63])).
% 3.38/1.01  
% 3.38/1.01  fof(f103,plain,(
% 3.38/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 3.38/1.01    inference(equality_resolution,[],[f89])).
% 3.38/1.01  
% 3.38/1.01  fof(f104,plain,(
% 3.38/1.01    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 3.38/1.01    inference(equality_resolution,[],[f103])).
% 3.38/1.01  
% 3.38/1.01  fof(f71,plain,(
% 3.38/1.01    sK2 != sK3),
% 3.38/1.01    inference(cnf_transformation,[],[f38])).
% 3.38/1.01  
% 3.38/1.01  cnf(c_25,negated_conjecture,
% 3.38/1.01      ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK2) ),
% 3.38/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_0,plain,
% 3.38/1.01      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 3.38/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2247,plain,
% 3.38/1.01      ( k2_tarski(sK2,sK3) = k2_tarski(sK2,sK2) ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_25,c_0]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_22,plain,
% 3.38/1.01      ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 3.38/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_14,plain,
% 3.38/1.01      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
% 3.38/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1610,plain,
% 3.38/1.01      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2961,plain,
% 3.38/1.01      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_22,c_1610]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_3263,plain,
% 3.38/1.01      ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_2247,c_2961]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_21,plain,
% 3.38/1.01      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 3.38/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1728,plain,
% 3.38/1.01      ( ~ r2_hidden(sK3,k2_tarski(X0,X0)) | sK3 = X0 ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1729,plain,
% 3.38/1.01      ( sK3 = X0 | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_1728]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1731,plain,
% 3.38/1.01      ( sK3 = sK2 | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_1729]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1350,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1670,plain,
% 3.38/1.01      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_1350]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1671,plain,
% 3.38/1.01      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_1670]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_20,plain,
% 3.38/1.01      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 3.38/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_32,plain,
% 3.38/1.01      ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_29,plain,
% 3.38/1.01      ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2)) | sK2 = sK2 ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_24,negated_conjecture,
% 3.38/1.01      ( sK2 != sK3 ),
% 3.38/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(contradiction,plain,
% 3.38/1.01      ( $false ),
% 3.38/1.01      inference(minisat,
% 3.38/1.01                [status(thm)],
% 3.38/1.01                [c_3263,c_1731,c_1671,c_32,c_29,c_24]) ).
% 3.38/1.01  
% 3.38/1.01  
% 3.38/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.38/1.01  
% 3.38/1.01  ------                               Statistics
% 3.38/1.01  
% 3.38/1.01  ------ Selected
% 3.38/1.01  
% 3.38/1.01  total_time:                             0.155
% 3.38/1.01  
%------------------------------------------------------------------------------
