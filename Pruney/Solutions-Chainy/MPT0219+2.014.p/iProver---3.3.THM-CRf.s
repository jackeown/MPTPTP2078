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
% DateTime   : Thu Dec  3 11:29:11 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
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
fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f61,f47,f63,f63])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f93,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) = k2_tarski(sK2,sK2) ),
    inference(definition_unfolding,[],[f70,f47,f63,f63,f63])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f96,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f84])).

fof(f97,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f96])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f63])).

fof(f105,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f103,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f90])).

fof(f104,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f103])).

fof(f71,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) = k2_tarski(sK2,sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2514,plain,
    ( k2_tarski(sK2,sK3) = k2_tarski(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_0,c_25])).

cnf(c_22,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_14,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1595,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5212,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1595])).

cnf(c_5216,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2514,c_5212])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1785,plain,
    ( ~ r2_hidden(sK3,k2_tarski(X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1786,plain,
    ( sK3 = X0
    | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_1788,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1786])).

cnf(c_1350,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1733,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_1734,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1733])).

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
    inference(minisat,[status(thm)],[c_5216,c_1788,c_1734,c_32,c_29,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:01:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.07/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/0.98  
% 2.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.07/0.98  
% 2.07/0.98  ------  iProver source info
% 2.07/0.98  
% 2.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.07/0.98  git: non_committed_changes: false
% 2.07/0.98  git: last_make_outside_of_git: false
% 2.07/0.98  
% 2.07/0.98  ------ 
% 2.07/0.98  
% 2.07/0.98  ------ Input Options
% 2.07/0.98  
% 2.07/0.98  --out_options                           all
% 2.07/0.98  --tptp_safe_out                         true
% 2.07/0.98  --problem_path                          ""
% 2.07/0.98  --include_path                          ""
% 2.07/0.98  --clausifier                            res/vclausify_rel
% 2.07/0.98  --clausifier_options                    --mode clausify
% 2.07/0.98  --stdin                                 false
% 2.07/0.98  --stats_out                             all
% 2.07/0.98  
% 2.07/0.98  ------ General Options
% 2.07/0.98  
% 2.07/0.98  --fof                                   false
% 2.07/0.98  --time_out_real                         305.
% 2.07/0.98  --time_out_virtual                      -1.
% 2.07/0.98  --symbol_type_check                     false
% 2.07/0.98  --clausify_out                          false
% 2.07/0.98  --sig_cnt_out                           false
% 2.07/0.98  --trig_cnt_out                          false
% 2.07/0.98  --trig_cnt_out_tolerance                1.
% 2.07/0.98  --trig_cnt_out_sk_spl                   false
% 2.07/0.98  --abstr_cl_out                          false
% 2.07/0.98  
% 2.07/0.98  ------ Global Options
% 2.07/0.98  
% 2.07/0.98  --schedule                              default
% 2.07/0.98  --add_important_lit                     false
% 2.07/0.98  --prop_solver_per_cl                    1000
% 2.07/0.98  --min_unsat_core                        false
% 2.07/0.98  --soft_assumptions                      false
% 2.07/0.98  --soft_lemma_size                       3
% 2.07/0.98  --prop_impl_unit_size                   0
% 2.07/0.98  --prop_impl_unit                        []
% 2.07/0.98  --share_sel_clauses                     true
% 2.07/0.98  --reset_solvers                         false
% 2.07/0.98  --bc_imp_inh                            [conj_cone]
% 2.07/0.98  --conj_cone_tolerance                   3.
% 2.07/0.98  --extra_neg_conj                        none
% 2.07/0.98  --large_theory_mode                     true
% 2.07/0.98  --prolific_symb_bound                   200
% 2.07/0.98  --lt_threshold                          2000
% 2.07/0.98  --clause_weak_htbl                      true
% 2.07/0.98  --gc_record_bc_elim                     false
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing Options
% 2.07/0.98  
% 2.07/0.98  --preprocessing_flag                    true
% 2.07/0.98  --time_out_prep_mult                    0.1
% 2.07/0.98  --splitting_mode                        input
% 2.07/0.98  --splitting_grd                         true
% 2.07/0.98  --splitting_cvd                         false
% 2.07/0.98  --splitting_cvd_svl                     false
% 2.07/0.98  --splitting_nvd                         32
% 2.07/0.98  --sub_typing                            true
% 2.07/0.98  --prep_gs_sim                           true
% 2.07/0.98  --prep_unflatten                        true
% 2.07/0.98  --prep_res_sim                          true
% 2.07/0.98  --prep_upred                            true
% 2.07/0.98  --prep_sem_filter                       exhaustive
% 2.07/0.98  --prep_sem_filter_out                   false
% 2.07/0.98  --pred_elim                             true
% 2.07/0.98  --res_sim_input                         true
% 2.07/0.98  --eq_ax_congr_red                       true
% 2.07/0.98  --pure_diseq_elim                       true
% 2.07/0.98  --brand_transform                       false
% 2.07/0.98  --non_eq_to_eq                          false
% 2.07/0.98  --prep_def_merge                        true
% 2.07/0.98  --prep_def_merge_prop_impl              false
% 2.07/0.98  --prep_def_merge_mbd                    true
% 2.07/0.98  --prep_def_merge_tr_red                 false
% 2.07/0.98  --prep_def_merge_tr_cl                  false
% 2.07/0.98  --smt_preprocessing                     true
% 2.07/0.98  --smt_ac_axioms                         fast
% 2.07/0.98  --preprocessed_out                      false
% 2.07/0.98  --preprocessed_stats                    false
% 2.07/0.98  
% 2.07/0.98  ------ Abstraction refinement Options
% 2.07/0.98  
% 2.07/0.98  --abstr_ref                             []
% 2.07/0.98  --abstr_ref_prep                        false
% 2.07/0.98  --abstr_ref_until_sat                   false
% 2.07/0.98  --abstr_ref_sig_restrict                funpre
% 2.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.98  --abstr_ref_under                       []
% 2.07/0.98  
% 2.07/0.98  ------ SAT Options
% 2.07/0.98  
% 2.07/0.98  --sat_mode                              false
% 2.07/0.98  --sat_fm_restart_options                ""
% 2.07/0.98  --sat_gr_def                            false
% 2.07/0.98  --sat_epr_types                         true
% 2.07/0.98  --sat_non_cyclic_types                  false
% 2.07/0.98  --sat_finite_models                     false
% 2.07/0.98  --sat_fm_lemmas                         false
% 2.07/0.98  --sat_fm_prep                           false
% 2.07/0.98  --sat_fm_uc_incr                        true
% 2.07/0.98  --sat_out_model                         small
% 2.07/0.98  --sat_out_clauses                       false
% 2.07/0.98  
% 2.07/0.98  ------ QBF Options
% 2.07/0.98  
% 2.07/0.98  --qbf_mode                              false
% 2.07/0.98  --qbf_elim_univ                         false
% 2.07/0.98  --qbf_dom_inst                          none
% 2.07/0.98  --qbf_dom_pre_inst                      false
% 2.07/0.98  --qbf_sk_in                             false
% 2.07/0.98  --qbf_pred_elim                         true
% 2.07/0.98  --qbf_split                             512
% 2.07/0.98  
% 2.07/0.98  ------ BMC1 Options
% 2.07/0.98  
% 2.07/0.98  --bmc1_incremental                      false
% 2.07/0.98  --bmc1_axioms                           reachable_all
% 2.07/0.98  --bmc1_min_bound                        0
% 2.07/0.98  --bmc1_max_bound                        -1
% 2.07/0.98  --bmc1_max_bound_default                -1
% 2.07/0.98  --bmc1_symbol_reachability              true
% 2.07/0.98  --bmc1_property_lemmas                  false
% 2.07/0.98  --bmc1_k_induction                      false
% 2.07/0.98  --bmc1_non_equiv_states                 false
% 2.07/0.98  --bmc1_deadlock                         false
% 2.07/0.98  --bmc1_ucm                              false
% 2.07/0.98  --bmc1_add_unsat_core                   none
% 2.07/0.98  --bmc1_unsat_core_children              false
% 2.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.98  --bmc1_out_stat                         full
% 2.07/0.98  --bmc1_ground_init                      false
% 2.07/0.98  --bmc1_pre_inst_next_state              false
% 2.07/0.98  --bmc1_pre_inst_state                   false
% 2.07/0.98  --bmc1_pre_inst_reach_state             false
% 2.07/0.98  --bmc1_out_unsat_core                   false
% 2.07/0.98  --bmc1_aig_witness_out                  false
% 2.07/0.98  --bmc1_verbose                          false
% 2.07/0.98  --bmc1_dump_clauses_tptp                false
% 2.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.98  --bmc1_dump_file                        -
% 2.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.98  --bmc1_ucm_extend_mode                  1
% 2.07/0.98  --bmc1_ucm_init_mode                    2
% 2.07/0.98  --bmc1_ucm_cone_mode                    none
% 2.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.98  --bmc1_ucm_relax_model                  4
% 2.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.98  --bmc1_ucm_layered_model                none
% 2.07/0.98  --bmc1_ucm_max_lemma_size               10
% 2.07/0.98  
% 2.07/0.98  ------ AIG Options
% 2.07/0.98  
% 2.07/0.98  --aig_mode                              false
% 2.07/0.98  
% 2.07/0.98  ------ Instantiation Options
% 2.07/0.98  
% 2.07/0.98  --instantiation_flag                    true
% 2.07/0.98  --inst_sos_flag                         false
% 2.07/0.98  --inst_sos_phase                        true
% 2.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.98  --inst_lit_sel_side                     num_symb
% 2.07/0.98  --inst_solver_per_active                1400
% 2.07/0.98  --inst_solver_calls_frac                1.
% 2.07/0.98  --inst_passive_queue_type               priority_queues
% 2.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.98  --inst_passive_queues_freq              [25;2]
% 2.07/0.98  --inst_dismatching                      true
% 2.07/0.98  --inst_eager_unprocessed_to_passive     true
% 2.07/0.98  --inst_prop_sim_given                   true
% 2.07/0.98  --inst_prop_sim_new                     false
% 2.07/0.98  --inst_subs_new                         false
% 2.07/0.98  --inst_eq_res_simp                      false
% 2.07/0.98  --inst_subs_given                       false
% 2.07/0.98  --inst_orphan_elimination               true
% 2.07/0.98  --inst_learning_loop_flag               true
% 2.07/0.98  --inst_learning_start                   3000
% 2.07/0.98  --inst_learning_factor                  2
% 2.07/0.98  --inst_start_prop_sim_after_learn       3
% 2.07/0.98  --inst_sel_renew                        solver
% 2.07/0.98  --inst_lit_activity_flag                true
% 2.07/0.98  --inst_restr_to_given                   false
% 2.07/0.98  --inst_activity_threshold               500
% 2.07/0.98  --inst_out_proof                        true
% 2.07/0.98  
% 2.07/0.98  ------ Resolution Options
% 2.07/0.98  
% 2.07/0.98  --resolution_flag                       true
% 2.07/0.98  --res_lit_sel                           adaptive
% 2.07/0.98  --res_lit_sel_side                      none
% 2.07/0.98  --res_ordering                          kbo
% 2.07/0.98  --res_to_prop_solver                    active
% 2.07/0.98  --res_prop_simpl_new                    false
% 2.07/0.98  --res_prop_simpl_given                  true
% 2.07/0.98  --res_passive_queue_type                priority_queues
% 2.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.98  --res_passive_queues_freq               [15;5]
% 2.07/0.98  --res_forward_subs                      full
% 2.07/0.98  --res_backward_subs                     full
% 2.07/0.98  --res_forward_subs_resolution           true
% 2.07/0.98  --res_backward_subs_resolution          true
% 2.07/0.98  --res_orphan_elimination                true
% 2.07/0.98  --res_time_limit                        2.
% 2.07/0.98  --res_out_proof                         true
% 2.07/0.98  
% 2.07/0.98  ------ Superposition Options
% 2.07/0.98  
% 2.07/0.98  --superposition_flag                    true
% 2.07/0.98  --sup_passive_queue_type                priority_queues
% 2.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.98  --demod_completeness_check              fast
% 2.07/0.98  --demod_use_ground                      true
% 2.07/0.98  --sup_to_prop_solver                    passive
% 2.07/0.98  --sup_prop_simpl_new                    true
% 2.07/0.98  --sup_prop_simpl_given                  true
% 2.07/0.98  --sup_fun_splitting                     false
% 2.07/0.98  --sup_smt_interval                      50000
% 2.07/0.98  
% 2.07/0.98  ------ Superposition Simplification Setup
% 2.07/0.98  
% 2.07/0.98  --sup_indices_passive                   []
% 2.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_full_bw                           [BwDemod]
% 2.07/0.98  --sup_immed_triv                        [TrivRules]
% 2.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_immed_bw_main                     []
% 2.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.98  
% 2.07/0.98  ------ Combination Options
% 2.07/0.98  
% 2.07/0.98  --comb_res_mult                         3
% 2.07/0.98  --comb_sup_mult                         2
% 2.07/0.98  --comb_inst_mult                        10
% 2.07/0.98  
% 2.07/0.98  ------ Debug Options
% 2.07/0.98  
% 2.07/0.98  --dbg_backtrace                         false
% 2.07/0.98  --dbg_dump_prop_clauses                 false
% 2.07/0.98  --dbg_dump_prop_clauses_file            -
% 2.07/0.98  --dbg_out_stat                          false
% 2.07/0.98  ------ Parsing...
% 2.07/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.07/0.98  ------ Proving...
% 2.07/0.98  ------ Problem Properties 
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  clauses                                 25
% 2.07/0.98  conjectures                             2
% 2.07/0.98  EPR                                     3
% 2.07/0.98  Horn                                    22
% 2.07/0.98  unary                                   15
% 2.07/0.98  binary                                  2
% 2.07/0.98  lits                                    46
% 2.07/0.98  lits eq                                 30
% 2.07/0.98  fd_pure                                 0
% 2.07/0.98  fd_pseudo                               0
% 2.07/0.98  fd_cond                                 0
% 2.07/0.98  fd_pseudo_cond                          7
% 2.07/0.98  AC symbols                              0
% 2.07/0.98  
% 2.07/0.98  ------ Schedule dynamic 5 is on 
% 2.07/0.98  
% 2.07/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  ------ 
% 2.07/0.98  Current options:
% 2.07/0.98  ------ 
% 2.07/0.98  
% 2.07/0.98  ------ Input Options
% 2.07/0.98  
% 2.07/0.98  --out_options                           all
% 2.07/0.98  --tptp_safe_out                         true
% 2.07/0.98  --problem_path                          ""
% 2.07/0.98  --include_path                          ""
% 2.07/0.98  --clausifier                            res/vclausify_rel
% 2.07/0.98  --clausifier_options                    --mode clausify
% 2.07/0.98  --stdin                                 false
% 2.07/0.98  --stats_out                             all
% 2.07/0.98  
% 2.07/0.98  ------ General Options
% 2.07/0.98  
% 2.07/0.98  --fof                                   false
% 2.07/0.98  --time_out_real                         305.
% 2.07/0.98  --time_out_virtual                      -1.
% 2.07/0.98  --symbol_type_check                     false
% 2.07/0.98  --clausify_out                          false
% 2.07/0.98  --sig_cnt_out                           false
% 2.07/0.98  --trig_cnt_out                          false
% 2.07/0.98  --trig_cnt_out_tolerance                1.
% 2.07/0.98  --trig_cnt_out_sk_spl                   false
% 2.07/0.98  --abstr_cl_out                          false
% 2.07/0.98  
% 2.07/0.98  ------ Global Options
% 2.07/0.98  
% 2.07/0.98  --schedule                              default
% 2.07/0.98  --add_important_lit                     false
% 2.07/0.98  --prop_solver_per_cl                    1000
% 2.07/0.98  --min_unsat_core                        false
% 2.07/0.98  --soft_assumptions                      false
% 2.07/0.98  --soft_lemma_size                       3
% 2.07/0.98  --prop_impl_unit_size                   0
% 2.07/0.98  --prop_impl_unit                        []
% 2.07/0.98  --share_sel_clauses                     true
% 2.07/0.98  --reset_solvers                         false
% 2.07/0.98  --bc_imp_inh                            [conj_cone]
% 2.07/0.98  --conj_cone_tolerance                   3.
% 2.07/0.98  --extra_neg_conj                        none
% 2.07/0.98  --large_theory_mode                     true
% 2.07/0.98  --prolific_symb_bound                   200
% 2.07/0.98  --lt_threshold                          2000
% 2.07/0.98  --clause_weak_htbl                      true
% 2.07/0.98  --gc_record_bc_elim                     false
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing Options
% 2.07/0.98  
% 2.07/0.98  --preprocessing_flag                    true
% 2.07/0.98  --time_out_prep_mult                    0.1
% 2.07/0.98  --splitting_mode                        input
% 2.07/0.98  --splitting_grd                         true
% 2.07/0.98  --splitting_cvd                         false
% 2.07/0.98  --splitting_cvd_svl                     false
% 2.07/0.98  --splitting_nvd                         32
% 2.07/0.98  --sub_typing                            true
% 2.07/0.98  --prep_gs_sim                           true
% 2.07/0.98  --prep_unflatten                        true
% 2.07/0.98  --prep_res_sim                          true
% 2.07/0.98  --prep_upred                            true
% 2.07/0.98  --prep_sem_filter                       exhaustive
% 2.07/0.98  --prep_sem_filter_out                   false
% 2.07/0.98  --pred_elim                             true
% 2.07/0.98  --res_sim_input                         true
% 2.07/0.98  --eq_ax_congr_red                       true
% 2.07/0.98  --pure_diseq_elim                       true
% 2.07/0.98  --brand_transform                       false
% 2.07/0.98  --non_eq_to_eq                          false
% 2.07/0.98  --prep_def_merge                        true
% 2.07/0.98  --prep_def_merge_prop_impl              false
% 2.07/0.98  --prep_def_merge_mbd                    true
% 2.07/0.98  --prep_def_merge_tr_red                 false
% 2.07/0.98  --prep_def_merge_tr_cl                  false
% 2.07/0.98  --smt_preprocessing                     true
% 2.07/0.98  --smt_ac_axioms                         fast
% 2.07/0.98  --preprocessed_out                      false
% 2.07/0.98  --preprocessed_stats                    false
% 2.07/0.98  
% 2.07/0.98  ------ Abstraction refinement Options
% 2.07/0.98  
% 2.07/0.98  --abstr_ref                             []
% 2.07/0.98  --abstr_ref_prep                        false
% 2.07/0.98  --abstr_ref_until_sat                   false
% 2.07/0.98  --abstr_ref_sig_restrict                funpre
% 2.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.98  --abstr_ref_under                       []
% 2.07/0.98  
% 2.07/0.98  ------ SAT Options
% 2.07/0.98  
% 2.07/0.98  --sat_mode                              false
% 2.07/0.98  --sat_fm_restart_options                ""
% 2.07/0.98  --sat_gr_def                            false
% 2.07/0.98  --sat_epr_types                         true
% 2.07/0.98  --sat_non_cyclic_types                  false
% 2.07/0.98  --sat_finite_models                     false
% 2.07/0.98  --sat_fm_lemmas                         false
% 2.07/0.98  --sat_fm_prep                           false
% 2.07/0.98  --sat_fm_uc_incr                        true
% 2.07/0.98  --sat_out_model                         small
% 2.07/0.98  --sat_out_clauses                       false
% 2.07/0.98  
% 2.07/0.98  ------ QBF Options
% 2.07/0.98  
% 2.07/0.98  --qbf_mode                              false
% 2.07/0.98  --qbf_elim_univ                         false
% 2.07/0.98  --qbf_dom_inst                          none
% 2.07/0.98  --qbf_dom_pre_inst                      false
% 2.07/0.98  --qbf_sk_in                             false
% 2.07/0.98  --qbf_pred_elim                         true
% 2.07/0.98  --qbf_split                             512
% 2.07/0.98  
% 2.07/0.98  ------ BMC1 Options
% 2.07/0.98  
% 2.07/0.98  --bmc1_incremental                      false
% 2.07/0.98  --bmc1_axioms                           reachable_all
% 2.07/0.98  --bmc1_min_bound                        0
% 2.07/0.98  --bmc1_max_bound                        -1
% 2.07/0.98  --bmc1_max_bound_default                -1
% 2.07/0.98  --bmc1_symbol_reachability              true
% 2.07/0.98  --bmc1_property_lemmas                  false
% 2.07/0.98  --bmc1_k_induction                      false
% 2.07/0.98  --bmc1_non_equiv_states                 false
% 2.07/0.98  --bmc1_deadlock                         false
% 2.07/0.98  --bmc1_ucm                              false
% 2.07/0.98  --bmc1_add_unsat_core                   none
% 2.07/0.98  --bmc1_unsat_core_children              false
% 2.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.98  --bmc1_out_stat                         full
% 2.07/0.98  --bmc1_ground_init                      false
% 2.07/0.98  --bmc1_pre_inst_next_state              false
% 2.07/0.98  --bmc1_pre_inst_state                   false
% 2.07/0.98  --bmc1_pre_inst_reach_state             false
% 2.07/0.98  --bmc1_out_unsat_core                   false
% 2.07/0.98  --bmc1_aig_witness_out                  false
% 2.07/0.98  --bmc1_verbose                          false
% 2.07/0.98  --bmc1_dump_clauses_tptp                false
% 2.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.98  --bmc1_dump_file                        -
% 2.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.98  --bmc1_ucm_extend_mode                  1
% 2.07/0.98  --bmc1_ucm_init_mode                    2
% 2.07/0.98  --bmc1_ucm_cone_mode                    none
% 2.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.98  --bmc1_ucm_relax_model                  4
% 2.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.98  --bmc1_ucm_layered_model                none
% 2.07/0.98  --bmc1_ucm_max_lemma_size               10
% 2.07/0.98  
% 2.07/0.98  ------ AIG Options
% 2.07/0.98  
% 2.07/0.98  --aig_mode                              false
% 2.07/0.98  
% 2.07/0.98  ------ Instantiation Options
% 2.07/0.98  
% 2.07/0.98  --instantiation_flag                    true
% 2.07/0.98  --inst_sos_flag                         false
% 2.07/0.98  --inst_sos_phase                        true
% 2.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.98  --inst_lit_sel_side                     none
% 2.07/0.98  --inst_solver_per_active                1400
% 2.07/0.98  --inst_solver_calls_frac                1.
% 2.07/0.98  --inst_passive_queue_type               priority_queues
% 2.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.98  --inst_passive_queues_freq              [25;2]
% 2.07/0.98  --inst_dismatching                      true
% 2.07/0.98  --inst_eager_unprocessed_to_passive     true
% 2.07/0.98  --inst_prop_sim_given                   true
% 2.07/0.98  --inst_prop_sim_new                     false
% 2.07/0.98  --inst_subs_new                         false
% 2.07/0.98  --inst_eq_res_simp                      false
% 2.07/0.98  --inst_subs_given                       false
% 2.07/0.98  --inst_orphan_elimination               true
% 2.07/0.98  --inst_learning_loop_flag               true
% 2.07/0.98  --inst_learning_start                   3000
% 2.07/0.98  --inst_learning_factor                  2
% 2.07/0.98  --inst_start_prop_sim_after_learn       3
% 2.07/0.98  --inst_sel_renew                        solver
% 2.07/0.98  --inst_lit_activity_flag                true
% 2.07/0.98  --inst_restr_to_given                   false
% 2.07/0.98  --inst_activity_threshold               500
% 2.07/0.98  --inst_out_proof                        true
% 2.07/0.98  
% 2.07/0.98  ------ Resolution Options
% 2.07/0.98  
% 2.07/0.98  --resolution_flag                       false
% 2.07/0.98  --res_lit_sel                           adaptive
% 2.07/0.98  --res_lit_sel_side                      none
% 2.07/0.98  --res_ordering                          kbo
% 2.07/0.98  --res_to_prop_solver                    active
% 2.07/0.98  --res_prop_simpl_new                    false
% 2.07/0.98  --res_prop_simpl_given                  true
% 2.07/0.98  --res_passive_queue_type                priority_queues
% 2.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.98  --res_passive_queues_freq               [15;5]
% 2.07/0.98  --res_forward_subs                      full
% 2.07/0.98  --res_backward_subs                     full
% 2.07/0.98  --res_forward_subs_resolution           true
% 2.07/0.98  --res_backward_subs_resolution          true
% 2.07/0.98  --res_orphan_elimination                true
% 2.07/0.98  --res_time_limit                        2.
% 2.07/0.98  --res_out_proof                         true
% 2.07/0.98  
% 2.07/0.98  ------ Superposition Options
% 2.07/0.98  
% 2.07/0.98  --superposition_flag                    true
% 2.07/0.98  --sup_passive_queue_type                priority_queues
% 2.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.98  --demod_completeness_check              fast
% 2.07/0.98  --demod_use_ground                      true
% 2.07/0.98  --sup_to_prop_solver                    passive
% 2.07/0.98  --sup_prop_simpl_new                    true
% 2.07/0.98  --sup_prop_simpl_given                  true
% 2.07/0.98  --sup_fun_splitting                     false
% 2.07/0.98  --sup_smt_interval                      50000
% 2.07/0.98  
% 2.07/0.98  ------ Superposition Simplification Setup
% 2.07/0.98  
% 2.07/0.98  --sup_indices_passive                   []
% 2.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_full_bw                           [BwDemod]
% 2.07/0.98  --sup_immed_triv                        [TrivRules]
% 2.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_immed_bw_main                     []
% 2.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.98  
% 2.07/0.98  ------ Combination Options
% 2.07/0.98  
% 2.07/0.98  --comb_res_mult                         3
% 2.07/0.98  --comb_sup_mult                         2
% 2.07/0.98  --comb_inst_mult                        10
% 2.07/0.98  
% 2.07/0.98  ------ Debug Options
% 2.07/0.98  
% 2.07/0.98  --dbg_backtrace                         false
% 2.07/0.98  --dbg_dump_prop_clauses                 false
% 2.07/0.98  --dbg_dump_prop_clauses_file            -
% 2.07/0.98  --dbg_out_stat                          false
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  ------ Proving...
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  % SZS status Theorem for theBenchmark.p
% 2.07/0.98  
% 2.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.07/0.98  
% 2.07/0.98  fof(f11,axiom,(
% 2.07/0.98    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f61,plain,(
% 2.07/0.98    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f11])).
% 2.07/0.98  
% 2.07/0.98  fof(f7,axiom,(
% 2.07/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f47,plain,(
% 2.07/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.07/0.98    inference(cnf_transformation,[],[f7])).
% 2.07/0.98  
% 2.07/0.98  fof(f13,axiom,(
% 2.07/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f63,plain,(
% 2.07/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f13])).
% 2.07/0.98  
% 2.07/0.98  fof(f75,plain,(
% 2.07/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1)) )),
% 2.07/0.98    inference(definition_unfolding,[],[f61,f47,f63,f63])).
% 2.07/0.98  
% 2.07/0.98  fof(f20,conjecture,(
% 2.07/0.98    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f21,negated_conjecture,(
% 2.07/0.98    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 2.07/0.98    inference(negated_conjecture,[],[f20])).
% 2.07/0.98  
% 2.07/0.98  fof(f25,plain,(
% 2.07/0.98    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 2.07/0.98    inference(ennf_transformation,[],[f21])).
% 2.07/0.98  
% 2.07/0.98  fof(f37,plain,(
% 2.07/0.98    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 2.07/0.98    introduced(choice_axiom,[])).
% 2.07/0.98  
% 2.07/0.98  fof(f38,plain,(
% 2.07/0.98    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 2.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f37])).
% 2.07/0.98  
% 2.07/0.98  fof(f70,plain,(
% 2.07/0.98    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 2.07/0.98    inference(cnf_transformation,[],[f38])).
% 2.07/0.98  
% 2.07/0.98  fof(f93,plain,(
% 2.07/0.98    k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) = k2_tarski(sK2,sK2)),
% 2.07/0.98    inference(definition_unfolding,[],[f70,f47,f63,f63,f63])).
% 2.07/0.98  
% 2.07/0.98  fof(f14,axiom,(
% 2.07/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f64,plain,(
% 2.07/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f14])).
% 2.07/0.98  
% 2.07/0.98  fof(f15,axiom,(
% 2.07/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f65,plain,(
% 2.07/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f15])).
% 2.07/0.98  
% 2.07/0.98  fof(f16,axiom,(
% 2.07/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f66,plain,(
% 2.07/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f16])).
% 2.07/0.98  
% 2.07/0.98  fof(f17,axiom,(
% 2.07/0.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f67,plain,(
% 2.07/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f17])).
% 2.07/0.98  
% 2.07/0.98  fof(f18,axiom,(
% 2.07/0.98    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f68,plain,(
% 2.07/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f18])).
% 2.07/0.98  
% 2.07/0.98  fof(f72,plain,(
% 2.07/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.07/0.98    inference(definition_unfolding,[],[f67,f68])).
% 2.07/0.98  
% 2.07/0.98  fof(f73,plain,(
% 2.07/0.98    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.07/0.98    inference(definition_unfolding,[],[f66,f72])).
% 2.07/0.98  
% 2.07/0.98  fof(f74,plain,(
% 2.07/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.07/0.98    inference(definition_unfolding,[],[f65,f73])).
% 2.07/0.98  
% 2.07/0.98  fof(f92,plain,(
% 2.07/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.07/0.98    inference(definition_unfolding,[],[f64,f74])).
% 2.07/0.98  
% 2.07/0.98  fof(f9,axiom,(
% 2.07/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f24,plain,(
% 2.07/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.07/0.98    inference(ennf_transformation,[],[f9])).
% 2.07/0.98  
% 2.07/0.98  fof(f28,plain,(
% 2.07/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.07/0.98    inference(nnf_transformation,[],[f24])).
% 2.07/0.98  
% 2.07/0.98  fof(f29,plain,(
% 2.07/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.07/0.98    inference(flattening,[],[f28])).
% 2.07/0.98  
% 2.07/0.98  fof(f30,plain,(
% 2.07/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.07/0.98    inference(rectify,[],[f29])).
% 2.07/0.98  
% 2.07/0.98  fof(f31,plain,(
% 2.07/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 2.07/0.98    introduced(choice_axiom,[])).
% 2.07/0.98  
% 2.07/0.98  fof(f32,plain,(
% 2.07/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.07/0.98  
% 2.07/0.98  fof(f52,plain,(
% 2.07/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.07/0.98    inference(cnf_transformation,[],[f32])).
% 2.07/0.98  
% 2.07/0.98  fof(f84,plain,(
% 2.07/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.07/0.98    inference(definition_unfolding,[],[f52,f74])).
% 2.07/0.98  
% 2.07/0.98  fof(f96,plain,(
% 2.07/0.98    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 2.07/0.98    inference(equality_resolution,[],[f84])).
% 2.07/0.98  
% 2.07/0.98  fof(f97,plain,(
% 2.07/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 2.07/0.98    inference(equality_resolution,[],[f96])).
% 2.07/0.98  
% 2.07/0.98  fof(f10,axiom,(
% 2.07/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f33,plain,(
% 2.07/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.07/0.98    inference(nnf_transformation,[],[f10])).
% 2.07/0.98  
% 2.07/0.98  fof(f34,plain,(
% 2.07/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.07/0.98    inference(rectify,[],[f33])).
% 2.07/0.98  
% 2.07/0.98  fof(f35,plain,(
% 2.07/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 2.07/0.98    introduced(choice_axiom,[])).
% 2.07/0.98  
% 2.07/0.98  fof(f36,plain,(
% 2.07/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 2.07/0.98  
% 2.07/0.98  fof(f57,plain,(
% 2.07/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.07/0.98    inference(cnf_transformation,[],[f36])).
% 2.07/0.98  
% 2.07/0.98  fof(f91,plain,(
% 2.07/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 2.07/0.98    inference(definition_unfolding,[],[f57,f63])).
% 2.07/0.98  
% 2.07/0.98  fof(f105,plain,(
% 2.07/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 2.07/0.98    inference(equality_resolution,[],[f91])).
% 2.07/0.98  
% 2.07/0.98  fof(f58,plain,(
% 2.07/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.07/0.98    inference(cnf_transformation,[],[f36])).
% 2.07/0.98  
% 2.07/0.98  fof(f90,plain,(
% 2.07/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 2.07/0.98    inference(definition_unfolding,[],[f58,f63])).
% 2.07/0.98  
% 2.07/0.98  fof(f103,plain,(
% 2.07/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 2.07/0.98    inference(equality_resolution,[],[f90])).
% 2.07/0.98  
% 2.07/0.98  fof(f104,plain,(
% 2.07/0.98    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 2.07/0.98    inference(equality_resolution,[],[f103])).
% 2.07/0.98  
% 2.07/0.98  fof(f71,plain,(
% 2.07/0.98    sK2 != sK3),
% 2.07/0.98    inference(cnf_transformation,[],[f38])).
% 2.07/0.98  
% 2.07/0.98  cnf(c_0,plain,
% 2.07/0.98      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 2.07/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_25,negated_conjecture,
% 2.07/0.98      ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) = k2_tarski(sK2,sK2) ),
% 2.07/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2514,plain,
% 2.07/0.98      ( k2_tarski(sK2,sK3) = k2_tarski(sK2,sK2) ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_0,c_25]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_22,plain,
% 2.07/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 2.07/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_14,plain,
% 2.07/0.98      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 2.07/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1595,plain,
% 2.07/0.98      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_5212,plain,
% 2.07/0.98      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_22,c_1595]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_5216,plain,
% 2.07/0.98      ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_2514,c_5212]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_21,plain,
% 2.07/0.98      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 2.07/0.98      inference(cnf_transformation,[],[f105]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1785,plain,
% 2.07/0.98      ( ~ r2_hidden(sK3,k2_tarski(X0,X0)) | sK3 = X0 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1786,plain,
% 2.07/0.98      ( sK3 = X0 | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1788,plain,
% 2.07/0.98      ( sK3 = sK2 | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_1786]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1350,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1733,plain,
% 2.07/0.98      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_1350]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1734,plain,
% 2.07/0.98      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_1733]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_20,plain,
% 2.07/0.98      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 2.07/0.98      inference(cnf_transformation,[],[f104]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_32,plain,
% 2.07/0.98      ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_29,plain,
% 2.07/0.98      ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2)) | sK2 = sK2 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_24,negated_conjecture,
% 2.07/0.98      ( sK2 != sK3 ),
% 2.07/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(contradiction,plain,
% 2.07/0.98      ( $false ),
% 2.07/0.98      inference(minisat,
% 2.07/0.98                [status(thm)],
% 2.07/0.99                [c_5216,c_1788,c_1734,c_32,c_29,c_24]) ).
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.07/0.99  
% 2.07/0.99  ------                               Statistics
% 2.07/0.99  
% 2.07/0.99  ------ General
% 2.07/0.99  
% 2.07/0.99  abstr_ref_over_cycles:                  0
% 2.07/0.99  abstr_ref_under_cycles:                 0
% 2.07/0.99  gc_basic_clause_elim:                   0
% 2.07/0.99  forced_gc_time:                         0
% 2.07/0.99  parsing_time:                           0.008
% 2.07/0.99  unif_index_cands_time:                  0.
% 2.07/0.99  unif_index_add_time:                    0.
% 2.07/0.99  orderings_time:                         0.
% 2.07/0.99  out_proof_time:                         0.007
% 2.07/0.99  total_time:                             0.196
% 2.07/0.99  num_of_symbols:                         42
% 2.07/0.99  num_of_terms:                           6935
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing
% 2.07/0.99  
% 2.07/0.99  num_of_splits:                          0
% 2.07/0.99  num_of_split_atoms:                     0
% 2.07/0.99  num_of_reused_defs:                     0
% 2.07/0.99  num_eq_ax_congr_red:                    69
% 2.07/0.99  num_of_sem_filtered_clauses:            1
% 2.07/0.99  num_of_subtypes:                        0
% 2.07/0.99  monotx_restored_types:                  0
% 2.07/0.99  sat_num_of_epr_types:                   0
% 2.07/0.99  sat_num_of_non_cyclic_types:            0
% 2.07/0.99  sat_guarded_non_collapsed_types:        0
% 2.07/0.99  num_pure_diseq_elim:                    0
% 2.07/0.99  simp_replaced_by:                       0
% 2.07/0.99  res_preprocessed:                       113
% 2.07/0.99  prep_upred:                             0
% 2.07/0.99  prep_unflattend:                        72
% 2.07/0.99  smt_new_axioms:                         0
% 2.07/0.99  pred_elim_cands:                        2
% 2.07/0.99  pred_elim:                              0
% 2.07/0.99  pred_elim_cl:                           0
% 2.07/0.99  pred_elim_cycles:                       2
% 2.07/0.99  merged_defs:                            0
% 2.07/0.99  merged_defs_ncl:                        0
% 2.07/0.99  bin_hyper_res:                          0
% 2.07/0.99  prep_cycles:                            4
% 2.07/0.99  pred_elim_time:                         0.013
% 2.07/0.99  splitting_time:                         0.
% 2.07/0.99  sem_filter_time:                        0.
% 2.07/0.99  monotx_time:                            0.
% 2.07/0.99  subtype_inf_time:                       0.
% 2.07/0.99  
% 2.07/0.99  ------ Problem properties
% 2.07/0.99  
% 2.07/0.99  clauses:                                25
% 2.07/0.99  conjectures:                            2
% 2.07/0.99  epr:                                    3
% 2.07/0.99  horn:                                   22
% 2.07/0.99  ground:                                 2
% 2.07/0.99  unary:                                  15
% 2.07/0.99  binary:                                 2
% 2.07/0.99  lits:                                   46
% 2.07/0.99  lits_eq:                                30
% 2.07/0.99  fd_pure:                                0
% 2.07/0.99  fd_pseudo:                              0
% 2.07/0.99  fd_cond:                                0
% 2.07/0.99  fd_pseudo_cond:                         7
% 2.07/0.99  ac_symbols:                             0
% 2.07/0.99  
% 2.07/0.99  ------ Propositional Solver
% 2.07/0.99  
% 2.07/0.99  prop_solver_calls:                      27
% 2.07/0.99  prop_fast_solver_calls:                 710
% 2.07/0.99  smt_solver_calls:                       0
% 2.07/0.99  smt_fast_solver_calls:                  0
% 2.07/0.99  prop_num_of_clauses:                    1792
% 2.07/0.99  prop_preprocess_simplified:             6837
% 2.07/0.99  prop_fo_subsumed:                       0
% 2.07/0.99  prop_solver_time:                       0.
% 2.07/0.99  smt_solver_time:                        0.
% 2.07/0.99  smt_fast_solver_time:                   0.
% 2.07/0.99  prop_fast_solver_time:                  0.
% 2.07/0.99  prop_unsat_core_time:                   0.
% 2.07/0.99  
% 2.07/0.99  ------ QBF
% 2.07/0.99  
% 2.07/0.99  qbf_q_res:                              0
% 2.07/0.99  qbf_num_tautologies:                    0
% 2.07/0.99  qbf_prep_cycles:                        0
% 2.07/0.99  
% 2.07/0.99  ------ BMC1
% 2.07/0.99  
% 2.07/0.99  bmc1_current_bound:                     -1
% 2.07/0.99  bmc1_last_solved_bound:                 -1
% 2.07/0.99  bmc1_unsat_core_size:                   -1
% 2.07/0.99  bmc1_unsat_core_parents_size:           -1
% 2.07/0.99  bmc1_merge_next_fun:                    0
% 2.07/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.07/0.99  
% 2.07/0.99  ------ Instantiation
% 2.07/0.99  
% 2.07/0.99  inst_num_of_clauses:                    581
% 2.07/0.99  inst_num_in_passive:                    387
% 2.07/0.99  inst_num_in_active:                     149
% 2.07/0.99  inst_num_in_unprocessed:                45
% 2.07/0.99  inst_num_of_loops:                      190
% 2.07/0.99  inst_num_of_learning_restarts:          0
% 2.07/0.99  inst_num_moves_active_passive:          40
% 2.07/0.99  inst_lit_activity:                      0
% 2.07/0.99  inst_lit_activity_moves:                0
% 2.07/0.99  inst_num_tautologies:                   0
% 2.07/0.99  inst_num_prop_implied:                  0
% 2.07/0.99  inst_num_existing_simplified:           0
% 2.07/0.99  inst_num_eq_res_simplified:             0
% 2.07/0.99  inst_num_child_elim:                    0
% 2.07/0.99  inst_num_of_dismatching_blockings:      148
% 2.07/0.99  inst_num_of_non_proper_insts:           364
% 2.07/0.99  inst_num_of_duplicates:                 0
% 2.07/0.99  inst_inst_num_from_inst_to_res:         0
% 2.07/0.99  inst_dismatching_checking_time:         0.
% 2.07/0.99  
% 2.07/0.99  ------ Resolution
% 2.07/0.99  
% 2.07/0.99  res_num_of_clauses:                     0
% 2.07/0.99  res_num_in_passive:                     0
% 2.07/0.99  res_num_in_active:                      0
% 2.07/0.99  res_num_of_loops:                       117
% 2.07/0.99  res_forward_subset_subsumed:            44
% 2.07/0.99  res_backward_subset_subsumed:           0
% 2.07/0.99  res_forward_subsumed:                   0
% 2.07/0.99  res_backward_subsumed:                  0
% 2.07/0.99  res_forward_subsumption_resolution:     0
% 2.07/0.99  res_backward_subsumption_resolution:    0
% 2.07/0.99  res_clause_to_clause_subsumption:       525
% 2.07/0.99  res_orphan_elimination:                 0
% 2.07/0.99  res_tautology_del:                      14
% 2.07/0.99  res_num_eq_res_simplified:              0
% 2.07/0.99  res_num_sel_changes:                    0
% 2.07/0.99  res_moves_from_active_to_pass:          0
% 2.07/0.99  
% 2.07/0.99  ------ Superposition
% 2.07/0.99  
% 2.07/0.99  sup_time_total:                         0.
% 2.07/0.99  sup_time_generating:                    0.
% 2.07/0.99  sup_time_sim_full:                      0.
% 2.07/0.99  sup_time_sim_immed:                     0.
% 2.07/0.99  
% 2.07/0.99  sup_num_of_clauses:                     117
% 2.07/0.99  sup_num_in_active:                      37
% 2.07/0.99  sup_num_in_passive:                     80
% 2.07/0.99  sup_num_of_loops:                       37
% 2.07/0.99  sup_fw_superposition:                   66
% 2.07/0.99  sup_bw_superposition:                   86
% 2.07/0.99  sup_immediate_simplified:               37
% 2.07/0.99  sup_given_eliminated:                   1
% 2.07/0.99  comparisons_done:                       0
% 2.07/0.99  comparisons_avoided:                    2
% 2.07/0.99  
% 2.07/0.99  ------ Simplifications
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  sim_fw_subset_subsumed:                 0
% 2.07/0.99  sim_bw_subset_subsumed:                 0
% 2.07/0.99  sim_fw_subsumed:                        4
% 2.07/0.99  sim_bw_subsumed:                        3
% 2.07/0.99  sim_fw_subsumption_res:                 0
% 2.07/0.99  sim_bw_subsumption_res:                 0
% 2.07/0.99  sim_tautology_del:                      0
% 2.07/0.99  sim_eq_tautology_del:                   1
% 2.07/0.99  sim_eq_res_simp:                        0
% 2.07/0.99  sim_fw_demodulated:                     21
% 2.07/0.99  sim_bw_demodulated:                     4
% 2.07/0.99  sim_light_normalised:                   14
% 2.07/0.99  sim_joinable_taut:                      0
% 2.07/0.99  sim_joinable_simp:                      0
% 2.07/0.99  sim_ac_normalised:                      0
% 2.07/0.99  sim_smt_subsumption:                    0
% 2.07/0.99  
%------------------------------------------------------------------------------
