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
% DateTime   : Thu Dec  3 11:35:17 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 132 expanded)
%              Number of clauses        :   26 (  27 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  303 ( 738 expanded)
%              Number of equality atoms :  177 ( 467 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f64,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f65,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f64])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) )
   => ( sK2 != sK3
      & r2_hidden(sK3,sK4)
      & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( sK2 != sK3
    & r2_hidden(sK3,sK4)
    & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f23])).

fof(f45,plain,(
    k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f60,plain,(
    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f45,f33,f48,f49])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f34,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f34,f44])).

fof(f70,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f68,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f69,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f68])).

fof(f47,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_390,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1180,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_18,c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_397,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2898,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_397])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_396,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3497,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2898,c_396])).

cnf(c_6860,plain,
    ( r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_390,c_3497])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_445,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,X2))
    | sK3 = X0
    | sK3 = X2
    | sK3 = X1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_446,plain,
    ( sK3 = X0
    | sK3 = X1
    | sK3 = X2
    | r2_hidden(sK3,k2_enumset1(X0,X0,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_448,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_165,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_420,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_421,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_21,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6860,c_448,c_421,c_24,c_21,c_16,c_19])).

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
% 0.12/0.34  % DateTime   : Tue Dec  1 10:47:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.74/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/0.98  
% 3.74/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/0.98  
% 3.74/0.98  ------  iProver source info
% 3.74/0.98  
% 3.74/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.74/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/0.98  git: non_committed_changes: false
% 3.74/0.98  git: last_make_outside_of_git: false
% 3.74/0.98  
% 3.74/0.98  ------ 
% 3.74/0.98  
% 3.74/0.98  ------ Input Options
% 3.74/0.98  
% 3.74/0.98  --out_options                           all
% 3.74/0.98  --tptp_safe_out                         true
% 3.74/0.98  --problem_path                          ""
% 3.74/0.98  --include_path                          ""
% 3.74/0.98  --clausifier                            res/vclausify_rel
% 3.74/0.98  --clausifier_options                    ""
% 3.74/0.98  --stdin                                 false
% 3.74/0.98  --stats_out                             all
% 3.74/0.98  
% 3.74/0.98  ------ General Options
% 3.74/0.98  
% 3.74/0.98  --fof                                   false
% 3.74/0.98  --time_out_real                         305.
% 3.74/0.98  --time_out_virtual                      -1.
% 3.74/0.98  --symbol_type_check                     false
% 3.74/0.98  --clausify_out                          false
% 3.74/0.98  --sig_cnt_out                           false
% 3.74/0.98  --trig_cnt_out                          false
% 3.74/0.98  --trig_cnt_out_tolerance                1.
% 3.74/0.98  --trig_cnt_out_sk_spl                   false
% 3.74/0.98  --abstr_cl_out                          false
% 3.74/0.98  
% 3.74/0.98  ------ Global Options
% 3.74/0.98  
% 3.74/0.98  --schedule                              default
% 3.74/0.98  --add_important_lit                     false
% 3.74/0.98  --prop_solver_per_cl                    1000
% 3.74/0.98  --min_unsat_core                        false
% 3.74/0.98  --soft_assumptions                      false
% 3.74/0.98  --soft_lemma_size                       3
% 3.74/0.98  --prop_impl_unit_size                   0
% 3.74/0.98  --prop_impl_unit                        []
% 3.74/0.98  --share_sel_clauses                     true
% 3.74/0.98  --reset_solvers                         false
% 3.74/0.98  --bc_imp_inh                            [conj_cone]
% 3.74/0.98  --conj_cone_tolerance                   3.
% 3.74/0.98  --extra_neg_conj                        none
% 3.74/0.98  --large_theory_mode                     true
% 3.74/0.98  --prolific_symb_bound                   200
% 3.74/0.98  --lt_threshold                          2000
% 3.74/0.98  --clause_weak_htbl                      true
% 3.74/0.98  --gc_record_bc_elim                     false
% 3.74/0.98  
% 3.74/0.98  ------ Preprocessing Options
% 3.74/0.98  
% 3.74/0.98  --preprocessing_flag                    true
% 3.74/0.98  --time_out_prep_mult                    0.1
% 3.74/0.98  --splitting_mode                        input
% 3.74/0.98  --splitting_grd                         true
% 3.74/0.98  --splitting_cvd                         false
% 3.74/0.98  --splitting_cvd_svl                     false
% 3.74/0.98  --splitting_nvd                         32
% 3.74/0.98  --sub_typing                            true
% 3.74/0.98  --prep_gs_sim                           true
% 3.74/0.98  --prep_unflatten                        true
% 3.74/0.98  --prep_res_sim                          true
% 3.74/0.98  --prep_upred                            true
% 3.74/0.98  --prep_sem_filter                       exhaustive
% 3.74/0.98  --prep_sem_filter_out                   false
% 3.74/0.98  --pred_elim                             true
% 3.74/0.98  --res_sim_input                         true
% 3.74/0.98  --eq_ax_congr_red                       true
% 3.74/0.98  --pure_diseq_elim                       true
% 3.74/0.98  --brand_transform                       false
% 3.74/0.98  --non_eq_to_eq                          false
% 3.74/0.98  --prep_def_merge                        true
% 3.74/0.98  --prep_def_merge_prop_impl              false
% 3.74/0.98  --prep_def_merge_mbd                    true
% 3.74/0.98  --prep_def_merge_tr_red                 false
% 3.74/0.98  --prep_def_merge_tr_cl                  false
% 3.74/0.98  --smt_preprocessing                     true
% 3.74/0.98  --smt_ac_axioms                         fast
% 3.74/0.98  --preprocessed_out                      false
% 3.74/0.98  --preprocessed_stats                    false
% 3.74/0.98  
% 3.74/0.98  ------ Abstraction refinement Options
% 3.74/0.98  
% 3.74/0.98  --abstr_ref                             []
% 3.74/0.98  --abstr_ref_prep                        false
% 3.74/0.98  --abstr_ref_until_sat                   false
% 3.74/0.98  --abstr_ref_sig_restrict                funpre
% 3.74/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/0.98  --abstr_ref_under                       []
% 3.74/0.98  
% 3.74/0.98  ------ SAT Options
% 3.74/0.98  
% 3.74/0.98  --sat_mode                              false
% 3.74/0.98  --sat_fm_restart_options                ""
% 3.74/0.98  --sat_gr_def                            false
% 3.74/0.98  --sat_epr_types                         true
% 3.74/0.98  --sat_non_cyclic_types                  false
% 3.74/0.98  --sat_finite_models                     false
% 3.74/0.98  --sat_fm_lemmas                         false
% 3.74/0.98  --sat_fm_prep                           false
% 3.74/0.98  --sat_fm_uc_incr                        true
% 3.74/0.98  --sat_out_model                         small
% 3.74/0.98  --sat_out_clauses                       false
% 3.74/0.98  
% 3.74/0.98  ------ QBF Options
% 3.74/0.98  
% 3.74/0.98  --qbf_mode                              false
% 3.74/0.98  --qbf_elim_univ                         false
% 3.74/0.98  --qbf_dom_inst                          none
% 3.74/0.98  --qbf_dom_pre_inst                      false
% 3.74/0.98  --qbf_sk_in                             false
% 3.74/0.98  --qbf_pred_elim                         true
% 3.74/0.98  --qbf_split                             512
% 3.74/0.98  
% 3.74/0.98  ------ BMC1 Options
% 3.74/0.98  
% 3.74/0.98  --bmc1_incremental                      false
% 3.74/0.98  --bmc1_axioms                           reachable_all
% 3.74/0.98  --bmc1_min_bound                        0
% 3.74/0.98  --bmc1_max_bound                        -1
% 3.74/0.98  --bmc1_max_bound_default                -1
% 3.74/0.98  --bmc1_symbol_reachability              true
% 3.74/0.98  --bmc1_property_lemmas                  false
% 3.74/0.98  --bmc1_k_induction                      false
% 3.74/0.98  --bmc1_non_equiv_states                 false
% 3.74/0.98  --bmc1_deadlock                         false
% 3.74/0.98  --bmc1_ucm                              false
% 3.74/0.98  --bmc1_add_unsat_core                   none
% 3.74/0.98  --bmc1_unsat_core_children              false
% 3.74/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/0.98  --bmc1_out_stat                         full
% 3.74/0.98  --bmc1_ground_init                      false
% 3.74/0.98  --bmc1_pre_inst_next_state              false
% 3.74/0.98  --bmc1_pre_inst_state                   false
% 3.74/0.98  --bmc1_pre_inst_reach_state             false
% 3.74/0.98  --bmc1_out_unsat_core                   false
% 3.74/0.98  --bmc1_aig_witness_out                  false
% 3.74/0.98  --bmc1_verbose                          false
% 3.74/0.98  --bmc1_dump_clauses_tptp                false
% 3.74/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.74/0.98  --bmc1_dump_file                        -
% 3.74/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.74/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.74/0.98  --bmc1_ucm_extend_mode                  1
% 3.74/0.98  --bmc1_ucm_init_mode                    2
% 3.74/0.98  --bmc1_ucm_cone_mode                    none
% 3.74/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.74/0.98  --bmc1_ucm_relax_model                  4
% 3.74/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.74/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/0.98  --bmc1_ucm_layered_model                none
% 3.74/0.98  --bmc1_ucm_max_lemma_size               10
% 3.74/0.98  
% 3.74/0.98  ------ AIG Options
% 3.74/0.98  
% 3.74/0.98  --aig_mode                              false
% 3.74/0.98  
% 3.74/0.98  ------ Instantiation Options
% 3.74/0.98  
% 3.74/0.98  --instantiation_flag                    true
% 3.74/0.98  --inst_sos_flag                         true
% 3.74/0.98  --inst_sos_phase                        true
% 3.74/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/0.98  --inst_lit_sel_side                     num_symb
% 3.74/0.98  --inst_solver_per_active                1400
% 3.74/0.98  --inst_solver_calls_frac                1.
% 3.74/0.98  --inst_passive_queue_type               priority_queues
% 3.74/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/0.98  --inst_passive_queues_freq              [25;2]
% 3.74/0.98  --inst_dismatching                      true
% 3.74/0.98  --inst_eager_unprocessed_to_passive     true
% 3.74/0.98  --inst_prop_sim_given                   true
% 3.74/0.98  --inst_prop_sim_new                     false
% 3.74/0.98  --inst_subs_new                         false
% 3.74/0.98  --inst_eq_res_simp                      false
% 3.74/0.98  --inst_subs_given                       false
% 3.74/0.98  --inst_orphan_elimination               true
% 3.74/0.98  --inst_learning_loop_flag               true
% 3.74/0.98  --inst_learning_start                   3000
% 3.74/0.98  --inst_learning_factor                  2
% 3.74/0.98  --inst_start_prop_sim_after_learn       3
% 3.74/0.98  --inst_sel_renew                        solver
% 3.74/0.98  --inst_lit_activity_flag                true
% 3.74/0.98  --inst_restr_to_given                   false
% 3.74/0.98  --inst_activity_threshold               500
% 3.74/0.98  --inst_out_proof                        true
% 3.74/0.98  
% 3.74/0.98  ------ Resolution Options
% 3.74/0.98  
% 3.74/0.98  --resolution_flag                       true
% 3.74/0.98  --res_lit_sel                           adaptive
% 3.74/0.98  --res_lit_sel_side                      none
% 3.74/0.98  --res_ordering                          kbo
% 3.74/0.98  --res_to_prop_solver                    active
% 3.74/0.98  --res_prop_simpl_new                    false
% 3.74/0.98  --res_prop_simpl_given                  true
% 3.74/0.98  --res_passive_queue_type                priority_queues
% 3.74/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/0.98  --res_passive_queues_freq               [15;5]
% 3.74/0.98  --res_forward_subs                      full
% 3.74/0.98  --res_backward_subs                     full
% 3.74/0.98  --res_forward_subs_resolution           true
% 3.74/0.98  --res_backward_subs_resolution          true
% 3.74/0.98  --res_orphan_elimination                true
% 3.74/0.98  --res_time_limit                        2.
% 3.74/0.98  --res_out_proof                         true
% 3.74/0.98  
% 3.74/0.98  ------ Superposition Options
% 3.74/0.98  
% 3.74/0.98  --superposition_flag                    true
% 3.74/0.98  --sup_passive_queue_type                priority_queues
% 3.74/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.74/0.98  --demod_completeness_check              fast
% 3.74/0.98  --demod_use_ground                      true
% 3.74/0.98  --sup_to_prop_solver                    passive
% 3.74/0.98  --sup_prop_simpl_new                    true
% 3.74/0.98  --sup_prop_simpl_given                  true
% 3.74/0.98  --sup_fun_splitting                     true
% 3.74/0.98  --sup_smt_interval                      50000
% 3.74/0.98  
% 3.74/0.98  ------ Superposition Simplification Setup
% 3.74/0.98  
% 3.74/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.74/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.74/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.74/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.74/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.74/0.98  --sup_immed_triv                        [TrivRules]
% 3.74/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.98  --sup_immed_bw_main                     []
% 3.74/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.74/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.98  --sup_input_bw                          []
% 3.74/0.98  
% 3.74/0.98  ------ Combination Options
% 3.74/0.98  
% 3.74/0.98  --comb_res_mult                         3
% 3.74/0.98  --comb_sup_mult                         2
% 3.74/0.98  --comb_inst_mult                        10
% 3.74/0.98  
% 3.74/0.98  ------ Debug Options
% 3.74/0.98  
% 3.74/0.98  --dbg_backtrace                         false
% 3.74/0.98  --dbg_dump_prop_clauses                 false
% 3.74/0.98  --dbg_dump_prop_clauses_file            -
% 3.74/0.98  --dbg_out_stat                          false
% 3.74/0.98  ------ Parsing...
% 3.74/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/0.98  
% 3.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.74/0.98  
% 3.74/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/0.98  
% 3.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.98  ------ Proving...
% 3.74/0.98  ------ Problem Properties 
% 3.74/0.98  
% 3.74/0.98  
% 3.74/0.98  clauses                                 19
% 3.74/0.98  conjectures                             3
% 3.74/0.98  EPR                                     2
% 3.74/0.98  Horn                                    13
% 3.74/0.98  unary                                   8
% 3.74/0.98  binary                                  2
% 3.74/0.98  lits                                    43
% 3.74/0.98  lits eq                                 20
% 3.74/0.98  fd_pure                                 0
% 3.74/0.98  fd_pseudo                               0
% 3.74/0.98  fd_cond                                 0
% 3.74/0.98  fd_pseudo_cond                          7
% 3.74/0.98  AC symbols                              0
% 3.74/0.98  
% 3.74/0.98  ------ Schedule dynamic 5 is on 
% 3.74/0.98  
% 3.74/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.74/0.98  
% 3.74/0.98  
% 3.74/0.98  ------ 
% 3.74/0.98  Current options:
% 3.74/0.98  ------ 
% 3.74/0.98  
% 3.74/0.98  ------ Input Options
% 3.74/0.98  
% 3.74/0.98  --out_options                           all
% 3.74/0.98  --tptp_safe_out                         true
% 3.74/0.98  --problem_path                          ""
% 3.74/0.98  --include_path                          ""
% 3.74/0.98  --clausifier                            res/vclausify_rel
% 3.74/0.98  --clausifier_options                    ""
% 3.74/0.98  --stdin                                 false
% 3.74/0.98  --stats_out                             all
% 3.74/0.98  
% 3.74/0.98  ------ General Options
% 3.74/0.98  
% 3.74/0.98  --fof                                   false
% 3.74/0.98  --time_out_real                         305.
% 3.74/0.98  --time_out_virtual                      -1.
% 3.74/0.98  --symbol_type_check                     false
% 3.74/0.99  --clausify_out                          false
% 3.74/0.99  --sig_cnt_out                           false
% 3.74/0.99  --trig_cnt_out                          false
% 3.74/0.99  --trig_cnt_out_tolerance                1.
% 3.74/0.99  --trig_cnt_out_sk_spl                   false
% 3.74/0.99  --abstr_cl_out                          false
% 3.74/0.99  
% 3.74/0.99  ------ Global Options
% 3.74/0.99  
% 3.74/0.99  --schedule                              default
% 3.74/0.99  --add_important_lit                     false
% 3.74/0.99  --prop_solver_per_cl                    1000
% 3.74/0.99  --min_unsat_core                        false
% 3.74/0.99  --soft_assumptions                      false
% 3.74/0.99  --soft_lemma_size                       3
% 3.74/0.99  --prop_impl_unit_size                   0
% 3.74/0.99  --prop_impl_unit                        []
% 3.74/0.99  --share_sel_clauses                     true
% 3.74/0.99  --reset_solvers                         false
% 3.74/0.99  --bc_imp_inh                            [conj_cone]
% 3.74/0.99  --conj_cone_tolerance                   3.
% 3.74/0.99  --extra_neg_conj                        none
% 3.74/0.99  --large_theory_mode                     true
% 3.74/0.99  --prolific_symb_bound                   200
% 3.74/0.99  --lt_threshold                          2000
% 3.74/0.99  --clause_weak_htbl                      true
% 3.74/0.99  --gc_record_bc_elim                     false
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing Options
% 3.74/0.99  
% 3.74/0.99  --preprocessing_flag                    true
% 3.74/0.99  --time_out_prep_mult                    0.1
% 3.74/0.99  --splitting_mode                        input
% 3.74/0.99  --splitting_grd                         true
% 3.74/0.99  --splitting_cvd                         false
% 3.74/0.99  --splitting_cvd_svl                     false
% 3.74/0.99  --splitting_nvd                         32
% 3.74/0.99  --sub_typing                            true
% 3.74/0.99  --prep_gs_sim                           true
% 3.74/0.99  --prep_unflatten                        true
% 3.74/0.99  --prep_res_sim                          true
% 3.74/0.99  --prep_upred                            true
% 3.74/0.99  --prep_sem_filter                       exhaustive
% 3.74/0.99  --prep_sem_filter_out                   false
% 3.74/0.99  --pred_elim                             true
% 3.74/0.99  --res_sim_input                         true
% 3.74/0.99  --eq_ax_congr_red                       true
% 3.74/0.99  --pure_diseq_elim                       true
% 3.74/0.99  --brand_transform                       false
% 3.74/0.99  --non_eq_to_eq                          false
% 3.74/0.99  --prep_def_merge                        true
% 3.74/0.99  --prep_def_merge_prop_impl              false
% 3.74/0.99  --prep_def_merge_mbd                    true
% 3.74/0.99  --prep_def_merge_tr_red                 false
% 3.74/0.99  --prep_def_merge_tr_cl                  false
% 3.74/0.99  --smt_preprocessing                     true
% 3.74/0.99  --smt_ac_axioms                         fast
% 3.74/0.99  --preprocessed_out                      false
% 3.74/0.99  --preprocessed_stats                    false
% 3.74/0.99  
% 3.74/0.99  ------ Abstraction refinement Options
% 3.74/0.99  
% 3.74/0.99  --abstr_ref                             []
% 3.74/0.99  --abstr_ref_prep                        false
% 3.74/0.99  --abstr_ref_until_sat                   false
% 3.74/0.99  --abstr_ref_sig_restrict                funpre
% 3.74/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/0.99  --abstr_ref_under                       []
% 3.74/0.99  
% 3.74/0.99  ------ SAT Options
% 3.74/0.99  
% 3.74/0.99  --sat_mode                              false
% 3.74/0.99  --sat_fm_restart_options                ""
% 3.74/0.99  --sat_gr_def                            false
% 3.74/0.99  --sat_epr_types                         true
% 3.74/0.99  --sat_non_cyclic_types                  false
% 3.74/0.99  --sat_finite_models                     false
% 3.74/0.99  --sat_fm_lemmas                         false
% 3.74/0.99  --sat_fm_prep                           false
% 3.74/0.99  --sat_fm_uc_incr                        true
% 3.74/0.99  --sat_out_model                         small
% 3.74/0.99  --sat_out_clauses                       false
% 3.74/0.99  
% 3.74/0.99  ------ QBF Options
% 3.74/0.99  
% 3.74/0.99  --qbf_mode                              false
% 3.74/0.99  --qbf_elim_univ                         false
% 3.74/0.99  --qbf_dom_inst                          none
% 3.74/0.99  --qbf_dom_pre_inst                      false
% 3.74/0.99  --qbf_sk_in                             false
% 3.74/0.99  --qbf_pred_elim                         true
% 3.74/0.99  --qbf_split                             512
% 3.74/0.99  
% 3.74/0.99  ------ BMC1 Options
% 3.74/0.99  
% 3.74/0.99  --bmc1_incremental                      false
% 3.74/0.99  --bmc1_axioms                           reachable_all
% 3.74/0.99  --bmc1_min_bound                        0
% 3.74/0.99  --bmc1_max_bound                        -1
% 3.74/0.99  --bmc1_max_bound_default                -1
% 3.74/0.99  --bmc1_symbol_reachability              true
% 3.74/0.99  --bmc1_property_lemmas                  false
% 3.74/0.99  --bmc1_k_induction                      false
% 3.74/0.99  --bmc1_non_equiv_states                 false
% 3.74/0.99  --bmc1_deadlock                         false
% 3.74/0.99  --bmc1_ucm                              false
% 3.74/0.99  --bmc1_add_unsat_core                   none
% 3.74/0.99  --bmc1_unsat_core_children              false
% 3.74/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/0.99  --bmc1_out_stat                         full
% 3.74/0.99  --bmc1_ground_init                      false
% 3.74/0.99  --bmc1_pre_inst_next_state              false
% 3.74/0.99  --bmc1_pre_inst_state                   false
% 3.74/0.99  --bmc1_pre_inst_reach_state             false
% 3.74/0.99  --bmc1_out_unsat_core                   false
% 3.74/0.99  --bmc1_aig_witness_out                  false
% 3.74/0.99  --bmc1_verbose                          false
% 3.74/0.99  --bmc1_dump_clauses_tptp                false
% 3.74/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.74/0.99  --bmc1_dump_file                        -
% 3.74/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.74/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.74/0.99  --bmc1_ucm_extend_mode                  1
% 3.74/0.99  --bmc1_ucm_init_mode                    2
% 3.74/0.99  --bmc1_ucm_cone_mode                    none
% 3.74/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.74/0.99  --bmc1_ucm_relax_model                  4
% 3.74/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.74/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/0.99  --bmc1_ucm_layered_model                none
% 3.74/0.99  --bmc1_ucm_max_lemma_size               10
% 3.74/0.99  
% 3.74/0.99  ------ AIG Options
% 3.74/0.99  
% 3.74/0.99  --aig_mode                              false
% 3.74/0.99  
% 3.74/0.99  ------ Instantiation Options
% 3.74/0.99  
% 3.74/0.99  --instantiation_flag                    true
% 3.74/0.99  --inst_sos_flag                         true
% 3.74/0.99  --inst_sos_phase                        true
% 3.74/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/0.99  --inst_lit_sel_side                     none
% 3.74/0.99  --inst_solver_per_active                1400
% 3.74/0.99  --inst_solver_calls_frac                1.
% 3.74/0.99  --inst_passive_queue_type               priority_queues
% 3.74/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/0.99  --inst_passive_queues_freq              [25;2]
% 3.74/0.99  --inst_dismatching                      true
% 3.74/0.99  --inst_eager_unprocessed_to_passive     true
% 3.74/0.99  --inst_prop_sim_given                   true
% 3.74/0.99  --inst_prop_sim_new                     false
% 3.74/0.99  --inst_subs_new                         false
% 3.74/0.99  --inst_eq_res_simp                      false
% 3.74/0.99  --inst_subs_given                       false
% 3.74/0.99  --inst_orphan_elimination               true
% 3.74/0.99  --inst_learning_loop_flag               true
% 3.74/0.99  --inst_learning_start                   3000
% 3.74/0.99  --inst_learning_factor                  2
% 3.74/0.99  --inst_start_prop_sim_after_learn       3
% 3.74/0.99  --inst_sel_renew                        solver
% 3.74/0.99  --inst_lit_activity_flag                true
% 3.74/0.99  --inst_restr_to_given                   false
% 3.74/0.99  --inst_activity_threshold               500
% 3.74/0.99  --inst_out_proof                        true
% 3.74/0.99  
% 3.74/0.99  ------ Resolution Options
% 3.74/0.99  
% 3.74/0.99  --resolution_flag                       false
% 3.74/0.99  --res_lit_sel                           adaptive
% 3.74/0.99  --res_lit_sel_side                      none
% 3.74/0.99  --res_ordering                          kbo
% 3.74/0.99  --res_to_prop_solver                    active
% 3.74/0.99  --res_prop_simpl_new                    false
% 3.74/0.99  --res_prop_simpl_given                  true
% 3.74/0.99  --res_passive_queue_type                priority_queues
% 3.74/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/0.99  --res_passive_queues_freq               [15;5]
% 3.74/0.99  --res_forward_subs                      full
% 3.74/0.99  --res_backward_subs                     full
% 3.74/0.99  --res_forward_subs_resolution           true
% 3.74/0.99  --res_backward_subs_resolution          true
% 3.74/0.99  --res_orphan_elimination                true
% 3.74/0.99  --res_time_limit                        2.
% 3.74/0.99  --res_out_proof                         true
% 3.74/0.99  
% 3.74/0.99  ------ Superposition Options
% 3.74/0.99  
% 3.74/0.99  --superposition_flag                    true
% 3.74/0.99  --sup_passive_queue_type                priority_queues
% 3.74/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.74/0.99  --demod_completeness_check              fast
% 3.74/0.99  --demod_use_ground                      true
% 3.74/0.99  --sup_to_prop_solver                    passive
% 3.74/0.99  --sup_prop_simpl_new                    true
% 3.74/0.99  --sup_prop_simpl_given                  true
% 3.74/0.99  --sup_fun_splitting                     true
% 3.74/0.99  --sup_smt_interval                      50000
% 3.74/0.99  
% 3.74/0.99  ------ Superposition Simplification Setup
% 3.74/0.99  
% 3.74/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.74/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.74/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.74/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.74/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.74/0.99  --sup_immed_triv                        [TrivRules]
% 3.74/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.99  --sup_immed_bw_main                     []
% 3.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.99  --sup_input_bw                          []
% 3.74/0.99  
% 3.74/0.99  ------ Combination Options
% 3.74/0.99  
% 3.74/0.99  --comb_res_mult                         3
% 3.74/0.99  --comb_sup_mult                         2
% 3.74/0.99  --comb_inst_mult                        10
% 3.74/0.99  
% 3.74/0.99  ------ Debug Options
% 3.74/0.99  
% 3.74/0.99  --dbg_backtrace                         false
% 3.74/0.99  --dbg_dump_prop_clauses                 false
% 3.74/0.99  --dbg_dump_prop_clauses_file            -
% 3.74/0.99  --dbg_out_stat                          false
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS status Theorem for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  fof(f5,axiom,(
% 3.74/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f11,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.74/0.99    inference(ennf_transformation,[],[f5])).
% 3.74/0.99  
% 3.74/0.99  fof(f18,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.74/0.99    inference(nnf_transformation,[],[f11])).
% 3.74/0.99  
% 3.74/0.99  fof(f19,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.74/0.99    inference(flattening,[],[f18])).
% 3.74/0.99  
% 3.74/0.99  fof(f20,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.74/0.99    inference(rectify,[],[f19])).
% 3.74/0.99  
% 3.74/0.99  fof(f21,plain,(
% 3.74/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f22,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 3.74/0.99  
% 3.74/0.99  fof(f37,plain,(
% 3.74/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.74/0.99    inference(cnf_transformation,[],[f22])).
% 3.74/0.99  
% 3.74/0.99  fof(f8,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f44,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f8])).
% 3.74/0.99  
% 3.74/0.99  fof(f56,plain,(
% 3.74/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.74/0.99    inference(definition_unfolding,[],[f37,f44])).
% 3.74/0.99  
% 3.74/0.99  fof(f64,plain,(
% 3.74/0.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 3.74/0.99    inference(equality_resolution,[],[f56])).
% 3.74/0.99  
% 3.74/0.99  fof(f65,plain,(
% 3.74/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 3.74/0.99    inference(equality_resolution,[],[f64])).
% 3.74/0.99  
% 3.74/0.99  fof(f9,conjecture,(
% 3.74/0.99    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f10,negated_conjecture,(
% 3.74/0.99    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 3.74/0.99    inference(negated_conjecture,[],[f9])).
% 3.74/0.99  
% 3.74/0.99  fof(f12,plain,(
% 3.74/0.99    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 3.74/0.99    inference(ennf_transformation,[],[f10])).
% 3.74/0.99  
% 3.74/0.99  fof(f23,plain,(
% 3.74/0.99    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)) => (sK2 != sK3 & r2_hidden(sK3,sK4) & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f24,plain,(
% 3.74/0.99    sK2 != sK3 & r2_hidden(sK3,sK4) & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2)),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f23])).
% 3.74/0.99  
% 3.74/0.99  fof(f45,plain,(
% 3.74/0.99    k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2)),
% 3.74/0.99    inference(cnf_transformation,[],[f24])).
% 3.74/0.99  
% 3.74/0.99  fof(f4,axiom,(
% 3.74/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f33,plain,(
% 3.74/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f4])).
% 3.74/0.99  
% 3.74/0.99  fof(f6,axiom,(
% 3.74/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f42,plain,(
% 3.74/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f6])).
% 3.74/0.99  
% 3.74/0.99  fof(f7,axiom,(
% 3.74/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f43,plain,(
% 3.74/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f7])).
% 3.74/0.99  
% 3.74/0.99  fof(f48,plain,(
% 3.74/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.74/0.99    inference(definition_unfolding,[],[f43,f44])).
% 3.74/0.99  
% 3.74/0.99  fof(f49,plain,(
% 3.74/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.74/0.99    inference(definition_unfolding,[],[f42,f48])).
% 3.74/0.99  
% 3.74/0.99  fof(f60,plain,(
% 3.74/0.99    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = k2_enumset1(sK2,sK2,sK2,sK2)),
% 3.74/0.99    inference(definition_unfolding,[],[f45,f33,f48,f49])).
% 3.74/0.99  
% 3.74/0.99  fof(f3,axiom,(
% 3.74/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f32,plain,(
% 3.74/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f3])).
% 3.74/0.99  
% 3.74/0.99  fof(f51,plain,(
% 3.74/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.74/0.99    inference(definition_unfolding,[],[f32,f33])).
% 3.74/0.99  
% 3.74/0.99  fof(f2,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f13,plain,(
% 3.74/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.74/0.99    inference(nnf_transformation,[],[f2])).
% 3.74/0.99  
% 3.74/0.99  fof(f14,plain,(
% 3.74/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.74/0.99    inference(flattening,[],[f13])).
% 3.74/0.99  
% 3.74/0.99  fof(f15,plain,(
% 3.74/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.74/0.99    inference(rectify,[],[f14])).
% 3.74/0.99  
% 3.74/0.99  fof(f16,plain,(
% 3.74/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f17,plain,(
% 3.74/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.74/0.99  
% 3.74/0.99  fof(f28,plain,(
% 3.74/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.74/0.99    inference(cnf_transformation,[],[f17])).
% 3.74/0.99  
% 3.74/0.99  fof(f61,plain,(
% 3.74/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.74/0.99    inference(equality_resolution,[],[f28])).
% 3.74/0.99  
% 3.74/0.99  fof(f27,plain,(
% 3.74/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.74/0.99    inference(cnf_transformation,[],[f17])).
% 3.74/0.99  
% 3.74/0.99  fof(f62,plain,(
% 3.74/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.74/0.99    inference(equality_resolution,[],[f27])).
% 3.74/0.99  
% 3.74/0.99  fof(f34,plain,(
% 3.74/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.74/0.99    inference(cnf_transformation,[],[f22])).
% 3.74/0.99  
% 3.74/0.99  fof(f59,plain,(
% 3.74/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.74/0.99    inference(definition_unfolding,[],[f34,f44])).
% 3.74/0.99  
% 3.74/0.99  fof(f70,plain,(
% 3.74/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.74/0.99    inference(equality_resolution,[],[f59])).
% 3.74/0.99  
% 3.74/0.99  fof(f35,plain,(
% 3.74/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.74/0.99    inference(cnf_transformation,[],[f22])).
% 3.74/0.99  
% 3.74/0.99  fof(f58,plain,(
% 3.74/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.74/0.99    inference(definition_unfolding,[],[f35,f44])).
% 3.74/0.99  
% 3.74/0.99  fof(f68,plain,(
% 3.74/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.74/0.99    inference(equality_resolution,[],[f58])).
% 3.74/0.99  
% 3.74/0.99  fof(f69,plain,(
% 3.74/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.74/0.99    inference(equality_resolution,[],[f68])).
% 3.74/0.99  
% 3.74/0.99  fof(f47,plain,(
% 3.74/0.99    sK2 != sK3),
% 3.74/0.99    inference(cnf_transformation,[],[f24])).
% 3.74/0.99  
% 3.74/0.99  fof(f46,plain,(
% 3.74/0.99    r2_hidden(sK3,sK4)),
% 3.74/0.99    inference(cnf_transformation,[],[f24])).
% 3.74/0.99  
% 3.74/0.99  cnf(c_12,plain,
% 3.74/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_390,plain,
% 3.74/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_18,negated_conjecture,
% 3.74/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 3.74/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7,plain,
% 3.74/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1180,plain,
% 3.74/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_18,c_7]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,X1)
% 3.74/0.99      | r2_hidden(X0,X2)
% 3.74/0.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_397,plain,
% 3.74/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.74/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.74/0.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2898,plain,
% 3.74/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top
% 3.74/0.99      | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 3.74/0.99      | r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_1180,c_397]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_396,plain,
% 3.74/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.74/0.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3497,plain,
% 3.74/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top
% 3.74/0.99      | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 3.74/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_2898,c_396]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6860,plain,
% 3.74/0.99      ( r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 3.74/0.99      | r2_hidden(sK3,sK4) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_390,c_3497]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_15,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.74/0.99      | X0 = X1
% 3.74/0.99      | X0 = X2
% 3.74/0.99      | X0 = X3 ),
% 3.74/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_445,plain,
% 3.74/0.99      ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,X2))
% 3.74/0.99      | sK3 = X0
% 3.74/0.99      | sK3 = X2
% 3.74/0.99      | sK3 = X1 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_446,plain,
% 3.74/0.99      ( sK3 = X0
% 3.74/0.99      | sK3 = X1
% 3.74/0.99      | sK3 = X2
% 3.74/0.99      | r2_hidden(sK3,k2_enumset1(X0,X0,X2,X1)) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_448,plain,
% 3.74/0.99      ( sK3 = sK2
% 3.74/0.99      | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_446]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_165,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_420,plain,
% 3.74/0.99      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_165]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_421,plain,
% 3.74/0.99      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_420]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_14,plain,
% 3.74/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_24,plain,
% 3.74/0.99      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_21,plain,
% 3.74/0.99      ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_16,negated_conjecture,
% 3.74/0.99      ( sK2 != sK3 ),
% 3.74/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_17,negated_conjecture,
% 3.74/0.99      ( r2_hidden(sK3,sK4) ),
% 3.74/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_19,plain,
% 3.74/0.99      ( r2_hidden(sK3,sK4) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(contradiction,plain,
% 3.74/0.99      ( $false ),
% 3.74/0.99      inference(minisat,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_6860,c_448,c_421,c_24,c_21,c_16,c_19]) ).
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  ------                               Statistics
% 3.74/0.99  
% 3.74/0.99  ------ General
% 3.74/0.99  
% 3.74/0.99  abstr_ref_over_cycles:                  0
% 3.74/0.99  abstr_ref_under_cycles:                 0
% 3.74/0.99  gc_basic_clause_elim:                   0
% 3.74/0.99  forced_gc_time:                         0
% 3.74/0.99  parsing_time:                           0.012
% 3.74/0.99  unif_index_cands_time:                  0.
% 3.74/0.99  unif_index_add_time:                    0.
% 3.74/0.99  orderings_time:                         0.
% 3.74/0.99  out_proof_time:                         0.007
% 3.74/0.99  total_time:                             0.222
% 3.74/0.99  num_of_symbols:                         39
% 3.74/0.99  num_of_terms:                           9550
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing
% 3.74/0.99  
% 3.74/0.99  num_of_splits:                          0
% 3.74/0.99  num_of_split_atoms:                     0
% 3.74/0.99  num_of_reused_defs:                     0
% 3.74/0.99  num_eq_ax_congr_red:                    14
% 3.74/0.99  num_of_sem_filtered_clauses:            1
% 3.74/0.99  num_of_subtypes:                        0
% 3.74/0.99  monotx_restored_types:                  0
% 3.74/0.99  sat_num_of_epr_types:                   0
% 3.74/0.99  sat_num_of_non_cyclic_types:            0
% 3.74/0.99  sat_guarded_non_collapsed_types:        0
% 3.74/0.99  num_pure_diseq_elim:                    0
% 3.74/0.99  simp_replaced_by:                       0
% 3.74/0.99  res_preprocessed:                       68
% 3.74/0.99  prep_upred:                             0
% 3.74/0.99  prep_unflattend:                        0
% 3.74/0.99  smt_new_axioms:                         0
% 3.74/0.99  pred_elim_cands:                        1
% 3.74/0.99  pred_elim:                              0
% 3.74/0.99  pred_elim_cl:                           0
% 3.74/0.99  pred_elim_cycles:                       1
% 3.74/0.99  merged_defs:                            0
% 3.74/0.99  merged_defs_ncl:                        0
% 3.74/0.99  bin_hyper_res:                          0
% 3.74/0.99  prep_cycles:                            3
% 3.74/0.99  pred_elim_time:                         0.
% 3.74/0.99  splitting_time:                         0.
% 3.74/0.99  sem_filter_time:                        0.
% 3.74/0.99  monotx_time:                            0.
% 3.74/0.99  subtype_inf_time:                       0.
% 3.74/0.99  
% 3.74/0.99  ------ Problem properties
% 3.74/0.99  
% 3.74/0.99  clauses:                                19
% 3.74/0.99  conjectures:                            3
% 3.74/0.99  epr:                                    2
% 3.74/0.99  horn:                                   13
% 3.74/0.99  ground:                                 3
% 3.74/0.99  unary:                                  8
% 3.74/0.99  binary:                                 2
% 3.74/0.99  lits:                                   43
% 3.74/0.99  lits_eq:                                20
% 3.74/0.99  fd_pure:                                0
% 3.74/0.99  fd_pseudo:                              0
% 3.74/0.99  fd_cond:                                0
% 3.74/0.99  fd_pseudo_cond:                         7
% 3.74/0.99  ac_symbols:                             0
% 3.74/0.99  
% 3.74/0.99  ------ Propositional Solver
% 3.74/0.99  
% 3.74/0.99  prop_solver_calls:                      25
% 3.74/0.99  prop_fast_solver_calls:                 434
% 3.74/0.99  smt_solver_calls:                       0
% 3.74/0.99  smt_fast_solver_calls:                  0
% 3.74/0.99  prop_num_of_clauses:                    2261
% 3.74/0.99  prop_preprocess_simplified:             5591
% 3.74/0.99  prop_fo_subsumed:                       0
% 3.74/0.99  prop_solver_time:                       0.
% 3.74/0.99  smt_solver_time:                        0.
% 3.74/0.99  smt_fast_solver_time:                   0.
% 3.74/0.99  prop_fast_solver_time:                  0.
% 3.74/0.99  prop_unsat_core_time:                   0.
% 3.74/0.99  
% 3.74/0.99  ------ QBF
% 3.74/0.99  
% 3.74/0.99  qbf_q_res:                              0
% 3.74/0.99  qbf_num_tautologies:                    0
% 3.74/0.99  qbf_prep_cycles:                        0
% 3.74/0.99  
% 3.74/0.99  ------ BMC1
% 3.74/0.99  
% 3.74/0.99  bmc1_current_bound:                     -1
% 3.74/0.99  bmc1_last_solved_bound:                 -1
% 3.74/0.99  bmc1_unsat_core_size:                   -1
% 3.74/0.99  bmc1_unsat_core_parents_size:           -1
% 3.74/0.99  bmc1_merge_next_fun:                    0
% 3.74/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.74/0.99  
% 3.74/0.99  ------ Instantiation
% 3.74/0.99  
% 3.74/0.99  inst_num_of_clauses:                    528
% 3.74/0.99  inst_num_in_passive:                    197
% 3.74/0.99  inst_num_in_active:                     227
% 3.74/0.99  inst_num_in_unprocessed:                104
% 3.74/0.99  inst_num_of_loops:                      260
% 3.74/0.99  inst_num_of_learning_restarts:          0
% 3.74/0.99  inst_num_moves_active_passive:          32
% 3.74/0.99  inst_lit_activity:                      0
% 3.74/0.99  inst_lit_activity_moves:                0
% 3.74/0.99  inst_num_tautologies:                   0
% 3.74/0.99  inst_num_prop_implied:                  0
% 3.74/0.99  inst_num_existing_simplified:           0
% 3.74/0.99  inst_num_eq_res_simplified:             0
% 3.74/0.99  inst_num_child_elim:                    0
% 3.74/0.99  inst_num_of_dismatching_blockings:      1528
% 3.74/0.99  inst_num_of_non_proper_insts:           1068
% 3.74/0.99  inst_num_of_duplicates:                 0
% 3.74/0.99  inst_inst_num_from_inst_to_res:         0
% 3.74/0.99  inst_dismatching_checking_time:         0.
% 3.74/0.99  
% 3.74/0.99  ------ Resolution
% 3.74/0.99  
% 3.74/0.99  res_num_of_clauses:                     0
% 3.74/0.99  res_num_in_passive:                     0
% 3.74/0.99  res_num_in_active:                      0
% 3.74/0.99  res_num_of_loops:                       71
% 3.74/0.99  res_forward_subset_subsumed:            176
% 3.74/0.99  res_backward_subset_subsumed:           0
% 3.74/0.99  res_forward_subsumed:                   0
% 3.74/0.99  res_backward_subsumed:                  0
% 3.74/0.99  res_forward_subsumption_resolution:     0
% 3.74/0.99  res_backward_subsumption_resolution:    0
% 3.74/0.99  res_clause_to_clause_subsumption:       944
% 3.74/0.99  res_orphan_elimination:                 0
% 3.74/0.99  res_tautology_del:                      16
% 3.74/0.99  res_num_eq_res_simplified:              0
% 3.74/0.99  res_num_sel_changes:                    0
% 3.74/0.99  res_moves_from_active_to_pass:          0
% 3.74/0.99  
% 3.74/0.99  ------ Superposition
% 3.74/0.99  
% 3.74/0.99  sup_time_total:                         0.
% 3.74/0.99  sup_time_generating:                    0.
% 3.74/0.99  sup_time_sim_full:                      0.
% 3.74/0.99  sup_time_sim_immed:                     0.
% 3.74/0.99  
% 3.74/0.99  sup_num_of_clauses:                     132
% 3.74/0.99  sup_num_in_active:                      49
% 3.74/0.99  sup_num_in_passive:                     83
% 3.74/0.99  sup_num_of_loops:                       51
% 3.74/0.99  sup_fw_superposition:                   264
% 3.74/0.99  sup_bw_superposition:                   158
% 3.74/0.99  sup_immediate_simplified:               193
% 3.74/0.99  sup_given_eliminated:                   0
% 3.74/0.99  comparisons_done:                       0
% 3.74/0.99  comparisons_avoided:                    16
% 3.74/0.99  
% 3.74/0.99  ------ Simplifications
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  sim_fw_subset_subsumed:                 10
% 3.74/0.99  sim_bw_subset_subsumed:                 0
% 3.74/0.99  sim_fw_subsumed:                        40
% 3.74/0.99  sim_bw_subsumed:                        12
% 3.74/0.99  sim_fw_subsumption_res:                 0
% 3.74/0.99  sim_bw_subsumption_res:                 0
% 3.74/0.99  sim_tautology_del:                      26
% 3.74/0.99  sim_eq_tautology_del:                   67
% 3.74/0.99  sim_eq_res_simp:                        3
% 3.74/0.99  sim_fw_demodulated:                     62
% 3.74/0.99  sim_bw_demodulated:                     6
% 3.74/0.99  sim_light_normalised:                   83
% 3.74/0.99  sim_joinable_taut:                      0
% 3.74/0.99  sim_joinable_simp:                      0
% 3.74/0.99  sim_ac_normalised:                      0
% 3.74/0.99  sim_smt_subsumption:                    0
% 3.74/0.99  
%------------------------------------------------------------------------------
