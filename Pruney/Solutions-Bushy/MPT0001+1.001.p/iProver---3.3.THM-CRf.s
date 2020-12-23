%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:13 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 379 expanded)
%              Number of clauses        :   35 (  97 expanded)
%              Number of leaves         :    7 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  336 (2605 expanded)
%              Number of equality atoms :   78 ( 393 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
      <=> ~ ( r2_hidden(X0,X1)
          <=> r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <~> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ( ( r2_hidden(X0,X1)
              | ~ r2_hidden(X0,X2) )
            & ( r2_hidden(X0,X2)
              | ~ r2_hidden(X0,X1) ) )
          | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) )
        & ( ( ( ~ r2_hidden(X0,X2)
              | ~ r2_hidden(X0,X1) )
            & ( r2_hidden(X0,X2)
              | r2_hidden(X0,X1) ) )
          | r2_hidden(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ( ( r2_hidden(sK2,sK3)
            | ~ r2_hidden(sK2,sK4) )
          & ( r2_hidden(sK2,sK4)
            | ~ r2_hidden(sK2,sK3) ) )
        | ~ r2_hidden(sK2,k5_xboole_0(sK3,sK4)) )
      & ( ( ( ~ r2_hidden(sK2,sK4)
            | ~ r2_hidden(sK2,sK3) )
          & ( r2_hidden(sK2,sK4)
            | r2_hidden(sK2,sK3) ) )
        | r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ( ( r2_hidden(sK2,sK3)
          | ~ r2_hidden(sK2,sK4) )
        & ( r2_hidden(sK2,sK4)
          | ~ r2_hidden(sK2,sK3) ) )
      | ~ r2_hidden(sK2,k5_xboole_0(sK3,sK4)) )
    & ( ( ( ~ r2_hidden(sK2,sK4)
          | ~ r2_hidden(sK2,sK3) )
        & ( r2_hidden(sK2,sK4)
          | r2_hidden(sK2,sK3) ) )
      | r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f18])).

fof(f34,plain,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f35,plain,
    ( r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,
    ( r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(flattening,[],[f12])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f22])).

fof(f36,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f33,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    inference(definition_unfolding,[],[f33,f32])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_425,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) = iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_434,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_795,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(sK2,k4_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_425,c_434])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_435,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_426,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_753,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_426])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_430,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_915,plain,
    ( r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_753,c_430])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_436,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_427,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_770,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_427])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_640,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(sK4,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_641,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_921,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_770,c_641])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_429,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_927,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_921,c_429])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_424,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_794,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(sK2,k4_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_434])).

cnf(c_917,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(sK3,sK4))
    | r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_918,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_929,plain,
    ( r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_430,c_927])).

cnf(c_932,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_794,c_918,c_927,c_929])).

cnf(c_1002,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_795,c_794,c_915,c_918,c_927,c_929])).

cnf(c_1008,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1002,c_429])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1008,c_932,c_915])).


%------------------------------------------------------------------------------
