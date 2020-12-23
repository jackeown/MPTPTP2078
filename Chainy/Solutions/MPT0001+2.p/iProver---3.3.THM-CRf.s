%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 379 expanded)
%              Number of clauses        :   42 (  97 expanded)
%              Number of leaves         :    8 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  364 (2513 expanded)
%              Number of equality atoms :   85 ( 362 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
      <=> ~ ( r2_hidden(X0,X1)
          <=> r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <~> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,
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

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f27])).

fof(f46,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f48,plain,
    ( r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,
    ( r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f49,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    inference(definition_unfolding,[],[f49,f44])).

fof(f47,plain,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k5_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    inference(definition_unfolding,[],[f47,f44])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_689,plain,
    ( r2_hidden(sK2,X0)
    | r2_hidden(sK2,k4_xboole_0(sK4,X0))
    | ~ r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1370,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1371,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_659,plain,
    ( r2_hidden(sK2,X0)
    | r2_hidden(sK2,k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1329,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK3,sK4))
    | r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_1331,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_453,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_469,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_722,plain,
    ( r2_hidden(k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)),sK2) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_469])).

cnf(c_20,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_633,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3))
    | r2_hidden(sK2,k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_634,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(sK2,k4_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_464,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_455,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_753,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_464,c_455])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_457,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_458,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_921,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK3,sK4)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_753,c_457,c_458])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_465,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_456,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_776,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_465,c_456])).

cnf(c_821,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(sK4,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_822,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_1114,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_822])).

cnf(c_1120,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1114,c_458])).

cnf(c_1142,plain,
    ( r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_20,c_634,c_921,c_1120])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_454,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) = iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_723,plain,
    ( r2_hidden(k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)),sK2) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_469])).

cnf(c_21,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) = iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1123,plain,
    ( r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_723,c_21,c_634,c_921,c_1120])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1371,c_1331,c_1142,c_1123,c_1120,c_921])).

%------------------------------------------------------------------------------
