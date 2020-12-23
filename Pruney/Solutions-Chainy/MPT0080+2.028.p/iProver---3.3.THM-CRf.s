%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:57 EST 2020

% Result     : Theorem 15.47s
% Output     : CNFRefutation 15.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 130 expanded)
%              Number of clauses        :   43 (  46 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   15
%              Number of atoms          :  324 ( 683 expanded)
%              Number of equality atoms :   94 ( 133 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK3,sK4)
      & r1_xboole_0(sK3,sK5)
      & r1_tarski(sK3,k2_xboole_0(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_tarski(sK3,sK4)
    & r1_xboole_0(sK3,sK5)
    & r1_tarski(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f34])).

fof(f62,plain,(
    r1_tarski(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f63,plain,(
    r1_xboole_0(sK3,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_702,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_358,plain,
    ( k2_xboole_0(X0,X1) = X1
    | k2_xboole_0(sK4,sK5) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_359,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK5)) = k2_xboole_0(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_706,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1962,plain,
    ( r2_hidden(X0,k2_xboole_0(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_706])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_705,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2996,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_705])).

cnf(c_27,negated_conjecture,
    ( r1_xboole_0(sK3,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_692,plain,
    ( r1_xboole_0(sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_698,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1514,plain,
    ( r1_xboole_0(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_698])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_695,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,k2_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1964,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_695])).

cnf(c_2899,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1964])).

cnf(c_4011,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2996,c_2899])).

cnf(c_4017,plain,
    ( k4_xboole_0(sK3,X0) = X1
    | r2_hidden(sK1(sK3,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK3,X0,X1),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_4011])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_703,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_33068,plain,
    ( k4_xboole_0(sK3,sK4) = X0
    | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4017,c_703])).

cnf(c_33099,plain,
    ( k4_xboole_0(sK3,sK4) = k1_xboole_0
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33068])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2403,plain,
    ( r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0))
    | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2409,plain,
    ( r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0)) = iProver_top
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2403])).

cnf(c_2411,plain,
    ( r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_1158,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),X0)
    | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(k1_xboole_0,X0))
    | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1159,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),X0) != iProver_top
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(k1_xboole_0,X0)) != iProver_top
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1158])).

cnf(c_1161,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_21,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_198,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_353,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_198,c_26])).

cnf(c_354,plain,
    ( k4_xboole_0(sK3,sK4) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_25,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_34,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33099,c_2411,c_1161,c_354,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.47/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.47/2.51  
% 15.47/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.47/2.51  
% 15.47/2.51  ------  iProver source info
% 15.47/2.51  
% 15.47/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.47/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.47/2.51  git: non_committed_changes: false
% 15.47/2.51  git: last_make_outside_of_git: false
% 15.47/2.51  
% 15.47/2.51  ------ 
% 15.47/2.51  
% 15.47/2.51  ------ Input Options
% 15.47/2.51  
% 15.47/2.51  --out_options                           all
% 15.47/2.51  --tptp_safe_out                         true
% 15.47/2.51  --problem_path                          ""
% 15.47/2.51  --include_path                          ""
% 15.47/2.51  --clausifier                            res/vclausify_rel
% 15.47/2.51  --clausifier_options                    ""
% 15.47/2.51  --stdin                                 false
% 15.47/2.51  --stats_out                             all
% 15.47/2.51  
% 15.47/2.51  ------ General Options
% 15.47/2.51  
% 15.47/2.51  --fof                                   false
% 15.47/2.51  --time_out_real                         305.
% 15.47/2.51  --time_out_virtual                      -1.
% 15.47/2.51  --symbol_type_check                     false
% 15.47/2.51  --clausify_out                          false
% 15.47/2.51  --sig_cnt_out                           false
% 15.47/2.52  --trig_cnt_out                          false
% 15.47/2.52  --trig_cnt_out_tolerance                1.
% 15.47/2.52  --trig_cnt_out_sk_spl                   false
% 15.47/2.52  --abstr_cl_out                          false
% 15.47/2.52  
% 15.47/2.52  ------ Global Options
% 15.47/2.52  
% 15.47/2.52  --schedule                              default
% 15.47/2.52  --add_important_lit                     false
% 15.47/2.52  --prop_solver_per_cl                    1000
% 15.47/2.52  --min_unsat_core                        false
% 15.47/2.52  --soft_assumptions                      false
% 15.47/2.52  --soft_lemma_size                       3
% 15.47/2.52  --prop_impl_unit_size                   0
% 15.47/2.52  --prop_impl_unit                        []
% 15.47/2.52  --share_sel_clauses                     true
% 15.47/2.52  --reset_solvers                         false
% 15.47/2.52  --bc_imp_inh                            [conj_cone]
% 15.47/2.52  --conj_cone_tolerance                   3.
% 15.47/2.52  --extra_neg_conj                        none
% 15.47/2.52  --large_theory_mode                     true
% 15.47/2.52  --prolific_symb_bound                   200
% 15.47/2.52  --lt_threshold                          2000
% 15.47/2.52  --clause_weak_htbl                      true
% 15.47/2.52  --gc_record_bc_elim                     false
% 15.47/2.52  
% 15.47/2.52  ------ Preprocessing Options
% 15.47/2.52  
% 15.47/2.52  --preprocessing_flag                    true
% 15.47/2.52  --time_out_prep_mult                    0.1
% 15.47/2.52  --splitting_mode                        input
% 15.47/2.52  --splitting_grd                         true
% 15.47/2.52  --splitting_cvd                         false
% 15.47/2.52  --splitting_cvd_svl                     false
% 15.47/2.52  --splitting_nvd                         32
% 15.47/2.52  --sub_typing                            true
% 15.47/2.52  --prep_gs_sim                           true
% 15.47/2.52  --prep_unflatten                        true
% 15.47/2.52  --prep_res_sim                          true
% 15.47/2.52  --prep_upred                            true
% 15.47/2.52  --prep_sem_filter                       exhaustive
% 15.47/2.52  --prep_sem_filter_out                   false
% 15.47/2.52  --pred_elim                             true
% 15.47/2.52  --res_sim_input                         true
% 15.47/2.52  --eq_ax_congr_red                       true
% 15.47/2.52  --pure_diseq_elim                       true
% 15.47/2.52  --brand_transform                       false
% 15.47/2.52  --non_eq_to_eq                          false
% 15.47/2.52  --prep_def_merge                        true
% 15.47/2.52  --prep_def_merge_prop_impl              false
% 15.47/2.52  --prep_def_merge_mbd                    true
% 15.47/2.52  --prep_def_merge_tr_red                 false
% 15.47/2.52  --prep_def_merge_tr_cl                  false
% 15.47/2.52  --smt_preprocessing                     true
% 15.47/2.52  --smt_ac_axioms                         fast
% 15.47/2.52  --preprocessed_out                      false
% 15.47/2.52  --preprocessed_stats                    false
% 15.47/2.52  
% 15.47/2.52  ------ Abstraction refinement Options
% 15.47/2.52  
% 15.47/2.52  --abstr_ref                             []
% 15.47/2.52  --abstr_ref_prep                        false
% 15.47/2.52  --abstr_ref_until_sat                   false
% 15.47/2.52  --abstr_ref_sig_restrict                funpre
% 15.47/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.47/2.52  --abstr_ref_under                       []
% 15.47/2.52  
% 15.47/2.52  ------ SAT Options
% 15.47/2.52  
% 15.47/2.52  --sat_mode                              false
% 15.47/2.52  --sat_fm_restart_options                ""
% 15.47/2.52  --sat_gr_def                            false
% 15.47/2.52  --sat_epr_types                         true
% 15.47/2.52  --sat_non_cyclic_types                  false
% 15.47/2.52  --sat_finite_models                     false
% 15.47/2.52  --sat_fm_lemmas                         false
% 15.47/2.52  --sat_fm_prep                           false
% 15.47/2.52  --sat_fm_uc_incr                        true
% 15.47/2.52  --sat_out_model                         small
% 15.47/2.52  --sat_out_clauses                       false
% 15.47/2.52  
% 15.47/2.52  ------ QBF Options
% 15.47/2.52  
% 15.47/2.52  --qbf_mode                              false
% 15.47/2.52  --qbf_elim_univ                         false
% 15.47/2.52  --qbf_dom_inst                          none
% 15.47/2.52  --qbf_dom_pre_inst                      false
% 15.47/2.52  --qbf_sk_in                             false
% 15.47/2.52  --qbf_pred_elim                         true
% 15.47/2.52  --qbf_split                             512
% 15.47/2.52  
% 15.47/2.52  ------ BMC1 Options
% 15.47/2.52  
% 15.47/2.52  --bmc1_incremental                      false
% 15.47/2.52  --bmc1_axioms                           reachable_all
% 15.47/2.52  --bmc1_min_bound                        0
% 15.47/2.52  --bmc1_max_bound                        -1
% 15.47/2.52  --bmc1_max_bound_default                -1
% 15.47/2.52  --bmc1_symbol_reachability              true
% 15.47/2.52  --bmc1_property_lemmas                  false
% 15.47/2.52  --bmc1_k_induction                      false
% 15.47/2.52  --bmc1_non_equiv_states                 false
% 15.47/2.52  --bmc1_deadlock                         false
% 15.47/2.52  --bmc1_ucm                              false
% 15.47/2.52  --bmc1_add_unsat_core                   none
% 15.47/2.52  --bmc1_unsat_core_children              false
% 15.47/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.47/2.52  --bmc1_out_stat                         full
% 15.47/2.52  --bmc1_ground_init                      false
% 15.47/2.52  --bmc1_pre_inst_next_state              false
% 15.47/2.52  --bmc1_pre_inst_state                   false
% 15.47/2.52  --bmc1_pre_inst_reach_state             false
% 15.47/2.52  --bmc1_out_unsat_core                   false
% 15.47/2.52  --bmc1_aig_witness_out                  false
% 15.47/2.52  --bmc1_verbose                          false
% 15.47/2.52  --bmc1_dump_clauses_tptp                false
% 15.47/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.47/2.52  --bmc1_dump_file                        -
% 15.47/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.47/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.47/2.52  --bmc1_ucm_extend_mode                  1
% 15.47/2.52  --bmc1_ucm_init_mode                    2
% 15.47/2.52  --bmc1_ucm_cone_mode                    none
% 15.47/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.47/2.52  --bmc1_ucm_relax_model                  4
% 15.47/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.47/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.47/2.52  --bmc1_ucm_layered_model                none
% 15.47/2.52  --bmc1_ucm_max_lemma_size               10
% 15.47/2.52  
% 15.47/2.52  ------ AIG Options
% 15.47/2.52  
% 15.47/2.52  --aig_mode                              false
% 15.47/2.52  
% 15.47/2.52  ------ Instantiation Options
% 15.47/2.52  
% 15.47/2.52  --instantiation_flag                    true
% 15.47/2.52  --inst_sos_flag                         true
% 15.47/2.52  --inst_sos_phase                        true
% 15.47/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.47/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.47/2.52  --inst_lit_sel_side                     num_symb
% 15.47/2.52  --inst_solver_per_active                1400
% 15.47/2.52  --inst_solver_calls_frac                1.
% 15.47/2.52  --inst_passive_queue_type               priority_queues
% 15.47/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.47/2.52  --inst_passive_queues_freq              [25;2]
% 15.47/2.52  --inst_dismatching                      true
% 15.47/2.52  --inst_eager_unprocessed_to_passive     true
% 15.47/2.52  --inst_prop_sim_given                   true
% 15.47/2.52  --inst_prop_sim_new                     false
% 15.47/2.52  --inst_subs_new                         false
% 15.47/2.52  --inst_eq_res_simp                      false
% 15.47/2.52  --inst_subs_given                       false
% 15.47/2.52  --inst_orphan_elimination               true
% 15.47/2.52  --inst_learning_loop_flag               true
% 15.47/2.52  --inst_learning_start                   3000
% 15.47/2.52  --inst_learning_factor                  2
% 15.47/2.52  --inst_start_prop_sim_after_learn       3
% 15.47/2.52  --inst_sel_renew                        solver
% 15.47/2.52  --inst_lit_activity_flag                true
% 15.47/2.52  --inst_restr_to_given                   false
% 15.47/2.52  --inst_activity_threshold               500
% 15.47/2.52  --inst_out_proof                        true
% 15.47/2.52  
% 15.47/2.52  ------ Resolution Options
% 15.47/2.52  
% 15.47/2.52  --resolution_flag                       true
% 15.47/2.52  --res_lit_sel                           adaptive
% 15.47/2.52  --res_lit_sel_side                      none
% 15.47/2.52  --res_ordering                          kbo
% 15.47/2.52  --res_to_prop_solver                    active
% 15.47/2.52  --res_prop_simpl_new                    false
% 15.47/2.52  --res_prop_simpl_given                  true
% 15.47/2.52  --res_passive_queue_type                priority_queues
% 15.47/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.47/2.52  --res_passive_queues_freq               [15;5]
% 15.47/2.52  --res_forward_subs                      full
% 15.47/2.52  --res_backward_subs                     full
% 15.47/2.52  --res_forward_subs_resolution           true
% 15.47/2.52  --res_backward_subs_resolution          true
% 15.47/2.52  --res_orphan_elimination                true
% 15.47/2.52  --res_time_limit                        2.
% 15.47/2.52  --res_out_proof                         true
% 15.47/2.52  
% 15.47/2.52  ------ Superposition Options
% 15.47/2.52  
% 15.47/2.52  --superposition_flag                    true
% 15.47/2.52  --sup_passive_queue_type                priority_queues
% 15.47/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.47/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.47/2.52  --demod_completeness_check              fast
% 15.47/2.52  --demod_use_ground                      true
% 15.47/2.52  --sup_to_prop_solver                    passive
% 15.47/2.52  --sup_prop_simpl_new                    true
% 15.47/2.52  --sup_prop_simpl_given                  true
% 15.47/2.52  --sup_fun_splitting                     true
% 15.47/2.52  --sup_smt_interval                      50000
% 15.47/2.52  
% 15.47/2.52  ------ Superposition Simplification Setup
% 15.47/2.52  
% 15.47/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.47/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.47/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.47/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.47/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.47/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.47/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.47/2.52  --sup_immed_triv                        [TrivRules]
% 15.47/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.52  --sup_immed_bw_main                     []
% 15.47/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.47/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.47/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.52  --sup_input_bw                          []
% 15.47/2.52  
% 15.47/2.52  ------ Combination Options
% 15.47/2.52  
% 15.47/2.52  --comb_res_mult                         3
% 15.47/2.52  --comb_sup_mult                         2
% 15.47/2.52  --comb_inst_mult                        10
% 15.47/2.52  
% 15.47/2.52  ------ Debug Options
% 15.47/2.52  
% 15.47/2.52  --dbg_backtrace                         false
% 15.47/2.52  --dbg_dump_prop_clauses                 false
% 15.47/2.52  --dbg_dump_prop_clauses_file            -
% 15.47/2.52  --dbg_out_stat                          false
% 15.47/2.52  ------ Parsing...
% 15.47/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.47/2.52  
% 15.47/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 15.47/2.52  
% 15.47/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.47/2.52  
% 15.47/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.47/2.52  ------ Proving...
% 15.47/2.52  ------ Problem Properties 
% 15.47/2.52  
% 15.47/2.52  
% 15.47/2.52  clauses                                 29
% 15.47/2.52  conjectures                             1
% 15.47/2.52  EPR                                     3
% 15.47/2.52  Horn                                    21
% 15.47/2.52  unary                                   10
% 15.47/2.52  binary                                  9
% 15.47/2.52  lits                                    62
% 15.47/2.52  lits eq                                 18
% 15.47/2.52  fd_pure                                 0
% 15.47/2.52  fd_pseudo                               0
% 15.47/2.52  fd_cond                                 0
% 15.47/2.52  fd_pseudo_cond                          6
% 15.47/2.52  AC symbols                              0
% 15.47/2.52  
% 15.47/2.52  ------ Schedule dynamic 5 is on 
% 15.47/2.52  
% 15.47/2.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.47/2.52  
% 15.47/2.52  
% 15.47/2.52  ------ 
% 15.47/2.52  Current options:
% 15.47/2.52  ------ 
% 15.47/2.52  
% 15.47/2.52  ------ Input Options
% 15.47/2.52  
% 15.47/2.52  --out_options                           all
% 15.47/2.52  --tptp_safe_out                         true
% 15.47/2.52  --problem_path                          ""
% 15.47/2.52  --include_path                          ""
% 15.47/2.52  --clausifier                            res/vclausify_rel
% 15.47/2.52  --clausifier_options                    ""
% 15.47/2.52  --stdin                                 false
% 15.47/2.52  --stats_out                             all
% 15.47/2.52  
% 15.47/2.52  ------ General Options
% 15.47/2.52  
% 15.47/2.52  --fof                                   false
% 15.47/2.52  --time_out_real                         305.
% 15.47/2.52  --time_out_virtual                      -1.
% 15.47/2.52  --symbol_type_check                     false
% 15.47/2.52  --clausify_out                          false
% 15.47/2.52  --sig_cnt_out                           false
% 15.47/2.52  --trig_cnt_out                          false
% 15.47/2.52  --trig_cnt_out_tolerance                1.
% 15.47/2.52  --trig_cnt_out_sk_spl                   false
% 15.47/2.52  --abstr_cl_out                          false
% 15.47/2.52  
% 15.47/2.52  ------ Global Options
% 15.47/2.52  
% 15.47/2.52  --schedule                              default
% 15.47/2.52  --add_important_lit                     false
% 15.47/2.52  --prop_solver_per_cl                    1000
% 15.47/2.52  --min_unsat_core                        false
% 15.47/2.52  --soft_assumptions                      false
% 15.47/2.52  --soft_lemma_size                       3
% 15.47/2.52  --prop_impl_unit_size                   0
% 15.47/2.52  --prop_impl_unit                        []
% 15.47/2.52  --share_sel_clauses                     true
% 15.47/2.52  --reset_solvers                         false
% 15.47/2.52  --bc_imp_inh                            [conj_cone]
% 15.47/2.52  --conj_cone_tolerance                   3.
% 15.47/2.52  --extra_neg_conj                        none
% 15.47/2.52  --large_theory_mode                     true
% 15.47/2.52  --prolific_symb_bound                   200
% 15.47/2.52  --lt_threshold                          2000
% 15.47/2.52  --clause_weak_htbl                      true
% 15.47/2.52  --gc_record_bc_elim                     false
% 15.47/2.52  
% 15.47/2.52  ------ Preprocessing Options
% 15.47/2.52  
% 15.47/2.52  --preprocessing_flag                    true
% 15.47/2.52  --time_out_prep_mult                    0.1
% 15.47/2.52  --splitting_mode                        input
% 15.47/2.52  --splitting_grd                         true
% 15.47/2.52  --splitting_cvd                         false
% 15.47/2.52  --splitting_cvd_svl                     false
% 15.47/2.52  --splitting_nvd                         32
% 15.47/2.52  --sub_typing                            true
% 15.47/2.52  --prep_gs_sim                           true
% 15.47/2.52  --prep_unflatten                        true
% 15.47/2.52  --prep_res_sim                          true
% 15.47/2.52  --prep_upred                            true
% 15.47/2.52  --prep_sem_filter                       exhaustive
% 15.47/2.52  --prep_sem_filter_out                   false
% 15.47/2.52  --pred_elim                             true
% 15.47/2.52  --res_sim_input                         true
% 15.47/2.52  --eq_ax_congr_red                       true
% 15.47/2.52  --pure_diseq_elim                       true
% 15.47/2.52  --brand_transform                       false
% 15.47/2.52  --non_eq_to_eq                          false
% 15.47/2.52  --prep_def_merge                        true
% 15.47/2.52  --prep_def_merge_prop_impl              false
% 15.47/2.52  --prep_def_merge_mbd                    true
% 15.47/2.52  --prep_def_merge_tr_red                 false
% 15.47/2.52  --prep_def_merge_tr_cl                  false
% 15.47/2.52  --smt_preprocessing                     true
% 15.47/2.52  --smt_ac_axioms                         fast
% 15.47/2.52  --preprocessed_out                      false
% 15.47/2.52  --preprocessed_stats                    false
% 15.47/2.52  
% 15.47/2.52  ------ Abstraction refinement Options
% 15.47/2.52  
% 15.47/2.52  --abstr_ref                             []
% 15.47/2.52  --abstr_ref_prep                        false
% 15.47/2.52  --abstr_ref_until_sat                   false
% 15.47/2.52  --abstr_ref_sig_restrict                funpre
% 15.47/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.47/2.52  --abstr_ref_under                       []
% 15.47/2.52  
% 15.47/2.52  ------ SAT Options
% 15.47/2.52  
% 15.47/2.52  --sat_mode                              false
% 15.47/2.52  --sat_fm_restart_options                ""
% 15.47/2.52  --sat_gr_def                            false
% 15.47/2.52  --sat_epr_types                         true
% 15.47/2.52  --sat_non_cyclic_types                  false
% 15.47/2.52  --sat_finite_models                     false
% 15.47/2.52  --sat_fm_lemmas                         false
% 15.47/2.52  --sat_fm_prep                           false
% 15.47/2.52  --sat_fm_uc_incr                        true
% 15.47/2.52  --sat_out_model                         small
% 15.47/2.52  --sat_out_clauses                       false
% 15.47/2.52  
% 15.47/2.52  ------ QBF Options
% 15.47/2.52  
% 15.47/2.52  --qbf_mode                              false
% 15.47/2.52  --qbf_elim_univ                         false
% 15.47/2.52  --qbf_dom_inst                          none
% 15.47/2.52  --qbf_dom_pre_inst                      false
% 15.47/2.52  --qbf_sk_in                             false
% 15.47/2.52  --qbf_pred_elim                         true
% 15.47/2.52  --qbf_split                             512
% 15.47/2.52  
% 15.47/2.52  ------ BMC1 Options
% 15.47/2.52  
% 15.47/2.52  --bmc1_incremental                      false
% 15.47/2.52  --bmc1_axioms                           reachable_all
% 15.47/2.52  --bmc1_min_bound                        0
% 15.47/2.52  --bmc1_max_bound                        -1
% 15.47/2.52  --bmc1_max_bound_default                -1
% 15.47/2.52  --bmc1_symbol_reachability              true
% 15.47/2.52  --bmc1_property_lemmas                  false
% 15.47/2.52  --bmc1_k_induction                      false
% 15.47/2.52  --bmc1_non_equiv_states                 false
% 15.47/2.52  --bmc1_deadlock                         false
% 15.47/2.52  --bmc1_ucm                              false
% 15.47/2.52  --bmc1_add_unsat_core                   none
% 15.47/2.52  --bmc1_unsat_core_children              false
% 15.47/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.47/2.52  --bmc1_out_stat                         full
% 15.47/2.52  --bmc1_ground_init                      false
% 15.47/2.52  --bmc1_pre_inst_next_state              false
% 15.47/2.52  --bmc1_pre_inst_state                   false
% 15.47/2.52  --bmc1_pre_inst_reach_state             false
% 15.47/2.52  --bmc1_out_unsat_core                   false
% 15.47/2.52  --bmc1_aig_witness_out                  false
% 15.47/2.52  --bmc1_verbose                          false
% 15.47/2.52  --bmc1_dump_clauses_tptp                false
% 15.47/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.47/2.52  --bmc1_dump_file                        -
% 15.47/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.47/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.47/2.52  --bmc1_ucm_extend_mode                  1
% 15.47/2.52  --bmc1_ucm_init_mode                    2
% 15.47/2.52  --bmc1_ucm_cone_mode                    none
% 15.47/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.47/2.52  --bmc1_ucm_relax_model                  4
% 15.47/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.47/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.47/2.52  --bmc1_ucm_layered_model                none
% 15.47/2.52  --bmc1_ucm_max_lemma_size               10
% 15.47/2.52  
% 15.47/2.52  ------ AIG Options
% 15.47/2.52  
% 15.47/2.52  --aig_mode                              false
% 15.47/2.52  
% 15.47/2.52  ------ Instantiation Options
% 15.47/2.52  
% 15.47/2.52  --instantiation_flag                    true
% 15.47/2.52  --inst_sos_flag                         true
% 15.47/2.52  --inst_sos_phase                        true
% 15.47/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.47/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.47/2.52  --inst_lit_sel_side                     none
% 15.47/2.52  --inst_solver_per_active                1400
% 15.47/2.52  --inst_solver_calls_frac                1.
% 15.47/2.52  --inst_passive_queue_type               priority_queues
% 15.47/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.47/2.52  --inst_passive_queues_freq              [25;2]
% 15.47/2.52  --inst_dismatching                      true
% 15.47/2.52  --inst_eager_unprocessed_to_passive     true
% 15.47/2.52  --inst_prop_sim_given                   true
% 15.47/2.52  --inst_prop_sim_new                     false
% 15.47/2.52  --inst_subs_new                         false
% 15.47/2.52  --inst_eq_res_simp                      false
% 15.47/2.52  --inst_subs_given                       false
% 15.47/2.52  --inst_orphan_elimination               true
% 15.47/2.52  --inst_learning_loop_flag               true
% 15.47/2.52  --inst_learning_start                   3000
% 15.47/2.52  --inst_learning_factor                  2
% 15.47/2.52  --inst_start_prop_sim_after_learn       3
% 15.47/2.52  --inst_sel_renew                        solver
% 15.47/2.52  --inst_lit_activity_flag                true
% 15.47/2.52  --inst_restr_to_given                   false
% 15.47/2.52  --inst_activity_threshold               500
% 15.47/2.52  --inst_out_proof                        true
% 15.47/2.52  
% 15.47/2.52  ------ Resolution Options
% 15.47/2.52  
% 15.47/2.52  --resolution_flag                       false
% 15.47/2.52  --res_lit_sel                           adaptive
% 15.47/2.52  --res_lit_sel_side                      none
% 15.47/2.52  --res_ordering                          kbo
% 15.47/2.52  --res_to_prop_solver                    active
% 15.47/2.52  --res_prop_simpl_new                    false
% 15.47/2.52  --res_prop_simpl_given                  true
% 15.47/2.52  --res_passive_queue_type                priority_queues
% 15.47/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.47/2.52  --res_passive_queues_freq               [15;5]
% 15.47/2.52  --res_forward_subs                      full
% 15.47/2.52  --res_backward_subs                     full
% 15.47/2.52  --res_forward_subs_resolution           true
% 15.47/2.52  --res_backward_subs_resolution          true
% 15.47/2.52  --res_orphan_elimination                true
% 15.47/2.52  --res_time_limit                        2.
% 15.47/2.52  --res_out_proof                         true
% 15.47/2.52  
% 15.47/2.52  ------ Superposition Options
% 15.47/2.52  
% 15.47/2.52  --superposition_flag                    true
% 15.47/2.52  --sup_passive_queue_type                priority_queues
% 15.47/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.47/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.47/2.52  --demod_completeness_check              fast
% 15.47/2.52  --demod_use_ground                      true
% 15.47/2.52  --sup_to_prop_solver                    passive
% 15.47/2.52  --sup_prop_simpl_new                    true
% 15.47/2.52  --sup_prop_simpl_given                  true
% 15.47/2.52  --sup_fun_splitting                     true
% 15.47/2.52  --sup_smt_interval                      50000
% 15.47/2.52  
% 15.47/2.52  ------ Superposition Simplification Setup
% 15.47/2.52  
% 15.47/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.47/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.47/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.47/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.47/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.47/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.47/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.47/2.52  --sup_immed_triv                        [TrivRules]
% 15.47/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.52  --sup_immed_bw_main                     []
% 15.47/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.47/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.47/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.52  --sup_input_bw                          []
% 15.47/2.52  
% 15.47/2.52  ------ Combination Options
% 15.47/2.52  
% 15.47/2.52  --comb_res_mult                         3
% 15.47/2.52  --comb_sup_mult                         2
% 15.47/2.52  --comb_inst_mult                        10
% 15.47/2.52  
% 15.47/2.52  ------ Debug Options
% 15.47/2.52  
% 15.47/2.52  --dbg_backtrace                         false
% 15.47/2.52  --dbg_dump_prop_clauses                 false
% 15.47/2.52  --dbg_dump_prop_clauses_file            -
% 15.47/2.52  --dbg_out_stat                          false
% 15.47/2.52  
% 15.47/2.52  
% 15.47/2.52  
% 15.47/2.52  
% 15.47/2.52  ------ Proving...
% 15.47/2.52  
% 15.47/2.52  
% 15.47/2.52  % SZS status Theorem for theBenchmark.p
% 15.47/2.52  
% 15.47/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.47/2.52  
% 15.47/2.52  fof(f3,axiom,(
% 15.47/2.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.47/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.52  
% 15.47/2.52  fof(f26,plain,(
% 15.47/2.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.47/2.52    inference(nnf_transformation,[],[f3])).
% 15.47/2.52  
% 15.47/2.52  fof(f27,plain,(
% 15.47/2.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.47/2.52    inference(flattening,[],[f26])).
% 15.47/2.52  
% 15.47/2.52  fof(f28,plain,(
% 15.47/2.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.47/2.52    inference(rectify,[],[f27])).
% 15.47/2.52  
% 15.47/2.52  fof(f29,plain,(
% 15.47/2.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 15.47/2.52    introduced(choice_axiom,[])).
% 15.47/2.52  
% 15.47/2.52  fof(f30,plain,(
% 15.47/2.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.47/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 15.47/2.52  
% 15.47/2.52  fof(f46,plain,(
% 15.47/2.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 15.47/2.52    inference(cnf_transformation,[],[f30])).
% 15.47/2.52  
% 15.47/2.52  fof(f8,axiom,(
% 15.47/2.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.47/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.52  
% 15.47/2.52  fof(f18,plain,(
% 15.47/2.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.47/2.52    inference(ennf_transformation,[],[f8])).
% 15.47/2.52  
% 15.47/2.52  fof(f58,plain,(
% 15.47/2.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.47/2.52    inference(cnf_transformation,[],[f18])).
% 15.47/2.52  
% 15.47/2.52  fof(f12,conjecture,(
% 15.47/2.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 15.47/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.52  
% 15.47/2.52  fof(f13,negated_conjecture,(
% 15.47/2.52    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 15.47/2.52    inference(negated_conjecture,[],[f12])).
% 15.47/2.52  
% 15.47/2.52  fof(f19,plain,(
% 15.47/2.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 15.47/2.52    inference(ennf_transformation,[],[f13])).
% 15.47/2.52  
% 15.47/2.52  fof(f20,plain,(
% 15.47/2.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.47/2.52    inference(flattening,[],[f19])).
% 15.47/2.52  
% 15.47/2.52  fof(f34,plain,(
% 15.47/2.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK3,sK4) & r1_xboole_0(sK3,sK5) & r1_tarski(sK3,k2_xboole_0(sK4,sK5)))),
% 15.47/2.52    introduced(choice_axiom,[])).
% 15.47/2.52  
% 15.47/2.52  fof(f35,plain,(
% 15.47/2.52    ~r1_tarski(sK3,sK4) & r1_xboole_0(sK3,sK5) & r1_tarski(sK3,k2_xboole_0(sK4,sK5))),
% 15.47/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f34])).
% 15.47/2.52  
% 15.47/2.52  fof(f62,plain,(
% 15.47/2.52    r1_tarski(sK3,k2_xboole_0(sK4,sK5))),
% 15.47/2.52    inference(cnf_transformation,[],[f35])).
% 15.47/2.52  
% 15.47/2.52  fof(f2,axiom,(
% 15.47/2.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 15.47/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.52  
% 15.47/2.52  fof(f21,plain,(
% 15.47/2.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.47/2.52    inference(nnf_transformation,[],[f2])).
% 15.47/2.52  
% 15.47/2.52  fof(f22,plain,(
% 15.47/2.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.47/2.52    inference(flattening,[],[f21])).
% 15.47/2.52  
% 15.47/2.52  fof(f23,plain,(
% 15.47/2.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.47/2.52    inference(rectify,[],[f22])).
% 15.47/2.52  
% 15.47/2.52  fof(f24,plain,(
% 15.47/2.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.47/2.52    introduced(choice_axiom,[])).
% 15.47/2.52  
% 15.47/2.52  fof(f25,plain,(
% 15.47/2.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.47/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 15.47/2.52  
% 15.47/2.52  fof(f38,plain,(
% 15.47/2.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 15.47/2.52    inference(cnf_transformation,[],[f25])).
% 15.47/2.52  
% 15.47/2.52  fof(f66,plain,(
% 15.47/2.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 15.47/2.52    inference(equality_resolution,[],[f38])).
% 15.47/2.52  
% 15.47/2.52  fof(f37,plain,(
% 15.47/2.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 15.47/2.52    inference(cnf_transformation,[],[f25])).
% 15.47/2.52  
% 15.47/2.52  fof(f67,plain,(
% 15.47/2.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 15.47/2.52    inference(equality_resolution,[],[f37])).
% 15.47/2.52  
% 15.47/2.52  fof(f63,plain,(
% 15.47/2.52    r1_xboole_0(sK3,sK5)),
% 15.47/2.52    inference(cnf_transformation,[],[f35])).
% 15.47/2.52  
% 15.47/2.52  fof(f4,axiom,(
% 15.47/2.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.47/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.52  
% 15.47/2.52  fof(f15,plain,(
% 15.47/2.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.47/2.52    inference(ennf_transformation,[],[f4])).
% 15.47/2.52  
% 15.47/2.52  fof(f49,plain,(
% 15.47/2.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.47/2.52    inference(cnf_transformation,[],[f15])).
% 15.47/2.52  
% 15.47/2.52  fof(f6,axiom,(
% 15.47/2.52    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 15.47/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.52  
% 15.47/2.52  fof(f17,plain,(
% 15.47/2.52    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 15.47/2.52    inference(ennf_transformation,[],[f6])).
% 15.47/2.52  
% 15.47/2.52  fof(f55,plain,(
% 15.47/2.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 15.47/2.52    inference(cnf_transformation,[],[f17])).
% 15.47/2.52  
% 15.47/2.52  fof(f47,plain,(
% 15.47/2.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 15.47/2.52    inference(cnf_transformation,[],[f30])).
% 15.47/2.52  
% 15.47/2.52  fof(f39,plain,(
% 15.47/2.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 15.47/2.52    inference(cnf_transformation,[],[f25])).
% 15.47/2.52  
% 15.47/2.52  fof(f65,plain,(
% 15.47/2.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 15.47/2.52    inference(equality_resolution,[],[f39])).
% 15.47/2.52  
% 15.47/2.52  fof(f7,axiom,(
% 15.47/2.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.47/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.52  
% 15.47/2.52  fof(f33,plain,(
% 15.47/2.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.47/2.52    inference(nnf_transformation,[],[f7])).
% 15.47/2.52  
% 15.47/2.52  fof(f56,plain,(
% 15.47/2.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.47/2.52    inference(cnf_transformation,[],[f33])).
% 15.47/2.52  
% 15.47/2.52  fof(f64,plain,(
% 15.47/2.52    ~r1_tarski(sK3,sK4)),
% 15.47/2.52    inference(cnf_transformation,[],[f35])).
% 15.47/2.52  
% 15.47/2.52  fof(f11,axiom,(
% 15.47/2.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 15.47/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.52  
% 15.47/2.52  fof(f61,plain,(
% 15.47/2.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 15.47/2.52    inference(cnf_transformation,[],[f11])).
% 15.47/2.52  
% 15.47/2.52  cnf(c_9,plain,
% 15.47/2.52      ( r2_hidden(sK1(X0,X1,X2),X0)
% 15.47/2.52      | r2_hidden(sK1(X0,X1,X2),X2)
% 15.47/2.52      | k4_xboole_0(X0,X1) = X2 ),
% 15.47/2.52      inference(cnf_transformation,[],[f46]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_702,plain,
% 15.47/2.52      ( k4_xboole_0(X0,X1) = X2
% 15.47/2.52      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 15.47/2.52      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_22,plain,
% 15.47/2.52      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.47/2.52      inference(cnf_transformation,[],[f58]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_28,negated_conjecture,
% 15.47/2.52      ( r1_tarski(sK3,k2_xboole_0(sK4,sK5)) ),
% 15.47/2.52      inference(cnf_transformation,[],[f62]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_358,plain,
% 15.47/2.52      ( k2_xboole_0(X0,X1) = X1
% 15.47/2.52      | k2_xboole_0(sK4,sK5) != X1
% 15.47/2.52      | sK3 != X0 ),
% 15.47/2.52      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_359,plain,
% 15.47/2.52      ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK5)) = k2_xboole_0(sK4,sK5) ),
% 15.47/2.52      inference(unflattening,[status(thm)],[c_358]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_5,plain,
% 15.47/2.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 15.47/2.52      inference(cnf_transformation,[],[f66]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_706,plain,
% 15.47/2.52      ( r2_hidden(X0,X1) != iProver_top
% 15.47/2.52      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_1962,plain,
% 15.47/2.52      ( r2_hidden(X0,k2_xboole_0(sK4,sK5)) = iProver_top
% 15.47/2.52      | r2_hidden(X0,sK3) != iProver_top ),
% 15.47/2.52      inference(superposition,[status(thm)],[c_359,c_706]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_6,plain,
% 15.47/2.52      ( r2_hidden(X0,X1)
% 15.47/2.52      | r2_hidden(X0,X2)
% 15.47/2.52      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 15.47/2.52      inference(cnf_transformation,[],[f67]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_705,plain,
% 15.47/2.52      ( r2_hidden(X0,X1) = iProver_top
% 15.47/2.52      | r2_hidden(X0,X2) = iProver_top
% 15.47/2.52      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_2996,plain,
% 15.47/2.52      ( r2_hidden(X0,sK5) = iProver_top
% 15.47/2.52      | r2_hidden(X0,sK4) = iProver_top
% 15.47/2.52      | r2_hidden(X0,sK3) != iProver_top ),
% 15.47/2.52      inference(superposition,[status(thm)],[c_1962,c_705]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_27,negated_conjecture,
% 15.47/2.52      ( r1_xboole_0(sK3,sK5) ),
% 15.47/2.52      inference(cnf_transformation,[],[f63]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_692,plain,
% 15.47/2.52      ( r1_xboole_0(sK3,sK5) = iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_13,plain,
% 15.47/2.52      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.47/2.52      inference(cnf_transformation,[],[f49]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_698,plain,
% 15.47/2.52      ( r1_xboole_0(X0,X1) != iProver_top
% 15.47/2.52      | r1_xboole_0(X1,X0) = iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_1514,plain,
% 15.47/2.52      ( r1_xboole_0(sK5,sK3) = iProver_top ),
% 15.47/2.52      inference(superposition,[status(thm)],[c_692,c_698]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_16,plain,
% 15.47/2.52      ( ~ r1_xboole_0(X0,X1)
% 15.47/2.52      | ~ r2_hidden(X2,X0)
% 15.47/2.52      | ~ r2_hidden(X2,X1)
% 15.47/2.52      | ~ r2_hidden(X2,k2_xboole_0(X0,X1)) ),
% 15.47/2.52      inference(cnf_transformation,[],[f55]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_695,plain,
% 15.47/2.52      ( r1_xboole_0(X0,X1) != iProver_top
% 15.47/2.52      | r2_hidden(X2,X0) != iProver_top
% 15.47/2.52      | r2_hidden(X2,X1) != iProver_top
% 15.47/2.52      | r2_hidden(X2,k2_xboole_0(X0,X1)) != iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_1964,plain,
% 15.47/2.52      ( r1_xboole_0(X0,X1) != iProver_top
% 15.47/2.52      | r2_hidden(X2,X0) != iProver_top
% 15.47/2.52      | r2_hidden(X2,X1) != iProver_top ),
% 15.47/2.52      inference(superposition,[status(thm)],[c_706,c_695]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_2899,plain,
% 15.47/2.52      ( r2_hidden(X0,sK5) != iProver_top
% 15.47/2.52      | r2_hidden(X0,sK3) != iProver_top ),
% 15.47/2.52      inference(superposition,[status(thm)],[c_1514,c_1964]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_4011,plain,
% 15.47/2.52      ( r2_hidden(X0,sK4) = iProver_top
% 15.47/2.52      | r2_hidden(X0,sK3) != iProver_top ),
% 15.47/2.52      inference(global_propositional_subsumption,
% 15.47/2.52                [status(thm)],
% 15.47/2.52                [c_2996,c_2899]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_4017,plain,
% 15.47/2.52      ( k4_xboole_0(sK3,X0) = X1
% 15.47/2.52      | r2_hidden(sK1(sK3,X0,X1),X1) = iProver_top
% 15.47/2.52      | r2_hidden(sK1(sK3,X0,X1),sK4) = iProver_top ),
% 15.47/2.52      inference(superposition,[status(thm)],[c_702,c_4011]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_8,plain,
% 15.47/2.52      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 15.47/2.52      | r2_hidden(sK1(X0,X1,X2),X2)
% 15.47/2.52      | k4_xboole_0(X0,X1) = X2 ),
% 15.47/2.52      inference(cnf_transformation,[],[f47]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_703,plain,
% 15.47/2.52      ( k4_xboole_0(X0,X1) = X2
% 15.47/2.52      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 15.47/2.52      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_33068,plain,
% 15.47/2.52      ( k4_xboole_0(sK3,sK4) = X0
% 15.47/2.52      | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
% 15.47/2.52      inference(superposition,[status(thm)],[c_4017,c_703]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_33099,plain,
% 15.47/2.52      ( k4_xboole_0(sK3,sK4) = k1_xboole_0
% 15.47/2.52      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 15.47/2.52      inference(instantiation,[status(thm)],[c_33068]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_4,plain,
% 15.47/2.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 15.47/2.52      inference(cnf_transformation,[],[f65]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_2403,plain,
% 15.47/2.52      ( r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0))
% 15.47/2.52      | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) ),
% 15.47/2.52      inference(instantiation,[status(thm)],[c_4]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_2409,plain,
% 15.47/2.52      ( r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0)) = iProver_top
% 15.47/2.52      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_2403]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_2411,plain,
% 15.47/2.52      ( r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top
% 15.47/2.52      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.47/2.52      inference(instantiation,[status(thm)],[c_2409]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_1158,plain,
% 15.47/2.52      ( ~ r1_xboole_0(k1_xboole_0,X0)
% 15.47/2.52      | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),X0)
% 15.47/2.52      | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(k1_xboole_0,X0))
% 15.47/2.52      | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) ),
% 15.47/2.52      inference(instantiation,[status(thm)],[c_16]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_1159,plain,
% 15.47/2.52      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 15.47/2.52      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),X0) != iProver_top
% 15.47/2.52      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(k1_xboole_0,X0)) != iProver_top
% 15.47/2.52      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_1158]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_1161,plain,
% 15.47/2.52      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 15.47/2.52      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 15.47/2.52      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.47/2.52      inference(instantiation,[status(thm)],[c_1159]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_21,plain,
% 15.47/2.52      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.47/2.52      inference(cnf_transformation,[],[f56]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_198,plain,
% 15.47/2.52      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.47/2.52      inference(prop_impl,[status(thm)],[c_21]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_26,negated_conjecture,
% 15.47/2.52      ( ~ r1_tarski(sK3,sK4) ),
% 15.47/2.52      inference(cnf_transformation,[],[f64]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_353,plain,
% 15.47/2.52      ( k4_xboole_0(X0,X1) != k1_xboole_0 | sK4 != X1 | sK3 != X0 ),
% 15.47/2.52      inference(resolution_lifted,[status(thm)],[c_198,c_26]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_354,plain,
% 15.47/2.52      ( k4_xboole_0(sK3,sK4) != k1_xboole_0 ),
% 15.47/2.52      inference(unflattening,[status(thm)],[c_353]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_25,plain,
% 15.47/2.52      ( r1_xboole_0(X0,k1_xboole_0) ),
% 15.47/2.52      inference(cnf_transformation,[],[f61]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_32,plain,
% 15.47/2.52      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 15.47/2.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(c_34,plain,
% 15.47/2.52      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.47/2.52      inference(instantiation,[status(thm)],[c_32]) ).
% 15.47/2.52  
% 15.47/2.52  cnf(contradiction,plain,
% 15.47/2.52      ( $false ),
% 15.47/2.52      inference(minisat,[status(thm)],[c_33099,c_2411,c_1161,c_354,c_34]) ).
% 15.47/2.52  
% 15.47/2.52  
% 15.47/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.47/2.52  
% 15.47/2.52  ------                               Statistics
% 15.47/2.52  
% 15.47/2.52  ------ General
% 15.47/2.52  
% 15.47/2.52  abstr_ref_over_cycles:                  0
% 15.47/2.52  abstr_ref_under_cycles:                 0
% 15.47/2.52  gc_basic_clause_elim:                   0
% 15.47/2.52  forced_gc_time:                         0
% 15.47/2.52  parsing_time:                           0.009
% 15.47/2.52  unif_index_cands_time:                  0.
% 15.47/2.52  unif_index_add_time:                    0.
% 15.47/2.52  orderings_time:                         0.
% 15.47/2.52  out_proof_time:                         0.013
% 15.47/2.52  total_time:                             1.52
% 15.47/2.52  num_of_symbols:                         44
% 15.47/2.52  num_of_terms:                           41716
% 15.47/2.52  
% 15.47/2.52  ------ Preprocessing
% 15.47/2.52  
% 15.47/2.52  num_of_splits:                          0
% 15.47/2.52  num_of_split_atoms:                     0
% 15.47/2.52  num_of_reused_defs:                     0
% 15.47/2.52  num_eq_ax_congr_red:                    20
% 15.47/2.52  num_of_sem_filtered_clauses:            1
% 15.47/2.52  num_of_subtypes:                        0
% 15.47/2.52  monotx_restored_types:                  0
% 15.47/2.52  sat_num_of_epr_types:                   0
% 15.47/2.52  sat_num_of_non_cyclic_types:            0
% 15.47/2.52  sat_guarded_non_collapsed_types:        0
% 15.47/2.52  num_pure_diseq_elim:                    0
% 15.47/2.52  simp_replaced_by:                       0
% 15.47/2.52  res_preprocessed:                       100
% 15.47/2.52  prep_upred:                             0
% 15.47/2.52  prep_unflattend:                        11
% 15.47/2.52  smt_new_axioms:                         0
% 15.47/2.52  pred_elim_cands:                        3
% 15.47/2.52  pred_elim:                              1
% 15.47/2.52  pred_elim_cl:                           -2
% 15.47/2.52  pred_elim_cycles:                       2
% 15.47/2.52  merged_defs:                            2
% 15.47/2.52  merged_defs_ncl:                        0
% 15.47/2.52  bin_hyper_res:                          2
% 15.47/2.52  prep_cycles:                            3
% 15.47/2.52  pred_elim_time:                         0.002
% 15.47/2.52  splitting_time:                         0.
% 15.47/2.52  sem_filter_time:                        0.
% 15.47/2.52  monotx_time:                            0.001
% 15.47/2.52  subtype_inf_time:                       0.
% 15.47/2.52  
% 15.47/2.52  ------ Problem properties
% 15.47/2.52  
% 15.47/2.52  clauses:                                29
% 15.47/2.52  conjectures:                            1
% 15.47/2.52  epr:                                    3
% 15.47/2.52  horn:                                   21
% 15.47/2.52  ground:                                 5
% 15.47/2.52  unary:                                  10
% 15.47/2.52  binary:                                 9
% 15.47/2.52  lits:                                   62
% 15.47/2.52  lits_eq:                                18
% 15.47/2.52  fd_pure:                                0
% 15.47/2.52  fd_pseudo:                              0
% 15.47/2.52  fd_cond:                                0
% 15.47/2.52  fd_pseudo_cond:                         6
% 15.47/2.52  ac_symbols:                             0
% 15.47/2.52  
% 15.47/2.52  ------ Propositional Solver
% 15.47/2.52  
% 15.47/2.52  prop_solver_calls:                      28
% 15.47/2.52  prop_fast_solver_calls:                 1125
% 15.47/2.52  smt_solver_calls:                       0
% 15.47/2.52  smt_fast_solver_calls:                  0
% 15.47/2.52  prop_num_of_clauses:                    14096
% 15.47/2.52  prop_preprocess_simplified:             23933
% 15.47/2.52  prop_fo_subsumed:                       19
% 15.47/2.52  prop_solver_time:                       0.
% 15.47/2.52  smt_solver_time:                        0.
% 15.47/2.52  smt_fast_solver_time:                   0.
% 15.47/2.52  prop_fast_solver_time:                  0.
% 15.47/2.52  prop_unsat_core_time:                   0.002
% 15.47/2.52  
% 15.47/2.52  ------ QBF
% 15.47/2.52  
% 15.47/2.52  qbf_q_res:                              0
% 15.47/2.52  qbf_num_tautologies:                    0
% 15.47/2.52  qbf_prep_cycles:                        0
% 15.47/2.52  
% 15.47/2.52  ------ BMC1
% 15.47/2.52  
% 15.47/2.52  bmc1_current_bound:                     -1
% 15.47/2.52  bmc1_last_solved_bound:                 -1
% 15.47/2.52  bmc1_unsat_core_size:                   -1
% 15.47/2.52  bmc1_unsat_core_parents_size:           -1
% 15.47/2.52  bmc1_merge_next_fun:                    0
% 15.47/2.52  bmc1_unsat_core_clauses_time:           0.
% 15.47/2.52  
% 15.47/2.52  ------ Instantiation
% 15.47/2.52  
% 15.47/2.52  inst_num_of_clauses:                    3101
% 15.47/2.52  inst_num_in_passive:                    1554
% 15.47/2.52  inst_num_in_active:                     915
% 15.47/2.52  inst_num_in_unprocessed:                635
% 15.47/2.52  inst_num_of_loops:                      1080
% 15.47/2.52  inst_num_of_learning_restarts:          0
% 15.47/2.52  inst_num_moves_active_passive:          165
% 15.47/2.52  inst_lit_activity:                      0
% 15.47/2.52  inst_lit_activity_moves:                0
% 15.47/2.52  inst_num_tautologies:                   0
% 15.47/2.52  inst_num_prop_implied:                  0
% 15.47/2.52  inst_num_existing_simplified:           0
% 15.47/2.52  inst_num_eq_res_simplified:             0
% 15.47/2.52  inst_num_child_elim:                    0
% 15.47/2.52  inst_num_of_dismatching_blockings:      6170
% 15.47/2.52  inst_num_of_non_proper_insts:           4163
% 15.47/2.52  inst_num_of_duplicates:                 0
% 15.47/2.52  inst_inst_num_from_inst_to_res:         0
% 15.47/2.52  inst_dismatching_checking_time:         0.
% 15.47/2.52  
% 15.47/2.52  ------ Resolution
% 15.47/2.52  
% 15.47/2.52  res_num_of_clauses:                     0
% 15.47/2.52  res_num_in_passive:                     0
% 15.47/2.52  res_num_in_active:                      0
% 15.47/2.52  res_num_of_loops:                       103
% 15.47/2.52  res_forward_subset_subsumed:            120
% 15.47/2.52  res_backward_subset_subsumed:           6
% 15.47/2.52  res_forward_subsumed:                   0
% 15.47/2.52  res_backward_subsumed:                  0
% 15.47/2.52  res_forward_subsumption_resolution:     0
% 15.47/2.52  res_backward_subsumption_resolution:    0
% 15.47/2.52  res_clause_to_clause_subsumption:       31518
% 15.47/2.52  res_orphan_elimination:                 0
% 15.47/2.52  res_tautology_del:                      91
% 15.47/2.52  res_num_eq_res_simplified:              1
% 15.47/2.52  res_num_sel_changes:                    0
% 15.47/2.52  res_moves_from_active_to_pass:          0
% 15.47/2.52  
% 15.47/2.52  ------ Superposition
% 15.47/2.52  
% 15.47/2.52  sup_time_total:                         0.
% 15.47/2.52  sup_time_generating:                    0.
% 15.47/2.52  sup_time_sim_full:                      0.
% 15.47/2.52  sup_time_sim_immed:                     0.
% 15.47/2.52  
% 15.47/2.52  sup_num_of_clauses:                     1594
% 15.47/2.52  sup_num_in_active:                      201
% 15.47/2.52  sup_num_in_passive:                     1393
% 15.47/2.52  sup_num_of_loops:                       214
% 15.47/2.52  sup_fw_superposition:                   2023
% 15.47/2.52  sup_bw_superposition:                   1193
% 15.47/2.52  sup_immediate_simplified:               1281
% 15.47/2.52  sup_given_eliminated:                   2
% 15.47/2.52  comparisons_done:                       0
% 15.47/2.52  comparisons_avoided:                    6
% 15.47/2.52  
% 15.47/2.52  ------ Simplifications
% 15.47/2.52  
% 15.47/2.52  
% 15.47/2.52  sim_fw_subset_subsumed:                 199
% 15.47/2.52  sim_bw_subset_subsumed:                 24
% 15.47/2.52  sim_fw_subsumed:                        683
% 15.47/2.52  sim_bw_subsumed:                        116
% 15.47/2.52  sim_fw_subsumption_res:                 0
% 15.47/2.52  sim_bw_subsumption_res:                 0
% 15.47/2.52  sim_tautology_del:                      60
% 15.47/2.52  sim_eq_tautology_del:                   24
% 15.47/2.52  sim_eq_res_simp:                        107
% 15.47/2.52  sim_fw_demodulated:                     337
% 15.47/2.52  sim_bw_demodulated:                     1
% 15.47/2.52  sim_light_normalised:                   441
% 15.47/2.52  sim_joinable_taut:                      0
% 15.47/2.52  sim_joinable_simp:                      0
% 15.47/2.52  sim_ac_normalised:                      0
% 15.47/2.52  sim_smt_subsumption:                    0
% 15.47/2.52  
%------------------------------------------------------------------------------
