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
% DateTime   : Thu Dec  3 11:32:54 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 174 expanded)
%              Number of clauses        :   25 (  32 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  243 ( 536 expanded)
%              Number of equality atoms :  137 ( 361 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f67,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

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
    inference(nnf_transformation,[],[f19])).

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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f86,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f87,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK2,sK3)
      & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r2_hidden(sK2,sK3)
    & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f33])).

fof(f61,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) ),
    inference(definition_unfolding,[],[f61,f60,f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f82,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f83,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f82])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_14,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_559,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_727,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_559])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_557,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_555,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_567,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1630,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3
    | r1_tarski(sK3,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_567])).

cnf(c_1648,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3
    | r2_hidden(sK3,k2_tarski(k2_tarski(sK2,sK2),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_1630])).

cnf(c_12,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_561,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_878,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_561])).

cnf(c_1741,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1648,c_878])).

cnf(c_1743,plain,
    ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK2),sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1741,c_557])).

cnf(c_2252,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_1743])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_568,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9988,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_568])).

cnf(c_14098,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_9988])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14098,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.34/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/1.00  
% 3.34/1.00  ------  iProver source info
% 3.34/1.00  
% 3.34/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.34/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/1.00  git: non_committed_changes: false
% 3.34/1.00  git: last_make_outside_of_git: false
% 3.34/1.00  
% 3.34/1.00  ------ 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options
% 3.34/1.00  
% 3.34/1.00  --out_options                           all
% 3.34/1.00  --tptp_safe_out                         true
% 3.34/1.00  --problem_path                          ""
% 3.34/1.00  --include_path                          ""
% 3.34/1.00  --clausifier                            res/vclausify_rel
% 3.34/1.00  --clausifier_options                    --mode clausify
% 3.34/1.00  --stdin                                 false
% 3.34/1.00  --stats_out                             all
% 3.34/1.00  
% 3.34/1.00  ------ General Options
% 3.34/1.00  
% 3.34/1.00  --fof                                   false
% 3.34/1.00  --time_out_real                         305.
% 3.34/1.00  --time_out_virtual                      -1.
% 3.34/1.00  --symbol_type_check                     false
% 3.34/1.00  --clausify_out                          false
% 3.34/1.00  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         false
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     num_symb
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       true
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     false
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   []
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_full_bw                           [BwDemod]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  ------ Parsing...
% 3.34/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/1.00  ------ Proving...
% 3.34/1.00  ------ Problem Properties 
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  clauses                                 20
% 3.34/1.00  conjectures                             2
% 3.34/1.00  EPR                                     4
% 3.34/1.00  Horn                                    17
% 3.34/1.00  unary                                   10
% 3.34/1.00  binary                                  3
% 3.34/1.00  lits                                    40
% 3.34/1.00  lits eq                                 18
% 3.34/1.00  fd_pure                                 0
% 3.34/1.00  fd_pseudo                               0
% 3.34/1.00  fd_cond                                 0
% 3.34/1.00  fd_pseudo_cond                          5
% 3.34/1.00  AC symbols                              0
% 3.34/1.00  
% 3.34/1.00  ------ Schedule dynamic 5 is on 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ 
% 3.34/1.00  Current options:
% 3.34/1.00  ------ 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options
% 3.34/1.00  
% 3.34/1.00  --out_options                           all
% 3.34/1.00  --tptp_safe_out                         true
% 3.34/1.00  --problem_path                          ""
% 3.34/1.00  --include_path                          ""
% 3.34/1.00  --clausifier                            res/vclausify_rel
% 3.34/1.00  --clausifier_options                    --mode clausify
% 3.34/1.00  --stdin                                 false
% 3.34/1.00  --stats_out                             all
% 3.34/1.00  
% 3.34/1.00  ------ General Options
% 3.34/1.00  
% 3.34/1.00  --fof                                   false
% 3.34/1.00  --time_out_real                         305.
% 3.34/1.00  --time_out_virtual                      -1.
% 3.34/1.00  --symbol_type_check                     false
% 3.34/1.00  --clausify_out                          false
% 3.34/1.00  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         false
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     none
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       false
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     false
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   []
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_full_bw                           [BwDemod]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ Proving...
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  % SZS status Theorem for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  fof(f8,axiom,(
% 3.34/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f53,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f8])).
% 3.34/1.00  
% 3.34/1.00  fof(f9,axiom,(
% 3.34/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f54,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f9])).
% 3.34/1.00  
% 3.34/1.00  fof(f10,axiom,(
% 3.34/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f55,plain,(
% 3.34/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f10])).
% 3.34/1.00  
% 3.34/1.00  fof(f11,axiom,(
% 3.34/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f56,plain,(
% 3.34/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f11])).
% 3.34/1.00  
% 3.34/1.00  fof(f12,axiom,(
% 3.34/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f57,plain,(
% 3.34/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f12])).
% 3.34/1.00  
% 3.34/1.00  fof(f63,plain,(
% 3.34/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.34/1.00    inference(definition_unfolding,[],[f56,f57])).
% 3.34/1.00  
% 3.34/1.00  fof(f64,plain,(
% 3.34/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.34/1.00    inference(definition_unfolding,[],[f55,f63])).
% 3.34/1.00  
% 3.34/1.00  fof(f65,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.34/1.00    inference(definition_unfolding,[],[f54,f64])).
% 3.34/1.00  
% 3.34/1.00  fof(f67,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.34/1.00    inference(definition_unfolding,[],[f53,f65])).
% 3.34/1.00  
% 3.34/1.00  fof(f3,axiom,(
% 3.34/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f19,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.34/1.00    inference(ennf_transformation,[],[f3])).
% 3.34/1.00  
% 3.34/1.00  fof(f28,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.34/1.00    inference(nnf_transformation,[],[f19])).
% 3.34/1.00  
% 3.34/1.00  fof(f29,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.34/1.00    inference(flattening,[],[f28])).
% 3.34/1.00  
% 3.34/1.00  fof(f30,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.34/1.00    inference(rectify,[],[f29])).
% 3.34/1.00  
% 3.34/1.00  fof(f31,plain,(
% 3.34/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f32,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.34/1.00  
% 3.34/1.00  fof(f42,plain,(
% 3.34/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.34/1.00    inference(cnf_transformation,[],[f32])).
% 3.34/1.00  
% 3.34/1.00  fof(f75,plain,(
% 3.34/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.34/1.00    inference(definition_unfolding,[],[f42,f65])).
% 3.34/1.00  
% 3.34/1.00  fof(f86,plain,(
% 3.34/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.34/1.00    inference(equality_resolution,[],[f75])).
% 3.34/1.00  
% 3.34/1.00  fof(f87,plain,(
% 3.34/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 3.34/1.00    inference(equality_resolution,[],[f86])).
% 3.34/1.00  
% 3.34/1.00  fof(f14,axiom,(
% 3.34/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f20,plain,(
% 3.34/1.00    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 3.34/1.00    inference(ennf_transformation,[],[f14])).
% 3.34/1.00  
% 3.34/1.00  fof(f59,plain,(
% 3.34/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f20])).
% 3.34/1.00  
% 3.34/1.00  fof(f16,conjecture,(
% 3.34/1.00    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f17,negated_conjecture,(
% 3.34/1.00    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.34/1.00    inference(negated_conjecture,[],[f16])).
% 3.34/1.00  
% 3.34/1.00  fof(f21,plain,(
% 3.34/1.00    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 3.34/1.00    inference(ennf_transformation,[],[f17])).
% 3.34/1.00  
% 3.34/1.00  fof(f33,plain,(
% 3.34/1.00    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f34,plain,(
% 3.34/1.00    ~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f33])).
% 3.34/1.00  
% 3.34/1.00  fof(f61,plain,(
% 3.34/1.00    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 3.34/1.00    inference(cnf_transformation,[],[f34])).
% 3.34/1.00  
% 3.34/1.00  fof(f15,axiom,(
% 3.34/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f60,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f15])).
% 3.34/1.00  
% 3.34/1.00  fof(f7,axiom,(
% 3.34/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f52,plain,(
% 3.34/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f7])).
% 3.34/1.00  
% 3.34/1.00  fof(f79,plain,(
% 3.34/1.00    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3)),
% 3.34/1.00    inference(definition_unfolding,[],[f61,f60,f52])).
% 3.34/1.00  
% 3.34/1.00  fof(f2,axiom,(
% 3.34/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f26,plain,(
% 3.34/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.00    inference(nnf_transformation,[],[f2])).
% 3.34/1.00  
% 3.34/1.00  fof(f27,plain,(
% 3.34/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.00    inference(flattening,[],[f26])).
% 3.34/1.00  
% 3.34/1.00  fof(f40,plain,(
% 3.34/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f27])).
% 3.34/1.00  
% 3.34/1.00  fof(f44,plain,(
% 3.34/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.34/1.00    inference(cnf_transformation,[],[f32])).
% 3.34/1.00  
% 3.34/1.00  fof(f73,plain,(
% 3.34/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.34/1.00    inference(definition_unfolding,[],[f44,f65])).
% 3.34/1.00  
% 3.34/1.00  fof(f82,plain,(
% 3.34/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 3.34/1.00    inference(equality_resolution,[],[f73])).
% 3.34/1.00  
% 3.34/1.00  fof(f83,plain,(
% 3.34/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 3.34/1.00    inference(equality_resolution,[],[f82])).
% 3.34/1.00  
% 3.34/1.00  fof(f1,axiom,(
% 3.34/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f18,plain,(
% 3.34/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f1])).
% 3.34/1.00  
% 3.34/1.00  fof(f22,plain,(
% 3.34/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/1.00    inference(nnf_transformation,[],[f18])).
% 3.34/1.00  
% 3.34/1.00  fof(f23,plain,(
% 3.34/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/1.00    inference(rectify,[],[f22])).
% 3.34/1.00  
% 3.34/1.00  fof(f24,plain,(
% 3.34/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f25,plain,(
% 3.34/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.34/1.00  
% 3.34/1.00  fof(f35,plain,(
% 3.34/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f25])).
% 3.34/1.00  
% 3.34/1.00  fof(f62,plain,(
% 3.34/1.00    ~r2_hidden(sK2,sK3)),
% 3.34/1.00    inference(cnf_transformation,[],[f34])).
% 3.34/1.00  
% 3.34/1.00  cnf(c_0,plain,
% 3.34/1.00      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_14,plain,
% 3.34/1.00      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_559,plain,
% 3.34/1.00      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_727,plain,
% 3.34/1.00      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_0,c_559]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_18,plain,
% 3.34/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_557,plain,
% 3.34/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.34/1.00      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_20,negated_conjecture,
% 3.34/1.00      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) ),
% 3.34/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_555,plain,
% 3.34/1.00      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_5,plain,
% 3.34/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.34/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_567,plain,
% 3.34/1.00      ( X0 = X1
% 3.34/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.34/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1630,plain,
% 3.34/1.00      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3
% 3.34/1.00      | r1_tarski(sK3,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3))) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_555,c_567]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1648,plain,
% 3.34/1.00      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3
% 3.34/1.00      | r2_hidden(sK3,k2_tarski(k2_tarski(sK2,sK2),sK3)) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_557,c_1630]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_12,plain,
% 3.34/1.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_561,plain,
% 3.34/1.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_878,plain,
% 3.34/1.00      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_0,c_561]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1741,plain,
% 3.34/1.00      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3 ),
% 3.34/1.00      inference(forward_subsumption_resolution,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_1648,c_878]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1743,plain,
% 3.34/1.00      ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK2),sK3)) != iProver_top
% 3.34/1.00      | r1_tarski(X0,sK3) = iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1741,c_557]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2252,plain,
% 3.34/1.00      ( r1_tarski(k2_tarski(sK2,sK2),sK3) = iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_727,c_1743]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4,plain,
% 3.34/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.34/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_568,plain,
% 3.34/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.34/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.34/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_9988,plain,
% 3.34/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.34/1.00      | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_727,c_568]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_14098,plain,
% 3.34/1.00      ( r2_hidden(sK2,sK3) = iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_2252,c_9988]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_19,negated_conjecture,
% 3.34/1.00      ( ~ r2_hidden(sK2,sK3) ),
% 3.34/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_22,plain,
% 3.34/1.00      ( r2_hidden(sK2,sK3) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(contradiction,plain,
% 3.34/1.00      ( $false ),
% 3.34/1.00      inference(minisat,[status(thm)],[c_14098,c_22]) ).
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  ------                               Statistics
% 3.34/1.00  
% 3.34/1.00  ------ General
% 3.34/1.00  
% 3.34/1.00  abstr_ref_over_cycles:                  0
% 3.34/1.00  abstr_ref_under_cycles:                 0
% 3.34/1.00  gc_basic_clause_elim:                   0
% 3.34/1.00  forced_gc_time:                         0
% 3.34/1.00  parsing_time:                           0.028
% 3.34/1.00  unif_index_cands_time:                  0.
% 3.34/1.00  unif_index_add_time:                    0.
% 3.34/1.00  orderings_time:                         0.
% 3.34/1.00  out_proof_time:                         0.007
% 3.34/1.00  total_time:                             0.456
% 3.34/1.00  num_of_symbols:                         40
% 3.34/1.00  num_of_terms:                           19584
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing
% 3.34/1.00  
% 3.34/1.00  num_of_splits:                          0
% 3.34/1.00  num_of_split_atoms:                     0
% 3.34/1.00  num_of_reused_defs:                     0
% 3.34/1.00  num_eq_ax_congr_red:                    39
% 3.34/1.00  num_of_sem_filtered_clauses:            1
% 3.34/1.00  num_of_subtypes:                        0
% 3.34/1.00  monotx_restored_types:                  0
% 3.34/1.00  sat_num_of_epr_types:                   0
% 3.34/1.00  sat_num_of_non_cyclic_types:            0
% 3.34/1.00  sat_guarded_non_collapsed_types:        0
% 3.34/1.00  num_pure_diseq_elim:                    0
% 3.34/1.00  simp_replaced_by:                       0
% 3.34/1.00  res_preprocessed:                       93
% 3.34/1.00  prep_upred:                             0
% 3.34/1.00  prep_unflattend:                        0
% 3.34/1.00  smt_new_axioms:                         0
% 3.34/1.00  pred_elim_cands:                        2
% 3.34/1.00  pred_elim:                              0
% 3.34/1.00  pred_elim_cl:                           0
% 3.34/1.00  pred_elim_cycles:                       2
% 3.34/1.00  merged_defs:                            0
% 3.34/1.00  merged_defs_ncl:                        0
% 3.34/1.00  bin_hyper_res:                          0
% 3.34/1.00  prep_cycles:                            4
% 3.34/1.00  pred_elim_time:                         0.
% 3.34/1.00  splitting_time:                         0.
% 3.34/1.00  sem_filter_time:                        0.
% 3.34/1.00  monotx_time:                            0.
% 3.34/1.00  subtype_inf_time:                       0.
% 3.34/1.00  
% 3.34/1.00  ------ Problem properties
% 3.34/1.00  
% 3.34/1.00  clauses:                                20
% 3.34/1.00  conjectures:                            2
% 3.34/1.00  epr:                                    4
% 3.34/1.00  horn:                                   17
% 3.34/1.00  ground:                                 2
% 3.34/1.00  unary:                                  10
% 3.34/1.00  binary:                                 3
% 3.34/1.00  lits:                                   40
% 3.34/1.00  lits_eq:                                18
% 3.34/1.00  fd_pure:                                0
% 3.34/1.00  fd_pseudo:                              0
% 3.34/1.00  fd_cond:                                0
% 3.34/1.00  fd_pseudo_cond:                         5
% 3.34/1.00  ac_symbols:                             0
% 3.34/1.00  
% 3.34/1.00  ------ Propositional Solver
% 3.34/1.00  
% 3.34/1.00  prop_solver_calls:                      29
% 3.34/1.00  prop_fast_solver_calls:                 572
% 3.34/1.00  smt_solver_calls:                       0
% 3.34/1.00  smt_fast_solver_calls:                  0
% 3.34/1.00  prop_num_of_clauses:                    4648
% 3.34/1.00  prop_preprocess_simplified:             12456
% 3.34/1.00  prop_fo_subsumed:                       0
% 3.34/1.00  prop_solver_time:                       0.
% 3.34/1.00  smt_solver_time:                        0.
% 3.34/1.00  smt_fast_solver_time:                   0.
% 3.34/1.00  prop_fast_solver_time:                  0.
% 3.34/1.00  prop_unsat_core_time:                   0.
% 3.34/1.00  
% 3.34/1.00  ------ QBF
% 3.34/1.00  
% 3.34/1.00  qbf_q_res:                              0
% 3.34/1.00  qbf_num_tautologies:                    0
% 3.34/1.00  qbf_prep_cycles:                        0
% 3.34/1.00  
% 3.34/1.00  ------ BMC1
% 3.34/1.00  
% 3.34/1.00  bmc1_current_bound:                     -1
% 3.34/1.00  bmc1_last_solved_bound:                 -1
% 3.34/1.00  bmc1_unsat_core_size:                   -1
% 3.34/1.00  bmc1_unsat_core_parents_size:           -1
% 3.34/1.00  bmc1_merge_next_fun:                    0
% 3.34/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation
% 3.34/1.00  
% 3.34/1.00  inst_num_of_clauses:                    1358
% 3.34/1.00  inst_num_in_passive:                    568
% 3.34/1.00  inst_num_in_active:                     413
% 3.34/1.00  inst_num_in_unprocessed:                377
% 3.34/1.00  inst_num_of_loops:                      560
% 3.34/1.00  inst_num_of_learning_restarts:          0
% 3.34/1.00  inst_num_moves_active_passive:          145
% 3.34/1.00  inst_lit_activity:                      0
% 3.34/1.00  inst_lit_activity_moves:                0
% 3.34/1.00  inst_num_tautologies:                   0
% 3.34/1.00  inst_num_prop_implied:                  0
% 3.34/1.00  inst_num_existing_simplified:           0
% 3.34/1.00  inst_num_eq_res_simplified:             0
% 3.34/1.00  inst_num_child_elim:                    0
% 3.34/1.00  inst_num_of_dismatching_blockings:      1164
% 3.34/1.00  inst_num_of_non_proper_insts:           1560
% 3.34/1.00  inst_num_of_duplicates:                 0
% 3.34/1.00  inst_inst_num_from_inst_to_res:         0
% 3.34/1.00  inst_dismatching_checking_time:         0.
% 3.34/1.00  
% 3.34/1.00  ------ Resolution
% 3.34/1.00  
% 3.34/1.00  res_num_of_clauses:                     0
% 3.34/1.00  res_num_in_passive:                     0
% 3.34/1.00  res_num_in_active:                      0
% 3.34/1.00  res_num_of_loops:                       97
% 3.34/1.00  res_forward_subset_subsumed:            131
% 3.34/1.00  res_backward_subset_subsumed:           6
% 3.34/1.00  res_forward_subsumed:                   0
% 3.34/1.00  res_backward_subsumed:                  0
% 3.34/1.00  res_forward_subsumption_resolution:     0
% 3.34/1.00  res_backward_subsumption_resolution:    0
% 3.34/1.00  res_clause_to_clause_subsumption:       3049
% 3.34/1.00  res_orphan_elimination:                 0
% 3.34/1.00  res_tautology_del:                      49
% 3.34/1.00  res_num_eq_res_simplified:              0
% 3.34/1.00  res_num_sel_changes:                    0
% 3.34/1.00  res_moves_from_active_to_pass:          0
% 3.34/1.00  
% 3.34/1.00  ------ Superposition
% 3.34/1.00  
% 3.34/1.00  sup_time_total:                         0.
% 3.34/1.00  sup_time_generating:                    0.
% 3.34/1.00  sup_time_sim_full:                      0.
% 3.34/1.00  sup_time_sim_immed:                     0.
% 3.34/1.00  
% 3.34/1.00  sup_num_of_clauses:                     340
% 3.34/1.00  sup_num_in_active:                      94
% 3.34/1.00  sup_num_in_passive:                     246
% 3.34/1.00  sup_num_of_loops:                       110
% 3.34/1.00  sup_fw_superposition:                   1053
% 3.34/1.00  sup_bw_superposition:                   958
% 3.34/1.00  sup_immediate_simplified:               153
% 3.34/1.00  sup_given_eliminated:                   0
% 3.34/1.00  comparisons_done:                       0
% 3.34/1.00  comparisons_avoided:                    48
% 3.34/1.00  
% 3.34/1.00  ------ Simplifications
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  sim_fw_subset_subsumed:                 0
% 3.34/1.00  sim_bw_subset_subsumed:                 1
% 3.34/1.00  sim_fw_subsumed:                        10
% 3.34/1.00  sim_bw_subsumed:                        4
% 3.34/1.00  sim_fw_subsumption_res:                 1
% 3.34/1.00  sim_bw_subsumption_res:                 0
% 3.34/1.00  sim_tautology_del:                      0
% 3.34/1.00  sim_eq_tautology_del:                   24
% 3.34/1.00  sim_eq_res_simp:                        0
% 3.34/1.00  sim_fw_demodulated:                     78
% 3.34/1.00  sim_bw_demodulated:                     19
% 3.34/1.00  sim_light_normalised:                   68
% 3.34/1.00  sim_joinable_taut:                      0
% 3.34/1.00  sim_joinable_simp:                      0
% 3.34/1.00  sim_ac_normalised:                      0
% 3.34/1.00  sim_smt_subsumption:                    0
% 3.34/1.00  
%------------------------------------------------------------------------------
