%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:37 EST 2020

% Result     : Theorem 23.54s
% Output     : CNFRefutation 23.54s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 178 expanded)
%              Number of clauses        :   52 (  60 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   19
%              Number of atoms          :  300 ( 662 expanded)
%              Number of equality atoms :   82 ( 110 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

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
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)
      & r1_xboole_0(sK5,sK4)
      & r2_hidden(sK6,sK5)
      & r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)
    & r1_xboole_0(sK5,sK4)
    & r2_hidden(sK6,sK5)
    & r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f38])).

fof(f68,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f69,plain,(
    r1_xboole_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,(
    r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(definition_unfolding,[],[f67,f56,f71])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1144,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1145,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1152,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1132,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1136,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1133,plain,
    ( r1_xboole_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1147,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2526,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1133,c_1147])).

cnf(c_20,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1137,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2839,plain,
    ( k4_xboole_0(sK4,sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_2526,c_1137])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1151,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4958,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2839,c_1151])).

cnf(c_5414,plain,
    ( k4_xboole_0(sK4,k2_enumset1(X0,X0,X0,X0)) = sK4
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_4958])).

cnf(c_6337,plain,
    ( k4_xboole_0(sK4,k2_enumset1(sK6,sK6,sK6,sK6)) = sK4 ),
    inference(superposition,[status(thm)],[c_1132,c_5414])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_353,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | k2_enumset1(sK6,sK6,sK6,sK6) != X2
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_354,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(X0,k2_enumset1(sK6,sK6,sK6,sK6))) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1131,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(X0,k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_2528,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_enumset1(sK6,sK6,sK6,sK6)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_1147])).

cnf(c_6596,plain,
    ( r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6337,c_2528])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1146,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6924,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6596,c_1146])).

cnf(c_8245,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_6924])).

cnf(c_10933,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8245,c_1151])).

cnf(c_11170,plain,
    ( r1_xboole_0(X0,sK4) = iProver_top
    | r2_hidden(sK1(X0,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_10933])).

cnf(c_102740,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1144,c_11170])).

cnf(c_2406,plain,
    ( ~ r1_xboole_0(X0,sK4)
    | r1_xboole_0(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_27067,plain,
    ( r1_xboole_0(sK4,sK3)
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2406])).

cnf(c_27068,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27067])).

cnf(c_1619,plain,
    ( r1_xboole_0(X0,sK5)
    | ~ r1_xboole_0(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2298,plain,
    ( r1_xboole_0(sK4,sK5)
    | ~ r1_xboole_0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_2299,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top
    | r1_xboole_0(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2298])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1377,plain,
    ( r1_xboole_0(sK4,k2_xboole_0(sK3,sK5))
    | ~ r1_xboole_0(sK4,sK5)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1378,plain,
    ( r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = iProver_top
    | r1_xboole_0(sK4,sK5) != iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1377])).

cnf(c_1210,plain,
    ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)
    | ~ r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1211,plain,
    ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) = iProver_top
    | r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1210])).

cnf(c_24,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,plain,
    ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( r1_xboole_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_102740,c_27068,c_2299,c_1378,c_1211,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:42:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 23.54/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.54/3.50  
% 23.54/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.54/3.50  
% 23.54/3.50  ------  iProver source info
% 23.54/3.50  
% 23.54/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.54/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.54/3.50  git: non_committed_changes: false
% 23.54/3.50  git: last_make_outside_of_git: false
% 23.54/3.50  
% 23.54/3.50  ------ 
% 23.54/3.50  
% 23.54/3.50  ------ Input Options
% 23.54/3.50  
% 23.54/3.50  --out_options                           all
% 23.54/3.50  --tptp_safe_out                         true
% 23.54/3.50  --problem_path                          ""
% 23.54/3.50  --include_path                          ""
% 23.54/3.50  --clausifier                            res/vclausify_rel
% 23.54/3.50  --clausifier_options                    ""
% 23.54/3.50  --stdin                                 false
% 23.54/3.50  --stats_out                             all
% 23.54/3.50  
% 23.54/3.50  ------ General Options
% 23.54/3.50  
% 23.54/3.50  --fof                                   false
% 23.54/3.50  --time_out_real                         305.
% 23.54/3.50  --time_out_virtual                      -1.
% 23.54/3.50  --symbol_type_check                     false
% 23.54/3.50  --clausify_out                          false
% 23.54/3.50  --sig_cnt_out                           false
% 23.54/3.50  --trig_cnt_out                          false
% 23.54/3.50  --trig_cnt_out_tolerance                1.
% 23.54/3.50  --trig_cnt_out_sk_spl                   false
% 23.54/3.50  --abstr_cl_out                          false
% 23.54/3.50  
% 23.54/3.50  ------ Global Options
% 23.54/3.50  
% 23.54/3.50  --schedule                              default
% 23.54/3.50  --add_important_lit                     false
% 23.54/3.50  --prop_solver_per_cl                    1000
% 23.54/3.50  --min_unsat_core                        false
% 23.54/3.50  --soft_assumptions                      false
% 23.54/3.50  --soft_lemma_size                       3
% 23.54/3.50  --prop_impl_unit_size                   0
% 23.54/3.50  --prop_impl_unit                        []
% 23.54/3.50  --share_sel_clauses                     true
% 23.54/3.50  --reset_solvers                         false
% 23.54/3.50  --bc_imp_inh                            [conj_cone]
% 23.54/3.50  --conj_cone_tolerance                   3.
% 23.54/3.50  --extra_neg_conj                        none
% 23.54/3.50  --large_theory_mode                     true
% 23.54/3.50  --prolific_symb_bound                   200
% 23.54/3.50  --lt_threshold                          2000
% 23.54/3.50  --clause_weak_htbl                      true
% 23.54/3.50  --gc_record_bc_elim                     false
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing Options
% 23.54/3.50  
% 23.54/3.50  --preprocessing_flag                    true
% 23.54/3.50  --time_out_prep_mult                    0.1
% 23.54/3.50  --splitting_mode                        input
% 23.54/3.50  --splitting_grd                         true
% 23.54/3.50  --splitting_cvd                         false
% 23.54/3.50  --splitting_cvd_svl                     false
% 23.54/3.50  --splitting_nvd                         32
% 23.54/3.50  --sub_typing                            true
% 23.54/3.50  --prep_gs_sim                           true
% 23.54/3.50  --prep_unflatten                        true
% 23.54/3.50  --prep_res_sim                          true
% 23.54/3.50  --prep_upred                            true
% 23.54/3.50  --prep_sem_filter                       exhaustive
% 23.54/3.50  --prep_sem_filter_out                   false
% 23.54/3.50  --pred_elim                             true
% 23.54/3.50  --res_sim_input                         true
% 23.54/3.50  --eq_ax_congr_red                       true
% 23.54/3.50  --pure_diseq_elim                       true
% 23.54/3.50  --brand_transform                       false
% 23.54/3.50  --non_eq_to_eq                          false
% 23.54/3.50  --prep_def_merge                        true
% 23.54/3.50  --prep_def_merge_prop_impl              false
% 23.54/3.50  --prep_def_merge_mbd                    true
% 23.54/3.50  --prep_def_merge_tr_red                 false
% 23.54/3.50  --prep_def_merge_tr_cl                  false
% 23.54/3.50  --smt_preprocessing                     true
% 23.54/3.50  --smt_ac_axioms                         fast
% 23.54/3.50  --preprocessed_out                      false
% 23.54/3.50  --preprocessed_stats                    false
% 23.54/3.50  
% 23.54/3.50  ------ Abstraction refinement Options
% 23.54/3.50  
% 23.54/3.50  --abstr_ref                             []
% 23.54/3.50  --abstr_ref_prep                        false
% 23.54/3.50  --abstr_ref_until_sat                   false
% 23.54/3.50  --abstr_ref_sig_restrict                funpre
% 23.54/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.54/3.50  --abstr_ref_under                       []
% 23.54/3.50  
% 23.54/3.50  ------ SAT Options
% 23.54/3.50  
% 23.54/3.50  --sat_mode                              false
% 23.54/3.50  --sat_fm_restart_options                ""
% 23.54/3.50  --sat_gr_def                            false
% 23.54/3.50  --sat_epr_types                         true
% 23.54/3.50  --sat_non_cyclic_types                  false
% 23.54/3.50  --sat_finite_models                     false
% 23.54/3.50  --sat_fm_lemmas                         false
% 23.54/3.50  --sat_fm_prep                           false
% 23.54/3.50  --sat_fm_uc_incr                        true
% 23.54/3.50  --sat_out_model                         small
% 23.54/3.50  --sat_out_clauses                       false
% 23.54/3.50  
% 23.54/3.50  ------ QBF Options
% 23.54/3.50  
% 23.54/3.50  --qbf_mode                              false
% 23.54/3.50  --qbf_elim_univ                         false
% 23.54/3.50  --qbf_dom_inst                          none
% 23.54/3.50  --qbf_dom_pre_inst                      false
% 23.54/3.50  --qbf_sk_in                             false
% 23.54/3.50  --qbf_pred_elim                         true
% 23.54/3.50  --qbf_split                             512
% 23.54/3.50  
% 23.54/3.50  ------ BMC1 Options
% 23.54/3.50  
% 23.54/3.50  --bmc1_incremental                      false
% 23.54/3.50  --bmc1_axioms                           reachable_all
% 23.54/3.50  --bmc1_min_bound                        0
% 23.54/3.50  --bmc1_max_bound                        -1
% 23.54/3.50  --bmc1_max_bound_default                -1
% 23.54/3.50  --bmc1_symbol_reachability              true
% 23.54/3.50  --bmc1_property_lemmas                  false
% 23.54/3.50  --bmc1_k_induction                      false
% 23.54/3.50  --bmc1_non_equiv_states                 false
% 23.54/3.50  --bmc1_deadlock                         false
% 23.54/3.50  --bmc1_ucm                              false
% 23.54/3.50  --bmc1_add_unsat_core                   none
% 23.54/3.50  --bmc1_unsat_core_children              false
% 23.54/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.54/3.50  --bmc1_out_stat                         full
% 23.54/3.50  --bmc1_ground_init                      false
% 23.54/3.50  --bmc1_pre_inst_next_state              false
% 23.54/3.50  --bmc1_pre_inst_state                   false
% 23.54/3.50  --bmc1_pre_inst_reach_state             false
% 23.54/3.50  --bmc1_out_unsat_core                   false
% 23.54/3.50  --bmc1_aig_witness_out                  false
% 23.54/3.50  --bmc1_verbose                          false
% 23.54/3.50  --bmc1_dump_clauses_tptp                false
% 23.54/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.54/3.50  --bmc1_dump_file                        -
% 23.54/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.54/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.54/3.50  --bmc1_ucm_extend_mode                  1
% 23.54/3.50  --bmc1_ucm_init_mode                    2
% 23.54/3.50  --bmc1_ucm_cone_mode                    none
% 23.54/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.54/3.50  --bmc1_ucm_relax_model                  4
% 23.54/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.54/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.54/3.50  --bmc1_ucm_layered_model                none
% 23.54/3.50  --bmc1_ucm_max_lemma_size               10
% 23.54/3.50  
% 23.54/3.50  ------ AIG Options
% 23.54/3.50  
% 23.54/3.50  --aig_mode                              false
% 23.54/3.50  
% 23.54/3.50  ------ Instantiation Options
% 23.54/3.50  
% 23.54/3.50  --instantiation_flag                    true
% 23.54/3.50  --inst_sos_flag                         true
% 23.54/3.50  --inst_sos_phase                        true
% 23.54/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.54/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.54/3.50  --inst_lit_sel_side                     num_symb
% 23.54/3.50  --inst_solver_per_active                1400
% 23.54/3.50  --inst_solver_calls_frac                1.
% 23.54/3.50  --inst_passive_queue_type               priority_queues
% 23.54/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.54/3.50  --inst_passive_queues_freq              [25;2]
% 23.54/3.50  --inst_dismatching                      true
% 23.54/3.50  --inst_eager_unprocessed_to_passive     true
% 23.54/3.50  --inst_prop_sim_given                   true
% 23.54/3.50  --inst_prop_sim_new                     false
% 23.54/3.50  --inst_subs_new                         false
% 23.54/3.50  --inst_eq_res_simp                      false
% 23.54/3.50  --inst_subs_given                       false
% 23.54/3.50  --inst_orphan_elimination               true
% 23.54/3.50  --inst_learning_loop_flag               true
% 23.54/3.50  --inst_learning_start                   3000
% 23.54/3.50  --inst_learning_factor                  2
% 23.54/3.50  --inst_start_prop_sim_after_learn       3
% 23.54/3.50  --inst_sel_renew                        solver
% 23.54/3.50  --inst_lit_activity_flag                true
% 23.54/3.50  --inst_restr_to_given                   false
% 23.54/3.50  --inst_activity_threshold               500
% 23.54/3.50  --inst_out_proof                        true
% 23.54/3.50  
% 23.54/3.50  ------ Resolution Options
% 23.54/3.50  
% 23.54/3.50  --resolution_flag                       true
% 23.54/3.50  --res_lit_sel                           adaptive
% 23.54/3.50  --res_lit_sel_side                      none
% 23.54/3.50  --res_ordering                          kbo
% 23.54/3.50  --res_to_prop_solver                    active
% 23.54/3.50  --res_prop_simpl_new                    false
% 23.54/3.50  --res_prop_simpl_given                  true
% 23.54/3.50  --res_passive_queue_type                priority_queues
% 23.54/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.54/3.50  --res_passive_queues_freq               [15;5]
% 23.54/3.50  --res_forward_subs                      full
% 23.54/3.50  --res_backward_subs                     full
% 23.54/3.50  --res_forward_subs_resolution           true
% 23.54/3.50  --res_backward_subs_resolution          true
% 23.54/3.50  --res_orphan_elimination                true
% 23.54/3.50  --res_time_limit                        2.
% 23.54/3.50  --res_out_proof                         true
% 23.54/3.50  
% 23.54/3.50  ------ Superposition Options
% 23.54/3.50  
% 23.54/3.50  --superposition_flag                    true
% 23.54/3.50  --sup_passive_queue_type                priority_queues
% 23.54/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.54/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.54/3.50  --demod_completeness_check              fast
% 23.54/3.50  --demod_use_ground                      true
% 23.54/3.50  --sup_to_prop_solver                    passive
% 23.54/3.50  --sup_prop_simpl_new                    true
% 23.54/3.50  --sup_prop_simpl_given                  true
% 23.54/3.50  --sup_fun_splitting                     true
% 23.54/3.50  --sup_smt_interval                      50000
% 23.54/3.50  
% 23.54/3.50  ------ Superposition Simplification Setup
% 23.54/3.50  
% 23.54/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.54/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.54/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.54/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.54/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.54/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.54/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.54/3.50  --sup_immed_triv                        [TrivRules]
% 23.54/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_immed_bw_main                     []
% 23.54/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.54/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.54/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_input_bw                          []
% 23.54/3.50  
% 23.54/3.50  ------ Combination Options
% 23.54/3.50  
% 23.54/3.50  --comb_res_mult                         3
% 23.54/3.50  --comb_sup_mult                         2
% 23.54/3.50  --comb_inst_mult                        10
% 23.54/3.50  
% 23.54/3.50  ------ Debug Options
% 23.54/3.50  
% 23.54/3.50  --dbg_backtrace                         false
% 23.54/3.50  --dbg_dump_prop_clauses                 false
% 23.54/3.50  --dbg_dump_prop_clauses_file            -
% 23.54/3.50  --dbg_out_stat                          false
% 23.54/3.50  ------ Parsing...
% 23.54/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.54/3.50  ------ Proving...
% 23.54/3.50  ------ Problem Properties 
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  clauses                                 27
% 23.54/3.50  conjectures                             3
% 23.54/3.50  EPR                                     4
% 23.54/3.50  Horn                                    19
% 23.54/3.50  unary                                   6
% 23.54/3.50  binary                                  15
% 23.54/3.50  lits                                    55
% 23.54/3.50  lits eq                                 11
% 23.54/3.50  fd_pure                                 0
% 23.54/3.50  fd_pseudo                               0
% 23.54/3.50  fd_cond                                 0
% 23.54/3.50  fd_pseudo_cond                          3
% 23.54/3.50  AC symbols                              0
% 23.54/3.50  
% 23.54/3.50  ------ Schedule dynamic 5 is on 
% 23.54/3.50  
% 23.54/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  ------ 
% 23.54/3.50  Current options:
% 23.54/3.50  ------ 
% 23.54/3.50  
% 23.54/3.50  ------ Input Options
% 23.54/3.50  
% 23.54/3.50  --out_options                           all
% 23.54/3.50  --tptp_safe_out                         true
% 23.54/3.50  --problem_path                          ""
% 23.54/3.50  --include_path                          ""
% 23.54/3.50  --clausifier                            res/vclausify_rel
% 23.54/3.50  --clausifier_options                    ""
% 23.54/3.50  --stdin                                 false
% 23.54/3.50  --stats_out                             all
% 23.54/3.50  
% 23.54/3.50  ------ General Options
% 23.54/3.50  
% 23.54/3.50  --fof                                   false
% 23.54/3.50  --time_out_real                         305.
% 23.54/3.50  --time_out_virtual                      -1.
% 23.54/3.50  --symbol_type_check                     false
% 23.54/3.50  --clausify_out                          false
% 23.54/3.50  --sig_cnt_out                           false
% 23.54/3.50  --trig_cnt_out                          false
% 23.54/3.50  --trig_cnt_out_tolerance                1.
% 23.54/3.50  --trig_cnt_out_sk_spl                   false
% 23.54/3.50  --abstr_cl_out                          false
% 23.54/3.50  
% 23.54/3.50  ------ Global Options
% 23.54/3.50  
% 23.54/3.50  --schedule                              default
% 23.54/3.50  --add_important_lit                     false
% 23.54/3.50  --prop_solver_per_cl                    1000
% 23.54/3.50  --min_unsat_core                        false
% 23.54/3.50  --soft_assumptions                      false
% 23.54/3.50  --soft_lemma_size                       3
% 23.54/3.50  --prop_impl_unit_size                   0
% 23.54/3.50  --prop_impl_unit                        []
% 23.54/3.50  --share_sel_clauses                     true
% 23.54/3.50  --reset_solvers                         false
% 23.54/3.50  --bc_imp_inh                            [conj_cone]
% 23.54/3.50  --conj_cone_tolerance                   3.
% 23.54/3.50  --extra_neg_conj                        none
% 23.54/3.50  --large_theory_mode                     true
% 23.54/3.50  --prolific_symb_bound                   200
% 23.54/3.50  --lt_threshold                          2000
% 23.54/3.50  --clause_weak_htbl                      true
% 23.54/3.50  --gc_record_bc_elim                     false
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing Options
% 23.54/3.50  
% 23.54/3.50  --preprocessing_flag                    true
% 23.54/3.50  --time_out_prep_mult                    0.1
% 23.54/3.50  --splitting_mode                        input
% 23.54/3.50  --splitting_grd                         true
% 23.54/3.50  --splitting_cvd                         false
% 23.54/3.50  --splitting_cvd_svl                     false
% 23.54/3.50  --splitting_nvd                         32
% 23.54/3.50  --sub_typing                            true
% 23.54/3.50  --prep_gs_sim                           true
% 23.54/3.50  --prep_unflatten                        true
% 23.54/3.50  --prep_res_sim                          true
% 23.54/3.50  --prep_upred                            true
% 23.54/3.50  --prep_sem_filter                       exhaustive
% 23.54/3.50  --prep_sem_filter_out                   false
% 23.54/3.50  --pred_elim                             true
% 23.54/3.50  --res_sim_input                         true
% 23.54/3.50  --eq_ax_congr_red                       true
% 23.54/3.50  --pure_diseq_elim                       true
% 23.54/3.50  --brand_transform                       false
% 23.54/3.50  --non_eq_to_eq                          false
% 23.54/3.50  --prep_def_merge                        true
% 23.54/3.50  --prep_def_merge_prop_impl              false
% 23.54/3.50  --prep_def_merge_mbd                    true
% 23.54/3.50  --prep_def_merge_tr_red                 false
% 23.54/3.50  --prep_def_merge_tr_cl                  false
% 23.54/3.50  --smt_preprocessing                     true
% 23.54/3.50  --smt_ac_axioms                         fast
% 23.54/3.50  --preprocessed_out                      false
% 23.54/3.50  --preprocessed_stats                    false
% 23.54/3.50  
% 23.54/3.50  ------ Abstraction refinement Options
% 23.54/3.50  
% 23.54/3.50  --abstr_ref                             []
% 23.54/3.50  --abstr_ref_prep                        false
% 23.54/3.50  --abstr_ref_until_sat                   false
% 23.54/3.50  --abstr_ref_sig_restrict                funpre
% 23.54/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.54/3.50  --abstr_ref_under                       []
% 23.54/3.50  
% 23.54/3.50  ------ SAT Options
% 23.54/3.50  
% 23.54/3.50  --sat_mode                              false
% 23.54/3.50  --sat_fm_restart_options                ""
% 23.54/3.50  --sat_gr_def                            false
% 23.54/3.50  --sat_epr_types                         true
% 23.54/3.50  --sat_non_cyclic_types                  false
% 23.54/3.50  --sat_finite_models                     false
% 23.54/3.50  --sat_fm_lemmas                         false
% 23.54/3.50  --sat_fm_prep                           false
% 23.54/3.50  --sat_fm_uc_incr                        true
% 23.54/3.50  --sat_out_model                         small
% 23.54/3.50  --sat_out_clauses                       false
% 23.54/3.50  
% 23.54/3.50  ------ QBF Options
% 23.54/3.50  
% 23.54/3.50  --qbf_mode                              false
% 23.54/3.50  --qbf_elim_univ                         false
% 23.54/3.50  --qbf_dom_inst                          none
% 23.54/3.50  --qbf_dom_pre_inst                      false
% 23.54/3.50  --qbf_sk_in                             false
% 23.54/3.50  --qbf_pred_elim                         true
% 23.54/3.50  --qbf_split                             512
% 23.54/3.50  
% 23.54/3.50  ------ BMC1 Options
% 23.54/3.50  
% 23.54/3.50  --bmc1_incremental                      false
% 23.54/3.50  --bmc1_axioms                           reachable_all
% 23.54/3.50  --bmc1_min_bound                        0
% 23.54/3.50  --bmc1_max_bound                        -1
% 23.54/3.50  --bmc1_max_bound_default                -1
% 23.54/3.50  --bmc1_symbol_reachability              true
% 23.54/3.50  --bmc1_property_lemmas                  false
% 23.54/3.50  --bmc1_k_induction                      false
% 23.54/3.50  --bmc1_non_equiv_states                 false
% 23.54/3.50  --bmc1_deadlock                         false
% 23.54/3.50  --bmc1_ucm                              false
% 23.54/3.50  --bmc1_add_unsat_core                   none
% 23.54/3.50  --bmc1_unsat_core_children              false
% 23.54/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.54/3.50  --bmc1_out_stat                         full
% 23.54/3.50  --bmc1_ground_init                      false
% 23.54/3.50  --bmc1_pre_inst_next_state              false
% 23.54/3.50  --bmc1_pre_inst_state                   false
% 23.54/3.50  --bmc1_pre_inst_reach_state             false
% 23.54/3.50  --bmc1_out_unsat_core                   false
% 23.54/3.50  --bmc1_aig_witness_out                  false
% 23.54/3.50  --bmc1_verbose                          false
% 23.54/3.50  --bmc1_dump_clauses_tptp                false
% 23.54/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.54/3.50  --bmc1_dump_file                        -
% 23.54/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.54/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.54/3.50  --bmc1_ucm_extend_mode                  1
% 23.54/3.50  --bmc1_ucm_init_mode                    2
% 23.54/3.50  --bmc1_ucm_cone_mode                    none
% 23.54/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.54/3.50  --bmc1_ucm_relax_model                  4
% 23.54/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.54/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.54/3.50  --bmc1_ucm_layered_model                none
% 23.54/3.50  --bmc1_ucm_max_lemma_size               10
% 23.54/3.50  
% 23.54/3.50  ------ AIG Options
% 23.54/3.50  
% 23.54/3.50  --aig_mode                              false
% 23.54/3.50  
% 23.54/3.50  ------ Instantiation Options
% 23.54/3.50  
% 23.54/3.50  --instantiation_flag                    true
% 23.54/3.50  --inst_sos_flag                         true
% 23.54/3.50  --inst_sos_phase                        true
% 23.54/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.54/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.54/3.50  --inst_lit_sel_side                     none
% 23.54/3.50  --inst_solver_per_active                1400
% 23.54/3.50  --inst_solver_calls_frac                1.
% 23.54/3.50  --inst_passive_queue_type               priority_queues
% 23.54/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.54/3.50  --inst_passive_queues_freq              [25;2]
% 23.54/3.50  --inst_dismatching                      true
% 23.54/3.50  --inst_eager_unprocessed_to_passive     true
% 23.54/3.50  --inst_prop_sim_given                   true
% 23.54/3.50  --inst_prop_sim_new                     false
% 23.54/3.50  --inst_subs_new                         false
% 23.54/3.50  --inst_eq_res_simp                      false
% 23.54/3.50  --inst_subs_given                       false
% 23.54/3.50  --inst_orphan_elimination               true
% 23.54/3.50  --inst_learning_loop_flag               true
% 23.54/3.50  --inst_learning_start                   3000
% 23.54/3.50  --inst_learning_factor                  2
% 23.54/3.50  --inst_start_prop_sim_after_learn       3
% 23.54/3.50  --inst_sel_renew                        solver
% 23.54/3.50  --inst_lit_activity_flag                true
% 23.54/3.50  --inst_restr_to_given                   false
% 23.54/3.50  --inst_activity_threshold               500
% 23.54/3.50  --inst_out_proof                        true
% 23.54/3.50  
% 23.54/3.50  ------ Resolution Options
% 23.54/3.50  
% 23.54/3.50  --resolution_flag                       false
% 23.54/3.50  --res_lit_sel                           adaptive
% 23.54/3.50  --res_lit_sel_side                      none
% 23.54/3.50  --res_ordering                          kbo
% 23.54/3.50  --res_to_prop_solver                    active
% 23.54/3.50  --res_prop_simpl_new                    false
% 23.54/3.50  --res_prop_simpl_given                  true
% 23.54/3.50  --res_passive_queue_type                priority_queues
% 23.54/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.54/3.50  --res_passive_queues_freq               [15;5]
% 23.54/3.50  --res_forward_subs                      full
% 23.54/3.50  --res_backward_subs                     full
% 23.54/3.50  --res_forward_subs_resolution           true
% 23.54/3.50  --res_backward_subs_resolution          true
% 23.54/3.50  --res_orphan_elimination                true
% 23.54/3.50  --res_time_limit                        2.
% 23.54/3.50  --res_out_proof                         true
% 23.54/3.50  
% 23.54/3.50  ------ Superposition Options
% 23.54/3.50  
% 23.54/3.50  --superposition_flag                    true
% 23.54/3.50  --sup_passive_queue_type                priority_queues
% 23.54/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.54/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.54/3.50  --demod_completeness_check              fast
% 23.54/3.50  --demod_use_ground                      true
% 23.54/3.50  --sup_to_prop_solver                    passive
% 23.54/3.50  --sup_prop_simpl_new                    true
% 23.54/3.50  --sup_prop_simpl_given                  true
% 23.54/3.50  --sup_fun_splitting                     true
% 23.54/3.50  --sup_smt_interval                      50000
% 23.54/3.50  
% 23.54/3.50  ------ Superposition Simplification Setup
% 23.54/3.50  
% 23.54/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.54/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.54/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.54/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.54/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.54/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.54/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.54/3.50  --sup_immed_triv                        [TrivRules]
% 23.54/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_immed_bw_main                     []
% 23.54/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.54/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.54/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_input_bw                          []
% 23.54/3.50  
% 23.54/3.50  ------ Combination Options
% 23.54/3.50  
% 23.54/3.50  --comb_res_mult                         3
% 23.54/3.50  --comb_sup_mult                         2
% 23.54/3.50  --comb_inst_mult                        10
% 23.54/3.50  
% 23.54/3.50  ------ Debug Options
% 23.54/3.50  
% 23.54/3.50  --dbg_backtrace                         false
% 23.54/3.50  --dbg_dump_prop_clauses                 false
% 23.54/3.50  --dbg_dump_prop_clauses_file            -
% 23.54/3.50  --dbg_out_stat                          false
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  ------ Proving...
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  % SZS status Theorem for theBenchmark.p
% 23.54/3.50  
% 23.54/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.54/3.50  
% 23.54/3.50  fof(f5,axiom,(
% 23.54/3.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f17,plain,(
% 23.54/3.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.54/3.50    inference(rectify,[],[f5])).
% 23.54/3.50  
% 23.54/3.50  fof(f20,plain,(
% 23.54/3.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 23.54/3.50    inference(ennf_transformation,[],[f17])).
% 23.54/3.50  
% 23.54/3.50  fof(f32,plain,(
% 23.54/3.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f33,plain,(
% 23.54/3.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 23.54/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f32])).
% 23.54/3.50  
% 23.54/3.50  fof(f50,plain,(
% 23.54/3.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f33])).
% 23.54/3.50  
% 23.54/3.50  fof(f51,plain,(
% 23.54/3.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f33])).
% 23.54/3.50  
% 23.54/3.50  fof(f2,axiom,(
% 23.54/3.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f26,plain,(
% 23.54/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.54/3.50    inference(nnf_transformation,[],[f2])).
% 23.54/3.50  
% 23.54/3.50  fof(f27,plain,(
% 23.54/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.54/3.50    inference(flattening,[],[f26])).
% 23.54/3.50  
% 23.54/3.50  fof(f28,plain,(
% 23.54/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.54/3.50    inference(rectify,[],[f27])).
% 23.54/3.50  
% 23.54/3.50  fof(f29,plain,(
% 23.54/3.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f30,plain,(
% 23.54/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.54/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 23.54/3.50  
% 23.54/3.50  fof(f43,plain,(
% 23.54/3.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 23.54/3.50    inference(cnf_transformation,[],[f30])).
% 23.54/3.50  
% 23.54/3.50  fof(f79,plain,(
% 23.54/3.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 23.54/3.50    inference(equality_resolution,[],[f43])).
% 23.54/3.50  
% 23.54/3.50  fof(f15,conjecture,(
% 23.54/3.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f16,negated_conjecture,(
% 23.54/3.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 23.54/3.50    inference(negated_conjecture,[],[f15])).
% 23.54/3.50  
% 23.54/3.50  fof(f24,plain,(
% 23.54/3.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 23.54/3.50    inference(ennf_transformation,[],[f16])).
% 23.54/3.50  
% 23.54/3.50  fof(f25,plain,(
% 23.54/3.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 23.54/3.50    inference(flattening,[],[f24])).
% 23.54/3.50  
% 23.54/3.50  fof(f38,plain,(
% 23.54/3.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) & r1_xboole_0(sK5,sK4) & r2_hidden(sK6,sK5) & r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6)))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f39,plain,(
% 23.54/3.50    ~r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) & r1_xboole_0(sK5,sK4) & r2_hidden(sK6,sK5) & r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6))),
% 23.54/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f38])).
% 23.54/3.50  
% 23.54/3.50  fof(f68,plain,(
% 23.54/3.50    r2_hidden(sK6,sK5)),
% 23.54/3.50    inference(cnf_transformation,[],[f39])).
% 23.54/3.50  
% 23.54/3.50  fof(f14,axiom,(
% 23.54/3.50    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f37,plain,(
% 23.54/3.50    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 23.54/3.50    inference(nnf_transformation,[],[f14])).
% 23.54/3.50  
% 23.54/3.50  fof(f66,plain,(
% 23.54/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f37])).
% 23.54/3.50  
% 23.54/3.50  fof(f12,axiom,(
% 23.54/3.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f63,plain,(
% 23.54/3.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f12])).
% 23.54/3.50  
% 23.54/3.50  fof(f13,axiom,(
% 23.54/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f64,plain,(
% 23.54/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f13])).
% 23.54/3.50  
% 23.54/3.50  fof(f71,plain,(
% 23.54/3.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 23.54/3.50    inference(definition_unfolding,[],[f63,f64])).
% 23.54/3.50  
% 23.54/3.50  fof(f76,plain,(
% 23.54/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 23.54/3.50    inference(definition_unfolding,[],[f66,f71])).
% 23.54/3.50  
% 23.54/3.50  fof(f69,plain,(
% 23.54/3.50    r1_xboole_0(sK5,sK4)),
% 23.54/3.50    inference(cnf_transformation,[],[f39])).
% 23.54/3.50  
% 23.54/3.50  fof(f4,axiom,(
% 23.54/3.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f19,plain,(
% 23.54/3.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 23.54/3.50    inference(ennf_transformation,[],[f4])).
% 23.54/3.50  
% 23.54/3.50  fof(f49,plain,(
% 23.54/3.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f19])).
% 23.54/3.50  
% 23.54/3.50  fof(f10,axiom,(
% 23.54/3.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f36,plain,(
% 23.54/3.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 23.54/3.50    inference(nnf_transformation,[],[f10])).
% 23.54/3.50  
% 23.54/3.50  fof(f60,plain,(
% 23.54/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f36])).
% 23.54/3.50  
% 23.54/3.50  fof(f42,plain,(
% 23.54/3.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.54/3.50    inference(cnf_transformation,[],[f30])).
% 23.54/3.50  
% 23.54/3.50  fof(f80,plain,(
% 23.54/3.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 23.54/3.50    inference(equality_resolution,[],[f42])).
% 23.54/3.50  
% 23.54/3.50  fof(f11,axiom,(
% 23.54/3.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f23,plain,(
% 23.54/3.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 23.54/3.50    inference(ennf_transformation,[],[f11])).
% 23.54/3.50  
% 23.54/3.50  fof(f62,plain,(
% 23.54/3.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f23])).
% 23.54/3.50  
% 23.54/3.50  fof(f67,plain,(
% 23.54/3.50    r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6))),
% 23.54/3.50    inference(cnf_transformation,[],[f39])).
% 23.54/3.50  
% 23.54/3.50  fof(f8,axiom,(
% 23.54/3.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f56,plain,(
% 23.54/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f8])).
% 23.54/3.50  
% 23.54/3.50  fof(f78,plain,(
% 23.54/3.50    r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k2_enumset1(sK6,sK6,sK6,sK6))),
% 23.54/3.50    inference(definition_unfolding,[],[f67,f56,f71])).
% 23.54/3.50  
% 23.54/3.50  fof(f52,plain,(
% 23.54/3.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f33])).
% 23.54/3.50  
% 23.54/3.50  fof(f9,axiom,(
% 23.54/3.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 23.54/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f22,plain,(
% 23.54/3.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 23.54/3.50    inference(ennf_transformation,[],[f9])).
% 23.54/3.50  
% 23.54/3.50  fof(f57,plain,(
% 23.54/3.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 23.54/3.50    inference(cnf_transformation,[],[f22])).
% 23.54/3.50  
% 23.54/3.50  fof(f70,plain,(
% 23.54/3.50    ~r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)),
% 23.54/3.50    inference(cnf_transformation,[],[f39])).
% 23.54/3.50  
% 23.54/3.50  cnf(c_12,plain,
% 23.54/3.50      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f50]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1144,plain,
% 23.54/3.50      ( r1_xboole_0(X0,X1) = iProver_top
% 23.54/3.50      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_11,plain,
% 23.54/3.50      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 23.54/3.50      inference(cnf_transformation,[],[f51]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1145,plain,
% 23.54/3.50      ( r1_xboole_0(X0,X1) = iProver_top
% 23.54/3.50      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_4,plain,
% 23.54/3.50      ( ~ r2_hidden(X0,X1)
% 23.54/3.50      | r2_hidden(X0,X2)
% 23.54/3.50      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 23.54/3.50      inference(cnf_transformation,[],[f79]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1152,plain,
% 23.54/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.54/3.50      | r2_hidden(X0,X2) = iProver_top
% 23.54/3.50      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_26,negated_conjecture,
% 23.54/3.50      ( r2_hidden(sK6,sK5) ),
% 23.54/3.50      inference(cnf_transformation,[],[f68]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1132,plain,
% 23.54/3.50      ( r2_hidden(sK6,sK5) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_22,plain,
% 23.54/3.50      ( r2_hidden(X0,X1)
% 23.54/3.50      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 23.54/3.50      inference(cnf_transformation,[],[f76]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1136,plain,
% 23.54/3.50      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 23.54/3.50      | r2_hidden(X1,X0) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_25,negated_conjecture,
% 23.54/3.50      ( r1_xboole_0(sK5,sK4) ),
% 23.54/3.50      inference(cnf_transformation,[],[f69]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1133,plain,
% 23.54/3.50      ( r1_xboole_0(sK5,sK4) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_9,plain,
% 23.54/3.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f49]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1147,plain,
% 23.54/3.50      ( r1_xboole_0(X0,X1) != iProver_top
% 23.54/3.50      | r1_xboole_0(X1,X0) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2526,plain,
% 23.54/3.50      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_1133,c_1147]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_20,plain,
% 23.54/3.50      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 23.54/3.50      inference(cnf_transformation,[],[f60]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1137,plain,
% 23.54/3.50      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2839,plain,
% 23.54/3.50      ( k4_xboole_0(sK4,sK5) = sK4 ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2526,c_1137]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_5,plain,
% 23.54/3.50      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 23.54/3.50      inference(cnf_transformation,[],[f80]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1151,plain,
% 23.54/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.54/3.50      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_4958,plain,
% 23.54/3.50      ( r2_hidden(X0,sK4) != iProver_top
% 23.54/3.50      | r2_hidden(X0,sK5) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2839,c_1151]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_5414,plain,
% 23.54/3.50      ( k4_xboole_0(sK4,k2_enumset1(X0,X0,X0,X0)) = sK4
% 23.54/3.50      | r2_hidden(X0,sK5) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_1136,c_4958]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_6337,plain,
% 23.54/3.50      ( k4_xboole_0(sK4,k2_enumset1(sK6,sK6,sK6,sK6)) = sK4 ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_1132,c_5414]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_21,plain,
% 23.54/3.50      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 23.54/3.50      inference(cnf_transformation,[],[f62]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_27,negated_conjecture,
% 23.54/3.50      ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 23.54/3.50      inference(cnf_transformation,[],[f78]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_353,plain,
% 23.54/3.50      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 23.54/3.50      | k2_enumset1(sK6,sK6,sK6,sK6) != X2
% 23.54/3.50      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != X0 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_354,plain,
% 23.54/3.50      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(X0,k2_enumset1(sK6,sK6,sK6,sK6))) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_353]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1131,plain,
% 23.54/3.50      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(X0,k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2528,plain,
% 23.54/3.50      ( r1_xboole_0(k4_xboole_0(X0,k2_enumset1(sK6,sK6,sK6,sK6)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_1131,c_1147]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_6596,plain,
% 23.54/3.50      ( r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_6337,c_2528]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_10,plain,
% 23.54/3.50      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f52]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1146,plain,
% 23.54/3.50      ( r1_xboole_0(X0,X1) != iProver_top
% 23.54/3.50      | r2_hidden(X2,X1) != iProver_top
% 23.54/3.50      | r2_hidden(X2,X0) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_6924,plain,
% 23.54/3.50      ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
% 23.54/3.50      | r2_hidden(X0,sK4) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_6596,c_1146]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_8245,plain,
% 23.54/3.50      ( r2_hidden(X0,k4_xboole_0(sK3,sK4)) = iProver_top
% 23.54/3.50      | r2_hidden(X0,sK4) != iProver_top
% 23.54/3.50      | r2_hidden(X0,sK3) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_1152,c_6924]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_10933,plain,
% 23.54/3.50      ( r2_hidden(X0,sK4) != iProver_top
% 23.54/3.50      | r2_hidden(X0,sK3) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_8245,c_1151]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_11170,plain,
% 23.54/3.50      ( r1_xboole_0(X0,sK4) = iProver_top
% 23.54/3.50      | r2_hidden(sK1(X0,sK4),sK3) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_1145,c_10933]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_102740,plain,
% 23.54/3.50      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_1144,c_11170]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2406,plain,
% 23.54/3.50      ( ~ r1_xboole_0(X0,sK4) | r1_xboole_0(sK4,X0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_9]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_27067,plain,
% 23.54/3.50      ( r1_xboole_0(sK4,sK3) | ~ r1_xboole_0(sK3,sK4) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2406]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_27068,plain,
% 23.54/3.50      ( r1_xboole_0(sK4,sK3) = iProver_top
% 23.54/3.50      | r1_xboole_0(sK3,sK4) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_27067]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1619,plain,
% 23.54/3.50      ( r1_xboole_0(X0,sK5) | ~ r1_xboole_0(sK5,X0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_9]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2298,plain,
% 23.54/3.50      ( r1_xboole_0(sK4,sK5) | ~ r1_xboole_0(sK5,sK4) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_1619]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2299,plain,
% 23.54/3.50      ( r1_xboole_0(sK4,sK5) = iProver_top
% 23.54/3.50      | r1_xboole_0(sK5,sK4) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2298]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_18,plain,
% 23.54/3.50      ( ~ r1_xboole_0(X0,X1)
% 23.54/3.50      | ~ r1_xboole_0(X0,X2)
% 23.54/3.50      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.54/3.50      inference(cnf_transformation,[],[f57]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1377,plain,
% 23.54/3.50      ( r1_xboole_0(sK4,k2_xboole_0(sK3,sK5))
% 23.54/3.50      | ~ r1_xboole_0(sK4,sK5)
% 23.54/3.50      | ~ r1_xboole_0(sK4,sK3) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_18]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1378,plain,
% 23.54/3.50      ( r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = iProver_top
% 23.54/3.50      | r1_xboole_0(sK4,sK5) != iProver_top
% 23.54/3.50      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_1377]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1210,plain,
% 23.54/3.50      ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)
% 23.54/3.50      | ~ r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_9]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1211,plain,
% 23.54/3.50      ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) = iProver_top
% 23.54/3.50      | r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_1210]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_24,negated_conjecture,
% 23.54/3.50      ( ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) ),
% 23.54/3.50      inference(cnf_transformation,[],[f70]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_31,plain,
% 23.54/3.50      ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_30,plain,
% 23.54/3.50      ( r1_xboole_0(sK5,sK4) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(contradiction,plain,
% 23.54/3.50      ( $false ),
% 23.54/3.50      inference(minisat,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_102740,c_27068,c_2299,c_1378,c_1211,c_31,c_30]) ).
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.54/3.50  
% 23.54/3.50  ------                               Statistics
% 23.54/3.50  
% 23.54/3.50  ------ General
% 23.54/3.50  
% 23.54/3.50  abstr_ref_over_cycles:                  0
% 23.54/3.50  abstr_ref_under_cycles:                 0
% 23.54/3.50  gc_basic_clause_elim:                   0
% 23.54/3.50  forced_gc_time:                         0
% 23.54/3.50  parsing_time:                           0.008
% 23.54/3.50  unif_index_cands_time:                  0.
% 23.54/3.50  unif_index_add_time:                    0.
% 23.54/3.50  orderings_time:                         0.
% 23.54/3.50  out_proof_time:                         0.012
% 23.54/3.50  total_time:                             2.718
% 23.54/3.50  num_of_symbols:                         45
% 23.54/3.50  num_of_terms:                           102501
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing
% 23.54/3.50  
% 23.54/3.50  num_of_splits:                          0
% 23.54/3.50  num_of_split_atoms:                     0
% 23.54/3.50  num_of_reused_defs:                     0
% 23.54/3.50  num_eq_ax_congr_red:                    21
% 23.54/3.50  num_of_sem_filtered_clauses:            1
% 23.54/3.50  num_of_subtypes:                        0
% 23.54/3.50  monotx_restored_types:                  0
% 23.54/3.50  sat_num_of_epr_types:                   0
% 23.54/3.50  sat_num_of_non_cyclic_types:            0
% 23.54/3.50  sat_guarded_non_collapsed_types:        0
% 23.54/3.50  num_pure_diseq_elim:                    0
% 23.54/3.50  simp_replaced_by:                       0
% 23.54/3.50  res_preprocessed:                       124
% 23.54/3.50  prep_upred:                             0
% 23.54/3.50  prep_unflattend:                        2
% 23.54/3.50  smt_new_axioms:                         0
% 23.54/3.50  pred_elim_cands:                        2
% 23.54/3.50  pred_elim:                              1
% 23.54/3.50  pred_elim_cl:                           1
% 23.54/3.50  pred_elim_cycles:                       3
% 23.54/3.50  merged_defs:                            24
% 23.54/3.50  merged_defs_ncl:                        0
% 23.54/3.50  bin_hyper_res:                          24
% 23.54/3.50  prep_cycles:                            4
% 23.54/3.50  pred_elim_time:                         0.
% 23.54/3.50  splitting_time:                         0.
% 23.54/3.50  sem_filter_time:                        0.
% 23.54/3.50  monotx_time:                            0.
% 23.54/3.50  subtype_inf_time:                       0.
% 23.54/3.50  
% 23.54/3.50  ------ Problem properties
% 23.54/3.50  
% 23.54/3.50  clauses:                                27
% 23.54/3.50  conjectures:                            3
% 23.54/3.50  epr:                                    4
% 23.54/3.50  horn:                                   19
% 23.54/3.50  ground:                                 3
% 23.54/3.50  unary:                                  6
% 23.54/3.50  binary:                                 15
% 23.54/3.50  lits:                                   55
% 23.54/3.50  lits_eq:                                11
% 23.54/3.50  fd_pure:                                0
% 23.54/3.50  fd_pseudo:                              0
% 23.54/3.50  fd_cond:                                0
% 23.54/3.50  fd_pseudo_cond:                         3
% 23.54/3.50  ac_symbols:                             0
% 23.54/3.50  
% 23.54/3.50  ------ Propositional Solver
% 23.54/3.50  
% 23.54/3.50  prop_solver_calls:                      38
% 23.54/3.50  prop_fast_solver_calls:                 1312
% 23.54/3.50  smt_solver_calls:                       0
% 23.54/3.50  smt_fast_solver_calls:                  0
% 23.54/3.50  prop_num_of_clauses:                    37650
% 23.54/3.50  prop_preprocess_simplified:             46127
% 23.54/3.50  prop_fo_subsumed:                       12
% 23.54/3.50  prop_solver_time:                       0.
% 23.54/3.50  smt_solver_time:                        0.
% 23.54/3.50  smt_fast_solver_time:                   0.
% 23.54/3.50  prop_fast_solver_time:                  0.
% 23.54/3.50  prop_unsat_core_time:                   0.004
% 23.54/3.50  
% 23.54/3.50  ------ QBF
% 23.54/3.50  
% 23.54/3.50  qbf_q_res:                              0
% 23.54/3.50  qbf_num_tautologies:                    0
% 23.54/3.50  qbf_prep_cycles:                        0
% 23.54/3.50  
% 23.54/3.50  ------ BMC1
% 23.54/3.50  
% 23.54/3.50  bmc1_current_bound:                     -1
% 23.54/3.50  bmc1_last_solved_bound:                 -1
% 23.54/3.50  bmc1_unsat_core_size:                   -1
% 23.54/3.50  bmc1_unsat_core_parents_size:           -1
% 23.54/3.50  bmc1_merge_next_fun:                    0
% 23.54/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.54/3.50  
% 23.54/3.50  ------ Instantiation
% 23.54/3.50  
% 23.54/3.50  inst_num_of_clauses:                    7270
% 23.54/3.50  inst_num_in_passive:                    2502
% 23.54/3.50  inst_num_in_active:                     1919
% 23.54/3.50  inst_num_in_unprocessed:                2849
% 23.54/3.50  inst_num_of_loops:                      2630
% 23.54/3.50  inst_num_of_learning_restarts:          0
% 23.54/3.50  inst_num_moves_active_passive:          711
% 23.54/3.50  inst_lit_activity:                      0
% 23.54/3.50  inst_lit_activity_moves:                2
% 23.54/3.50  inst_num_tautologies:                   0
% 23.54/3.50  inst_num_prop_implied:                  0
% 23.54/3.50  inst_num_existing_simplified:           0
% 23.54/3.50  inst_num_eq_res_simplified:             0
% 23.54/3.50  inst_num_child_elim:                    0
% 23.54/3.50  inst_num_of_dismatching_blockings:      18285
% 23.54/3.50  inst_num_of_non_proper_insts:           8991
% 23.54/3.50  inst_num_of_duplicates:                 0
% 23.54/3.50  inst_inst_num_from_inst_to_res:         0
% 23.54/3.50  inst_dismatching_checking_time:         0.
% 23.54/3.50  
% 23.54/3.50  ------ Resolution
% 23.54/3.50  
% 23.54/3.50  res_num_of_clauses:                     0
% 23.54/3.50  res_num_in_passive:                     0
% 23.54/3.50  res_num_in_active:                      0
% 23.54/3.50  res_num_of_loops:                       128
% 23.54/3.50  res_forward_subset_subsumed:            459
% 23.54/3.50  res_backward_subset_subsumed:           0
% 23.54/3.50  res_forward_subsumed:                   0
% 23.54/3.50  res_backward_subsumed:                  0
% 23.54/3.50  res_forward_subsumption_resolution:     0
% 23.54/3.50  res_backward_subsumption_resolution:    0
% 23.54/3.50  res_clause_to_clause_subsumption:       35540
% 23.54/3.50  res_orphan_elimination:                 0
% 23.54/3.50  res_tautology_del:                      360
% 23.54/3.50  res_num_eq_res_simplified:              0
% 23.54/3.50  res_num_sel_changes:                    0
% 23.54/3.50  res_moves_from_active_to_pass:          0
% 23.54/3.50  
% 23.54/3.50  ------ Superposition
% 23.54/3.50  
% 23.54/3.50  sup_time_total:                         0.
% 23.54/3.50  sup_time_generating:                    0.
% 23.54/3.50  sup_time_sim_full:                      0.
% 23.54/3.50  sup_time_sim_immed:                     0.
% 23.54/3.50  
% 23.54/3.50  sup_num_of_clauses:                     4534
% 23.54/3.50  sup_num_in_active:                      517
% 23.54/3.50  sup_num_in_passive:                     4017
% 23.54/3.50  sup_num_of_loops:                       525
% 23.54/3.50  sup_fw_superposition:                   8098
% 23.54/3.50  sup_bw_superposition:                   10409
% 23.54/3.50  sup_immediate_simplified:               8483
% 23.54/3.50  sup_given_eliminated:                   2
% 23.54/3.50  comparisons_done:                       0
% 23.54/3.50  comparisons_avoided:                    3
% 23.54/3.50  
% 23.54/3.50  ------ Simplifications
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  sim_fw_subset_subsumed:                 1236
% 23.54/3.50  sim_bw_subset_subsumed:                 15
% 23.54/3.50  sim_fw_subsumed:                        2487
% 23.54/3.50  sim_bw_subsumed:                        26
% 23.54/3.50  sim_fw_subsumption_res:                 0
% 23.54/3.50  sim_bw_subsumption_res:                 0
% 23.54/3.50  sim_tautology_del:                      697
% 23.54/3.50  sim_eq_tautology_del:                   2162
% 23.54/3.50  sim_eq_res_simp:                        7
% 23.54/3.50  sim_fw_demodulated:                     3007
% 23.54/3.50  sim_bw_demodulated:                     5
% 23.54/3.50  sim_light_normalised:                   4063
% 23.54/3.50  sim_joinable_taut:                      0
% 23.54/3.50  sim_joinable_simp:                      0
% 23.54/3.50  sim_ac_normalised:                      0
% 23.54/3.50  sim_smt_subsumption:                    0
% 23.54/3.50  
%------------------------------------------------------------------------------
