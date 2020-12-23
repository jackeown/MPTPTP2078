%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:10 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 238 expanded)
%              Number of clauses        :   50 (  59 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  335 ( 757 expanded)
%              Number of equality atoms :  187 ( 335 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f90,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
        & ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK4,sK5)
        | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0 )
      & ( r2_hidden(sK4,sK5)
        | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ~ r2_hidden(sK4,sK5)
      | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0 )
    & ( r2_hidden(sK4,sK5)
      | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f34])).

fof(f62,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) ),
    inference(definition_unfolding,[],[f62,f47,f63])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,
    ( r2_hidden(sK4,sK5)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) ),
    inference(definition_unfolding,[],[f61,f47,f63])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f93,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f81])).

fof(f94,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f93])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f88,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f75])).

fof(f89,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f88])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_884,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_871,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1423,plain,
    ( sK0(k1_enumset1(X0,X0,X0),X1) = X0
    | r1_tarski(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_871])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_876,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3207,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),X1)) = k1_xboole_0
    | sK0(k1_enumset1(X0,X0,X0),X1) = X0 ),
    inference(superposition,[status(thm)],[c_1423,c_876])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(sK4,sK5)
    | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_864,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11263,plain,
    ( sK0(k1_enumset1(sK4,sK4,sK4),sK5) = sK4
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3207,c_864])).

cnf(c_385,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3617,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k1_enumset1(sK4,sK4,sK4),sK5),sK5)
    | sK0(k1_enumset1(sK4,sK4,sK4),sK5) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_9593,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK0(k1_enumset1(sK4,sK4,sK4),sK5),sK5)
    | sK0(k1_enumset1(sK4,sK4,sK4),sK5) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3617])).

cnf(c_9595,plain,
    ( r2_hidden(sK0(k1_enumset1(sK4,sK4,sK4),sK5),sK5)
    | ~ r2_hidden(sK4,sK5)
    | sK0(k1_enumset1(sK4,sK4,sK4),sK5) != sK4
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_9593])).

cnf(c_2691,plain,
    ( ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5)
    | k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_885,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1511,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_885])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK4,sK5)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_863,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_883,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2055,plain,
    ( k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) = k1_xboole_0
    | r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_883])).

cnf(c_20,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_29,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_31,plain,
    ( r2_hidden(sK4,k1_enumset1(sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_916,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK4,sK5)
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_963,plain,
    ( ~ r2_hidden(sK4,k1_enumset1(sK4,sK4,sK4))
    | r2_hidden(sK4,sK5)
    | ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_964,plain,
    ( r2_hidden(sK4,k1_enumset1(sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1011,plain,
    ( r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5)
    | k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1018,plain,
    ( k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_xboole_0
    | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_958,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK4,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1087,plain,
    ( r2_hidden(sK4,X0)
    | ~ r2_hidden(sK4,sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_1095,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(c_2065,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2055,c_31,c_964,c_1018,c_1095])).

cnf(c_2071,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_2065])).

cnf(c_383,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1835,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1416,plain,
    ( r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_384,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1104,plain,
    ( k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_1337,plain,
    ( k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_1001,plain,
    ( ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1154,plain,
    ( ~ r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1012,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK4,sK4,sK4),sK5),sK5)
    | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_25,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11263,c_9595,c_2691,c_2071,c_1835,c_1416,c_1337,c_1154,c_1012,c_25,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.49/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/1.00  
% 3.49/1.00  ------  iProver source info
% 3.49/1.00  
% 3.49/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.49/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/1.00  git: non_committed_changes: false
% 3.49/1.00  git: last_make_outside_of_git: false
% 3.49/1.00  
% 3.49/1.00  ------ 
% 3.49/1.00  
% 3.49/1.00  ------ Input Options
% 3.49/1.00  
% 3.49/1.00  --out_options                           all
% 3.49/1.00  --tptp_safe_out                         true
% 3.49/1.00  --problem_path                          ""
% 3.49/1.00  --include_path                          ""
% 3.49/1.00  --clausifier                            res/vclausify_rel
% 3.49/1.00  --clausifier_options                    ""
% 3.49/1.00  --stdin                                 false
% 3.49/1.00  --stats_out                             all
% 3.49/1.00  
% 3.49/1.00  ------ General Options
% 3.49/1.00  
% 3.49/1.00  --fof                                   false
% 3.49/1.00  --time_out_real                         305.
% 3.49/1.00  --time_out_virtual                      -1.
% 3.49/1.00  --symbol_type_check                     false
% 3.49/1.00  --clausify_out                          false
% 3.49/1.00  --sig_cnt_out                           false
% 3.49/1.00  --trig_cnt_out                          false
% 3.49/1.00  --trig_cnt_out_tolerance                1.
% 3.49/1.00  --trig_cnt_out_sk_spl                   false
% 3.49/1.00  --abstr_cl_out                          false
% 3.49/1.00  
% 3.49/1.00  ------ Global Options
% 3.49/1.00  
% 3.49/1.00  --schedule                              default
% 3.49/1.00  --add_important_lit                     false
% 3.49/1.00  --prop_solver_per_cl                    1000
% 3.49/1.00  --min_unsat_core                        false
% 3.49/1.00  --soft_assumptions                      false
% 3.49/1.00  --soft_lemma_size                       3
% 3.49/1.00  --prop_impl_unit_size                   0
% 3.49/1.00  --prop_impl_unit                        []
% 3.49/1.00  --share_sel_clauses                     true
% 3.49/1.00  --reset_solvers                         false
% 3.49/1.00  --bc_imp_inh                            [conj_cone]
% 3.49/1.00  --conj_cone_tolerance                   3.
% 3.49/1.00  --extra_neg_conj                        none
% 3.49/1.00  --large_theory_mode                     true
% 3.49/1.00  --prolific_symb_bound                   200
% 3.49/1.00  --lt_threshold                          2000
% 3.49/1.00  --clause_weak_htbl                      true
% 3.49/1.00  --gc_record_bc_elim                     false
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing Options
% 3.49/1.00  
% 3.49/1.00  --preprocessing_flag                    true
% 3.49/1.00  --time_out_prep_mult                    0.1
% 3.49/1.00  --splitting_mode                        input
% 3.49/1.00  --splitting_grd                         true
% 3.49/1.00  --splitting_cvd                         false
% 3.49/1.00  --splitting_cvd_svl                     false
% 3.49/1.00  --splitting_nvd                         32
% 3.49/1.00  --sub_typing                            true
% 3.49/1.00  --prep_gs_sim                           true
% 3.49/1.00  --prep_unflatten                        true
% 3.49/1.00  --prep_res_sim                          true
% 3.49/1.00  --prep_upred                            true
% 3.49/1.00  --prep_sem_filter                       exhaustive
% 3.49/1.00  --prep_sem_filter_out                   false
% 3.49/1.00  --pred_elim                             true
% 3.49/1.00  --res_sim_input                         true
% 3.49/1.00  --eq_ax_congr_red                       true
% 3.49/1.00  --pure_diseq_elim                       true
% 3.49/1.00  --brand_transform                       false
% 3.49/1.00  --non_eq_to_eq                          false
% 3.49/1.00  --prep_def_merge                        true
% 3.49/1.00  --prep_def_merge_prop_impl              false
% 3.49/1.00  --prep_def_merge_mbd                    true
% 3.49/1.00  --prep_def_merge_tr_red                 false
% 3.49/1.00  --prep_def_merge_tr_cl                  false
% 3.49/1.00  --smt_preprocessing                     true
% 3.49/1.00  --smt_ac_axioms                         fast
% 3.49/1.00  --preprocessed_out                      false
% 3.49/1.00  --preprocessed_stats                    false
% 3.49/1.00  
% 3.49/1.00  ------ Abstraction refinement Options
% 3.49/1.00  
% 3.49/1.00  --abstr_ref                             []
% 3.49/1.00  --abstr_ref_prep                        false
% 3.49/1.00  --abstr_ref_until_sat                   false
% 3.49/1.00  --abstr_ref_sig_restrict                funpre
% 3.49/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/1.00  --abstr_ref_under                       []
% 3.49/1.00  
% 3.49/1.00  ------ SAT Options
% 3.49/1.00  
% 3.49/1.00  --sat_mode                              false
% 3.49/1.00  --sat_fm_restart_options                ""
% 3.49/1.00  --sat_gr_def                            false
% 3.49/1.00  --sat_epr_types                         true
% 3.49/1.00  --sat_non_cyclic_types                  false
% 3.49/1.00  --sat_finite_models                     false
% 3.49/1.00  --sat_fm_lemmas                         false
% 3.49/1.00  --sat_fm_prep                           false
% 3.49/1.00  --sat_fm_uc_incr                        true
% 3.49/1.00  --sat_out_model                         small
% 3.49/1.00  --sat_out_clauses                       false
% 3.49/1.00  
% 3.49/1.00  ------ QBF Options
% 3.49/1.00  
% 3.49/1.00  --qbf_mode                              false
% 3.49/1.00  --qbf_elim_univ                         false
% 3.49/1.00  --qbf_dom_inst                          none
% 3.49/1.00  --qbf_dom_pre_inst                      false
% 3.49/1.00  --qbf_sk_in                             false
% 3.49/1.00  --qbf_pred_elim                         true
% 3.49/1.00  --qbf_split                             512
% 3.49/1.00  
% 3.49/1.00  ------ BMC1 Options
% 3.49/1.00  
% 3.49/1.00  --bmc1_incremental                      false
% 3.49/1.00  --bmc1_axioms                           reachable_all
% 3.49/1.00  --bmc1_min_bound                        0
% 3.49/1.00  --bmc1_max_bound                        -1
% 3.49/1.00  --bmc1_max_bound_default                -1
% 3.49/1.00  --bmc1_symbol_reachability              true
% 3.49/1.00  --bmc1_property_lemmas                  false
% 3.49/1.00  --bmc1_k_induction                      false
% 3.49/1.00  --bmc1_non_equiv_states                 false
% 3.49/1.00  --bmc1_deadlock                         false
% 3.49/1.00  --bmc1_ucm                              false
% 3.49/1.00  --bmc1_add_unsat_core                   none
% 3.49/1.00  --bmc1_unsat_core_children              false
% 3.49/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/1.00  --bmc1_out_stat                         full
% 3.49/1.00  --bmc1_ground_init                      false
% 3.49/1.00  --bmc1_pre_inst_next_state              false
% 3.49/1.00  --bmc1_pre_inst_state                   false
% 3.49/1.00  --bmc1_pre_inst_reach_state             false
% 3.49/1.00  --bmc1_out_unsat_core                   false
% 3.49/1.00  --bmc1_aig_witness_out                  false
% 3.49/1.00  --bmc1_verbose                          false
% 3.49/1.00  --bmc1_dump_clauses_tptp                false
% 3.49/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.49/1.00  --bmc1_dump_file                        -
% 3.49/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.49/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.49/1.00  --bmc1_ucm_extend_mode                  1
% 3.49/1.00  --bmc1_ucm_init_mode                    2
% 3.49/1.00  --bmc1_ucm_cone_mode                    none
% 3.49/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.49/1.00  --bmc1_ucm_relax_model                  4
% 3.49/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.49/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/1.00  --bmc1_ucm_layered_model                none
% 3.49/1.00  --bmc1_ucm_max_lemma_size               10
% 3.49/1.00  
% 3.49/1.00  ------ AIG Options
% 3.49/1.00  
% 3.49/1.00  --aig_mode                              false
% 3.49/1.00  
% 3.49/1.00  ------ Instantiation Options
% 3.49/1.00  
% 3.49/1.00  --instantiation_flag                    true
% 3.49/1.00  --inst_sos_flag                         true
% 3.49/1.00  --inst_sos_phase                        true
% 3.49/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/1.00  --inst_lit_sel_side                     num_symb
% 3.49/1.00  --inst_solver_per_active                1400
% 3.49/1.00  --inst_solver_calls_frac                1.
% 3.49/1.00  --inst_passive_queue_type               priority_queues
% 3.49/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/1.00  --inst_passive_queues_freq              [25;2]
% 3.49/1.00  --inst_dismatching                      true
% 3.49/1.00  --inst_eager_unprocessed_to_passive     true
% 3.49/1.00  --inst_prop_sim_given                   true
% 3.49/1.00  --inst_prop_sim_new                     false
% 3.49/1.00  --inst_subs_new                         false
% 3.49/1.00  --inst_eq_res_simp                      false
% 3.49/1.00  --inst_subs_given                       false
% 3.49/1.00  --inst_orphan_elimination               true
% 3.49/1.00  --inst_learning_loop_flag               true
% 3.49/1.00  --inst_learning_start                   3000
% 3.49/1.00  --inst_learning_factor                  2
% 3.49/1.00  --inst_start_prop_sim_after_learn       3
% 3.49/1.00  --inst_sel_renew                        solver
% 3.49/1.00  --inst_lit_activity_flag                true
% 3.49/1.00  --inst_restr_to_given                   false
% 3.49/1.00  --inst_activity_threshold               500
% 3.49/1.00  --inst_out_proof                        true
% 3.49/1.00  
% 3.49/1.00  ------ Resolution Options
% 3.49/1.00  
% 3.49/1.00  --resolution_flag                       true
% 3.49/1.00  --res_lit_sel                           adaptive
% 3.49/1.00  --res_lit_sel_side                      none
% 3.49/1.00  --res_ordering                          kbo
% 3.49/1.00  --res_to_prop_solver                    active
% 3.49/1.00  --res_prop_simpl_new                    false
% 3.49/1.00  --res_prop_simpl_given                  true
% 3.49/1.00  --res_passive_queue_type                priority_queues
% 3.49/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/1.00  --res_passive_queues_freq               [15;5]
% 3.49/1.00  --res_forward_subs                      full
% 3.49/1.00  --res_backward_subs                     full
% 3.49/1.00  --res_forward_subs_resolution           true
% 3.49/1.00  --res_backward_subs_resolution          true
% 3.49/1.00  --res_orphan_elimination                true
% 3.49/1.00  --res_time_limit                        2.
% 3.49/1.00  --res_out_proof                         true
% 3.49/1.00  
% 3.49/1.00  ------ Superposition Options
% 3.49/1.00  
% 3.49/1.00  --superposition_flag                    true
% 3.49/1.00  --sup_passive_queue_type                priority_queues
% 3.49/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.49/1.00  --demod_completeness_check              fast
% 3.49/1.00  --demod_use_ground                      true
% 3.49/1.00  --sup_to_prop_solver                    passive
% 3.49/1.00  --sup_prop_simpl_new                    true
% 3.49/1.00  --sup_prop_simpl_given                  true
% 3.49/1.00  --sup_fun_splitting                     true
% 3.49/1.00  --sup_smt_interval                      50000
% 3.49/1.00  
% 3.49/1.00  ------ Superposition Simplification Setup
% 3.49/1.00  
% 3.49/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.49/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.49/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.49/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.49/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.49/1.00  --sup_immed_triv                        [TrivRules]
% 3.49/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.00  --sup_immed_bw_main                     []
% 3.49/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.49/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.00  --sup_input_bw                          []
% 3.49/1.00  
% 3.49/1.00  ------ Combination Options
% 3.49/1.00  
% 3.49/1.00  --comb_res_mult                         3
% 3.49/1.00  --comb_sup_mult                         2
% 3.49/1.00  --comb_inst_mult                        10
% 3.49/1.00  
% 3.49/1.00  ------ Debug Options
% 3.49/1.00  
% 3.49/1.00  --dbg_backtrace                         false
% 3.49/1.00  --dbg_dump_prop_clauses                 false
% 3.49/1.00  --dbg_dump_prop_clauses_file            -
% 3.49/1.00  --dbg_out_stat                          false
% 3.49/1.00  ------ Parsing...
% 3.49/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/1.00  ------ Proving...
% 3.49/1.00  ------ Problem Properties 
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  clauses                                 24
% 3.49/1.00  conjectures                             2
% 3.49/1.00  EPR                                     1
% 3.49/1.00  Horn                                    15
% 3.49/1.00  unary                                   4
% 3.49/1.00  binary                                  9
% 3.49/1.00  lits                                    57
% 3.49/1.00  lits eq                                 22
% 3.49/1.00  fd_pure                                 0
% 3.49/1.00  fd_pseudo                               0
% 3.49/1.00  fd_cond                                 0
% 3.49/1.00  fd_pseudo_cond                          8
% 3.49/1.00  AC symbols                              0
% 3.49/1.00  
% 3.49/1.00  ------ Schedule dynamic 5 is on 
% 3.49/1.00  
% 3.49/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  ------ 
% 3.49/1.00  Current options:
% 3.49/1.00  ------ 
% 3.49/1.00  
% 3.49/1.00  ------ Input Options
% 3.49/1.00  
% 3.49/1.00  --out_options                           all
% 3.49/1.00  --tptp_safe_out                         true
% 3.49/1.00  --problem_path                          ""
% 3.49/1.00  --include_path                          ""
% 3.49/1.00  --clausifier                            res/vclausify_rel
% 3.49/1.00  --clausifier_options                    ""
% 3.49/1.00  --stdin                                 false
% 3.49/1.00  --stats_out                             all
% 3.49/1.00  
% 3.49/1.00  ------ General Options
% 3.49/1.00  
% 3.49/1.00  --fof                                   false
% 3.49/1.00  --time_out_real                         305.
% 3.49/1.00  --time_out_virtual                      -1.
% 3.49/1.00  --symbol_type_check                     false
% 3.49/1.00  --clausify_out                          false
% 3.49/1.00  --sig_cnt_out                           false
% 3.49/1.00  --trig_cnt_out                          false
% 3.49/1.00  --trig_cnt_out_tolerance                1.
% 3.49/1.00  --trig_cnt_out_sk_spl                   false
% 3.49/1.00  --abstr_cl_out                          false
% 3.49/1.00  
% 3.49/1.00  ------ Global Options
% 3.49/1.00  
% 3.49/1.00  --schedule                              default
% 3.49/1.00  --add_important_lit                     false
% 3.49/1.00  --prop_solver_per_cl                    1000
% 3.49/1.00  --min_unsat_core                        false
% 3.49/1.00  --soft_assumptions                      false
% 3.49/1.00  --soft_lemma_size                       3
% 3.49/1.00  --prop_impl_unit_size                   0
% 3.49/1.00  --prop_impl_unit                        []
% 3.49/1.00  --share_sel_clauses                     true
% 3.49/1.00  --reset_solvers                         false
% 3.49/1.00  --bc_imp_inh                            [conj_cone]
% 3.49/1.00  --conj_cone_tolerance                   3.
% 3.49/1.00  --extra_neg_conj                        none
% 3.49/1.00  --large_theory_mode                     true
% 3.49/1.00  --prolific_symb_bound                   200
% 3.49/1.00  --lt_threshold                          2000
% 3.49/1.00  --clause_weak_htbl                      true
% 3.49/1.00  --gc_record_bc_elim                     false
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing Options
% 3.49/1.00  
% 3.49/1.00  --preprocessing_flag                    true
% 3.49/1.00  --time_out_prep_mult                    0.1
% 3.49/1.00  --splitting_mode                        input
% 3.49/1.00  --splitting_grd                         true
% 3.49/1.00  --splitting_cvd                         false
% 3.49/1.00  --splitting_cvd_svl                     false
% 3.49/1.00  --splitting_nvd                         32
% 3.49/1.00  --sub_typing                            true
% 3.49/1.00  --prep_gs_sim                           true
% 3.49/1.00  --prep_unflatten                        true
% 3.49/1.00  --prep_res_sim                          true
% 3.49/1.00  --prep_upred                            true
% 3.49/1.00  --prep_sem_filter                       exhaustive
% 3.49/1.00  --prep_sem_filter_out                   false
% 3.49/1.00  --pred_elim                             true
% 3.49/1.00  --res_sim_input                         true
% 3.49/1.00  --eq_ax_congr_red                       true
% 3.49/1.00  --pure_diseq_elim                       true
% 3.49/1.00  --brand_transform                       false
% 3.49/1.00  --non_eq_to_eq                          false
% 3.49/1.00  --prep_def_merge                        true
% 3.49/1.00  --prep_def_merge_prop_impl              false
% 3.49/1.00  --prep_def_merge_mbd                    true
% 3.49/1.00  --prep_def_merge_tr_red                 false
% 3.49/1.00  --prep_def_merge_tr_cl                  false
% 3.49/1.00  --smt_preprocessing                     true
% 3.49/1.00  --smt_ac_axioms                         fast
% 3.49/1.00  --preprocessed_out                      false
% 3.49/1.00  --preprocessed_stats                    false
% 3.49/1.00  
% 3.49/1.00  ------ Abstraction refinement Options
% 3.49/1.00  
% 3.49/1.00  --abstr_ref                             []
% 3.49/1.00  --abstr_ref_prep                        false
% 3.49/1.00  --abstr_ref_until_sat                   false
% 3.49/1.00  --abstr_ref_sig_restrict                funpre
% 3.49/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/1.00  --abstr_ref_under                       []
% 3.49/1.00  
% 3.49/1.00  ------ SAT Options
% 3.49/1.00  
% 3.49/1.00  --sat_mode                              false
% 3.49/1.00  --sat_fm_restart_options                ""
% 3.49/1.00  --sat_gr_def                            false
% 3.49/1.00  --sat_epr_types                         true
% 3.49/1.00  --sat_non_cyclic_types                  false
% 3.49/1.00  --sat_finite_models                     false
% 3.49/1.00  --sat_fm_lemmas                         false
% 3.49/1.00  --sat_fm_prep                           false
% 3.49/1.00  --sat_fm_uc_incr                        true
% 3.49/1.00  --sat_out_model                         small
% 3.49/1.00  --sat_out_clauses                       false
% 3.49/1.00  
% 3.49/1.00  ------ QBF Options
% 3.49/1.00  
% 3.49/1.00  --qbf_mode                              false
% 3.49/1.00  --qbf_elim_univ                         false
% 3.49/1.00  --qbf_dom_inst                          none
% 3.49/1.00  --qbf_dom_pre_inst                      false
% 3.49/1.00  --qbf_sk_in                             false
% 3.49/1.00  --qbf_pred_elim                         true
% 3.49/1.00  --qbf_split                             512
% 3.49/1.00  
% 3.49/1.00  ------ BMC1 Options
% 3.49/1.00  
% 3.49/1.00  --bmc1_incremental                      false
% 3.49/1.00  --bmc1_axioms                           reachable_all
% 3.49/1.00  --bmc1_min_bound                        0
% 3.49/1.00  --bmc1_max_bound                        -1
% 3.49/1.00  --bmc1_max_bound_default                -1
% 3.49/1.00  --bmc1_symbol_reachability              true
% 3.49/1.00  --bmc1_property_lemmas                  false
% 3.49/1.00  --bmc1_k_induction                      false
% 3.49/1.00  --bmc1_non_equiv_states                 false
% 3.49/1.00  --bmc1_deadlock                         false
% 3.49/1.00  --bmc1_ucm                              false
% 3.49/1.00  --bmc1_add_unsat_core                   none
% 3.49/1.00  --bmc1_unsat_core_children              false
% 3.49/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/1.00  --bmc1_out_stat                         full
% 3.49/1.00  --bmc1_ground_init                      false
% 3.49/1.00  --bmc1_pre_inst_next_state              false
% 3.49/1.00  --bmc1_pre_inst_state                   false
% 3.49/1.00  --bmc1_pre_inst_reach_state             false
% 3.49/1.00  --bmc1_out_unsat_core                   false
% 3.49/1.00  --bmc1_aig_witness_out                  false
% 3.49/1.00  --bmc1_verbose                          false
% 3.49/1.00  --bmc1_dump_clauses_tptp                false
% 3.49/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.49/1.00  --bmc1_dump_file                        -
% 3.49/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.49/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.49/1.00  --bmc1_ucm_extend_mode                  1
% 3.49/1.00  --bmc1_ucm_init_mode                    2
% 3.49/1.00  --bmc1_ucm_cone_mode                    none
% 3.49/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.49/1.00  --bmc1_ucm_relax_model                  4
% 3.49/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.49/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/1.00  --bmc1_ucm_layered_model                none
% 3.49/1.00  --bmc1_ucm_max_lemma_size               10
% 3.49/1.00  
% 3.49/1.00  ------ AIG Options
% 3.49/1.00  
% 3.49/1.00  --aig_mode                              false
% 3.49/1.00  
% 3.49/1.00  ------ Instantiation Options
% 3.49/1.00  
% 3.49/1.00  --instantiation_flag                    true
% 3.49/1.00  --inst_sos_flag                         true
% 3.49/1.00  --inst_sos_phase                        true
% 3.49/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/1.00  --inst_lit_sel_side                     none
% 3.49/1.00  --inst_solver_per_active                1400
% 3.49/1.00  --inst_solver_calls_frac                1.
% 3.49/1.00  --inst_passive_queue_type               priority_queues
% 3.49/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/1.00  --inst_passive_queues_freq              [25;2]
% 3.49/1.00  --inst_dismatching                      true
% 3.49/1.00  --inst_eager_unprocessed_to_passive     true
% 3.49/1.00  --inst_prop_sim_given                   true
% 3.49/1.00  --inst_prop_sim_new                     false
% 3.49/1.00  --inst_subs_new                         false
% 3.49/1.00  --inst_eq_res_simp                      false
% 3.49/1.00  --inst_subs_given                       false
% 3.49/1.00  --inst_orphan_elimination               true
% 3.49/1.00  --inst_learning_loop_flag               true
% 3.49/1.00  --inst_learning_start                   3000
% 3.49/1.00  --inst_learning_factor                  2
% 3.49/1.00  --inst_start_prop_sim_after_learn       3
% 3.49/1.00  --inst_sel_renew                        solver
% 3.49/1.00  --inst_lit_activity_flag                true
% 3.49/1.00  --inst_restr_to_given                   false
% 3.49/1.00  --inst_activity_threshold               500
% 3.49/1.00  --inst_out_proof                        true
% 3.49/1.00  
% 3.49/1.00  ------ Resolution Options
% 3.49/1.00  
% 3.49/1.00  --resolution_flag                       false
% 3.49/1.00  --res_lit_sel                           adaptive
% 3.49/1.00  --res_lit_sel_side                      none
% 3.49/1.00  --res_ordering                          kbo
% 3.49/1.00  --res_to_prop_solver                    active
% 3.49/1.00  --res_prop_simpl_new                    false
% 3.49/1.00  --res_prop_simpl_given                  true
% 3.49/1.00  --res_passive_queue_type                priority_queues
% 3.49/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/1.01  --res_passive_queues_freq               [15;5]
% 3.49/1.01  --res_forward_subs                      full
% 3.49/1.01  --res_backward_subs                     full
% 3.49/1.01  --res_forward_subs_resolution           true
% 3.49/1.01  --res_backward_subs_resolution          true
% 3.49/1.01  --res_orphan_elimination                true
% 3.49/1.01  --res_time_limit                        2.
% 3.49/1.01  --res_out_proof                         true
% 3.49/1.01  
% 3.49/1.01  ------ Superposition Options
% 3.49/1.01  
% 3.49/1.01  --superposition_flag                    true
% 3.49/1.01  --sup_passive_queue_type                priority_queues
% 3.49/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.49/1.01  --demod_completeness_check              fast
% 3.49/1.01  --demod_use_ground                      true
% 3.49/1.01  --sup_to_prop_solver                    passive
% 3.49/1.01  --sup_prop_simpl_new                    true
% 3.49/1.01  --sup_prop_simpl_given                  true
% 3.49/1.01  --sup_fun_splitting                     true
% 3.49/1.01  --sup_smt_interval                      50000
% 3.49/1.01  
% 3.49/1.01  ------ Superposition Simplification Setup
% 3.49/1.01  
% 3.49/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.49/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.49/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.49/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.49/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.49/1.01  --sup_immed_triv                        [TrivRules]
% 3.49/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.01  --sup_immed_bw_main                     []
% 3.49/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.49/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.01  --sup_input_bw                          []
% 3.49/1.01  
% 3.49/1.01  ------ Combination Options
% 3.49/1.01  
% 3.49/1.01  --comb_res_mult                         3
% 3.49/1.01  --comb_sup_mult                         2
% 3.49/1.01  --comb_inst_mult                        10
% 3.49/1.01  
% 3.49/1.01  ------ Debug Options
% 3.49/1.01  
% 3.49/1.01  --dbg_backtrace                         false
% 3.49/1.01  --dbg_dump_prop_clauses                 false
% 3.49/1.01  --dbg_dump_prop_clauses_file            -
% 3.49/1.01  --dbg_out_stat                          false
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  ------ Proving...
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  % SZS status Theorem for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  fof(f1,axiom,(
% 3.49/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f12,plain,(
% 3.49/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.49/1.01    inference(ennf_transformation,[],[f1])).
% 3.49/1.01  
% 3.49/1.01  fof(f14,plain,(
% 3.49/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.49/1.01    inference(nnf_transformation,[],[f12])).
% 3.49/1.01  
% 3.49/1.01  fof(f15,plain,(
% 3.49/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.49/1.01    inference(rectify,[],[f14])).
% 3.49/1.01  
% 3.49/1.01  fof(f16,plain,(
% 3.49/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f17,plain,(
% 3.49/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.49/1.01  
% 3.49/1.01  fof(f37,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f17])).
% 3.49/1.01  
% 3.49/1.01  fof(f6,axiom,(
% 3.49/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f24,plain,(
% 3.49/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.49/1.01    inference(nnf_transformation,[],[f6])).
% 3.49/1.01  
% 3.49/1.01  fof(f25,plain,(
% 3.49/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.49/1.01    inference(rectify,[],[f24])).
% 3.49/1.01  
% 3.49/1.01  fof(f26,plain,(
% 3.49/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f27,plain,(
% 3.49/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 3.49/1.01  
% 3.49/1.01  fof(f49,plain,(
% 3.49/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.49/1.01    inference(cnf_transformation,[],[f27])).
% 3.49/1.01  
% 3.49/1.01  fof(f8,axiom,(
% 3.49/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f59,plain,(
% 3.49/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f8])).
% 3.49/1.01  
% 3.49/1.01  fof(f9,axiom,(
% 3.49/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f60,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f9])).
% 3.49/1.01  
% 3.49/1.01  fof(f63,plain,(
% 3.49/1.01    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.49/1.01    inference(definition_unfolding,[],[f59,f60])).
% 3.49/1.01  
% 3.49/1.01  fof(f76,plain,(
% 3.49/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.49/1.01    inference(definition_unfolding,[],[f49,f63])).
% 3.49/1.01  
% 3.49/1.01  fof(f90,plain,(
% 3.49/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.49/1.01    inference(equality_resolution,[],[f76])).
% 3.49/1.01  
% 3.49/1.01  fof(f3,axiom,(
% 3.49/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f23,plain,(
% 3.49/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.49/1.01    inference(nnf_transformation,[],[f3])).
% 3.49/1.01  
% 3.49/1.01  fof(f46,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f23])).
% 3.49/1.01  
% 3.49/1.01  fof(f4,axiom,(
% 3.49/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f47,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f4])).
% 3.49/1.01  
% 3.49/1.01  fof(f70,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.49/1.01    inference(definition_unfolding,[],[f46,f47])).
% 3.49/1.01  
% 3.49/1.01  fof(f10,conjecture,(
% 3.49/1.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f11,negated_conjecture,(
% 3.49/1.01    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 3.49/1.01    inference(negated_conjecture,[],[f10])).
% 3.49/1.01  
% 3.49/1.01  fof(f13,plain,(
% 3.49/1.01    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <~> r2_hidden(X0,X1))),
% 3.49/1.01    inference(ennf_transformation,[],[f11])).
% 3.49/1.01  
% 3.49/1.01  fof(f33,plain,(
% 3.49/1.01    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0))),
% 3.49/1.01    inference(nnf_transformation,[],[f13])).
% 3.49/1.01  
% 3.49/1.01  fof(f34,plain,(
% 3.49/1.01    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)) => ((~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0) & (r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f35,plain,(
% 3.49/1.01    (~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0) & (r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0)),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f34])).
% 3.49/1.01  
% 3.49/1.01  fof(f62,plain,(
% 3.49/1.01    ~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0),
% 3.49/1.01    inference(cnf_transformation,[],[f35])).
% 3.49/1.01  
% 3.49/1.01  fof(f83,plain,(
% 3.49/1.01    ~r2_hidden(sK4,sK5) | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))),
% 3.49/1.01    inference(definition_unfolding,[],[f62,f47,f63])).
% 3.49/1.01  
% 3.49/1.01  fof(f38,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f17])).
% 3.49/1.01  
% 3.49/1.01  fof(f61,plain,(
% 3.49/1.01    r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0),
% 3.49/1.01    inference(cnf_transformation,[],[f35])).
% 3.49/1.01  
% 3.49/1.01  fof(f84,plain,(
% 3.49/1.01    r2_hidden(sK4,sK5) | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))),
% 3.49/1.01    inference(definition_unfolding,[],[f61,f47,f63])).
% 3.49/1.01  
% 3.49/1.01  fof(f36,plain,(
% 3.49/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f17])).
% 3.49/1.01  
% 3.49/1.01  fof(f7,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f28,plain,(
% 3.49/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.49/1.01    inference(nnf_transformation,[],[f7])).
% 3.49/1.01  
% 3.49/1.01  fof(f29,plain,(
% 3.49/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.49/1.01    inference(flattening,[],[f28])).
% 3.49/1.01  
% 3.49/1.01  fof(f30,plain,(
% 3.49/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.49/1.01    inference(rectify,[],[f29])).
% 3.49/1.01  
% 3.49/1.01  fof(f31,plain,(
% 3.49/1.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f32,plain,(
% 3.49/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 3.49/1.01  
% 3.49/1.01  fof(f54,plain,(
% 3.49/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.49/1.01    inference(cnf_transformation,[],[f32])).
% 3.49/1.01  
% 3.49/1.01  fof(f81,plain,(
% 3.49/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 3.49/1.01    inference(definition_unfolding,[],[f54,f60])).
% 3.49/1.01  
% 3.49/1.01  fof(f93,plain,(
% 3.49/1.01    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 3.49/1.01    inference(equality_resolution,[],[f81])).
% 3.49/1.01  
% 3.49/1.01  fof(f94,plain,(
% 3.49/1.01    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 3.49/1.01    inference(equality_resolution,[],[f93])).
% 3.49/1.01  
% 3.49/1.01  fof(f45,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.49/1.01    inference(cnf_transformation,[],[f23])).
% 3.49/1.01  
% 3.49/1.01  fof(f71,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.49/1.01    inference(definition_unfolding,[],[f45,f47])).
% 3.49/1.01  
% 3.49/1.01  fof(f50,plain,(
% 3.49/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.49/1.01    inference(cnf_transformation,[],[f27])).
% 3.49/1.01  
% 3.49/1.01  fof(f75,plain,(
% 3.49/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 3.49/1.01    inference(definition_unfolding,[],[f50,f63])).
% 3.49/1.01  
% 3.49/1.01  fof(f88,plain,(
% 3.49/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 3.49/1.01    inference(equality_resolution,[],[f75])).
% 3.49/1.01  
% 3.49/1.01  fof(f89,plain,(
% 3.49/1.01    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 3.49/1.01    inference(equality_resolution,[],[f88])).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1,plain,
% 3.49/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_884,plain,
% 3.49/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.49/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_15,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.49/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_871,plain,
% 3.49/1.01      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1423,plain,
% 3.49/1.01      ( sK0(k1_enumset1(X0,X0,X0),X1) = X0
% 3.49/1.01      | r1_tarski(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_884,c_871]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9,plain,
% 3.49/1.01      ( ~ r1_tarski(X0,X1)
% 3.49/1.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_876,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.49/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3207,plain,
% 3.49/1.01      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),X1)) = k1_xboole_0
% 3.49/1.01      | sK0(k1_enumset1(X0,X0,X0),X1) = X0 ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_1423,c_876]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_22,negated_conjecture,
% 3.49/1.01      ( ~ r2_hidden(sK4,sK5)
% 3.49/1.01      | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_864,plain,
% 3.49/1.01      ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))
% 3.49/1.01      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11263,plain,
% 3.49/1.01      ( sK0(k1_enumset1(sK4,sK4,sK4),sK5) = sK4
% 3.49/1.01      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_3207,c_864]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_385,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.49/1.01      theory(equality) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3617,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,X1)
% 3.49/1.01      | r2_hidden(sK0(k1_enumset1(sK4,sK4,sK4),sK5),sK5)
% 3.49/1.01      | sK0(k1_enumset1(sK4,sK4,sK4),sK5) != X0
% 3.49/1.01      | sK5 != X1 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_385]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9593,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,sK5)
% 3.49/1.01      | r2_hidden(sK0(k1_enumset1(sK4,sK4,sK4),sK5),sK5)
% 3.49/1.01      | sK0(k1_enumset1(sK4,sK4,sK4),sK5) != X0
% 3.49/1.01      | sK5 != sK5 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_3617]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9595,plain,
% 3.49/1.01      ( r2_hidden(sK0(k1_enumset1(sK4,sK4,sK4),sK5),sK5)
% 3.49/1.01      | ~ r2_hidden(sK4,sK5)
% 3.49/1.01      | sK0(k1_enumset1(sK4,sK4,sK4),sK5) != sK4
% 3.49/1.01      | sK5 != sK5 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_9593]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2691,plain,
% 3.49/1.01      ( ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5)
% 3.49/1.01      | k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_0,plain,
% 3.49/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_885,plain,
% 3.49/1.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.49/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1511,plain,
% 3.49/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_884,c_885]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_23,negated_conjecture,
% 3.49/1.01      ( r2_hidden(sK4,sK5)
% 3.49/1.01      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_863,plain,
% 3.49/1.01      ( k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))
% 3.49/1.01      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.49/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_883,plain,
% 3.49/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.49/1.01      | r2_hidden(X0,X2) = iProver_top
% 3.49/1.01      | r1_tarski(X1,X2) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2055,plain,
% 3.49/1.01      ( k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) = k1_xboole_0
% 3.49/1.01      | r2_hidden(sK4,X0) = iProver_top
% 3.49/1.01      | r1_tarski(sK5,X0) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_863,c_883]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_20,plain,
% 3.49/1.01      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_29,plain,
% 3.49/1.01      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_31,plain,
% 3.49/1.01      ( r2_hidden(sK4,k1_enumset1(sK4,sK4,sK4)) = iProver_top ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_916,plain,
% 3.49/1.01      ( ~ r2_hidden(sK4,X0) | r2_hidden(sK4,sK5) | ~ r1_tarski(X0,sK5) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_963,plain,
% 3.49/1.01      ( ~ r2_hidden(sK4,k1_enumset1(sK4,sK4,sK4))
% 3.49/1.01      | r2_hidden(sK4,sK5)
% 3.49/1.01      | ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_916]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_964,plain,
% 3.49/1.01      ( r2_hidden(sK4,k1_enumset1(sK4,sK4,sK4)) != iProver_top
% 3.49/1.01      | r2_hidden(sK4,sK5) = iProver_top
% 3.49/1.01      | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_10,plain,
% 3.49/1.01      ( r1_tarski(X0,X1)
% 3.49/1.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1011,plain,
% 3.49/1.01      ( r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5)
% 3.49/1.01      | k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1018,plain,
% 3.49/1.01      ( k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_xboole_0
% 3.49/1.01      | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_958,plain,
% 3.49/1.01      ( ~ r2_hidden(sK4,X0) | r2_hidden(sK4,X1) | ~ r1_tarski(X0,X1) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1087,plain,
% 3.49/1.01      ( r2_hidden(sK4,X0) | ~ r2_hidden(sK4,sK5) | ~ r1_tarski(sK5,X0) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_958]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1095,plain,
% 3.49/1.01      ( r2_hidden(sK4,X0) = iProver_top
% 3.49/1.01      | r2_hidden(sK4,sK5) != iProver_top
% 3.49/1.01      | r1_tarski(sK5,X0) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1087]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2065,plain,
% 3.49/1.01      ( r2_hidden(sK4,X0) = iProver_top
% 3.49/1.01      | r1_tarski(sK5,X0) != iProver_top ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_2055,c_31,c_964,c_1018,c_1095]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2071,plain,
% 3.49/1.01      ( r2_hidden(sK4,sK5) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_1511,c_2065]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_383,plain,( X0 = X0 ),theory(equality) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1835,plain,
% 3.49/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_383]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_14,plain,
% 3.49/1.01      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1416,plain,
% 3.49/1.01      ( r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5)) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_384,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1104,plain,
% 3.49/1.01      ( k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) != X0
% 3.49/1.01      | k1_xboole_0 != X0
% 3.49/1.01      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_384]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1337,plain,
% 3.49/1.01      ( k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_xboole_0
% 3.49/1.01      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))
% 3.49/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_1104]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1001,plain,
% 3.49/1.01      ( ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0)) | sK5 = X0 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1154,plain,
% 3.49/1.01      ( ~ r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5)) | sK5 = sK5 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_1001]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1012,plain,
% 3.49/1.01      ( ~ r2_hidden(sK0(k1_enumset1(sK4,sK4,sK4),sK5),sK5)
% 3.49/1.01      | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK5) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_25,plain,
% 3.49/1.01      ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK4,sK4,sK4),k3_xboole_0(k1_enumset1(sK4,sK4,sK4),sK5))
% 3.49/1.01      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(contradiction,plain,
% 3.49/1.01      ( $false ),
% 3.49/1.01      inference(minisat,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_11263,c_9595,c_2691,c_2071,c_1835,c_1416,c_1337,
% 3.49/1.01                 c_1154,c_1012,c_25,c_23]) ).
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  ------                               Statistics
% 3.49/1.01  
% 3.49/1.01  ------ General
% 3.49/1.01  
% 3.49/1.01  abstr_ref_over_cycles:                  0
% 3.49/1.01  abstr_ref_under_cycles:                 0
% 3.49/1.01  gc_basic_clause_elim:                   0
% 3.49/1.01  forced_gc_time:                         0
% 3.49/1.01  parsing_time:                           0.012
% 3.49/1.01  unif_index_cands_time:                  0.
% 3.49/1.01  unif_index_add_time:                    0.
% 3.49/1.01  orderings_time:                         0.
% 3.49/1.01  out_proof_time:                         0.007
% 3.49/1.01  total_time:                             0.468
% 3.49/1.01  num_of_symbols:                         43
% 3.49/1.01  num_of_terms:                           16841
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing
% 3.49/1.01  
% 3.49/1.01  num_of_splits:                          0
% 3.49/1.01  num_of_split_atoms:                     0
% 3.49/1.01  num_of_reused_defs:                     0
% 3.49/1.01  num_eq_ax_congr_red:                    24
% 3.49/1.01  num_of_sem_filtered_clauses:            1
% 3.49/1.01  num_of_subtypes:                        0
% 3.49/1.01  monotx_restored_types:                  0
% 3.49/1.01  sat_num_of_epr_types:                   0
% 3.49/1.01  sat_num_of_non_cyclic_types:            0
% 3.49/1.01  sat_guarded_non_collapsed_types:        0
% 3.49/1.01  num_pure_diseq_elim:                    0
% 3.49/1.01  simp_replaced_by:                       0
% 3.49/1.01  res_preprocessed:                       85
% 3.49/1.01  prep_upred:                             0
% 3.49/1.01  prep_unflattend:                        6
% 3.49/1.01  smt_new_axioms:                         0
% 3.49/1.01  pred_elim_cands:                        2
% 3.49/1.01  pred_elim:                              0
% 3.49/1.01  pred_elim_cl:                           0
% 3.49/1.01  pred_elim_cycles:                       1
% 3.49/1.01  merged_defs:                            12
% 3.49/1.01  merged_defs_ncl:                        0
% 3.49/1.01  bin_hyper_res:                          12
% 3.49/1.01  prep_cycles:                            3
% 3.49/1.01  pred_elim_time:                         0.002
% 3.49/1.01  splitting_time:                         0.
% 3.49/1.01  sem_filter_time:                        0.
% 3.49/1.01  monotx_time:                            0.001
% 3.49/1.01  subtype_inf_time:                       0.
% 3.49/1.01  
% 3.49/1.01  ------ Problem properties
% 3.49/1.01  
% 3.49/1.01  clauses:                                24
% 3.49/1.01  conjectures:                            2
% 3.49/1.01  epr:                                    1
% 3.49/1.01  horn:                                   15
% 3.49/1.01  ground:                                 2
% 3.49/1.01  unary:                                  4
% 3.49/1.01  binary:                                 9
% 3.49/1.01  lits:                                   57
% 3.49/1.01  lits_eq:                                22
% 3.49/1.01  fd_pure:                                0
% 3.49/1.01  fd_pseudo:                              0
% 3.49/1.01  fd_cond:                                0
% 3.49/1.01  fd_pseudo_cond:                         8
% 3.49/1.01  ac_symbols:                             0
% 3.49/1.01  
% 3.49/1.01  ------ Propositional Solver
% 3.49/1.01  
% 3.49/1.01  prop_solver_calls:                      26
% 3.49/1.01  prop_fast_solver_calls:                 728
% 3.49/1.01  smt_solver_calls:                       0
% 3.49/1.01  smt_fast_solver_calls:                  0
% 3.49/1.01  prop_num_of_clauses:                    4576
% 3.49/1.01  prop_preprocess_simplified:             9520
% 3.49/1.01  prop_fo_subsumed:                       19
% 3.49/1.01  prop_solver_time:                       0.
% 3.49/1.01  smt_solver_time:                        0.
% 3.49/1.01  smt_fast_solver_time:                   0.
% 3.49/1.01  prop_fast_solver_time:                  0.
% 3.49/1.01  prop_unsat_core_time:                   0.
% 3.49/1.01  
% 3.49/1.01  ------ QBF
% 3.49/1.01  
% 3.49/1.01  qbf_q_res:                              0
% 3.49/1.01  qbf_num_tautologies:                    0
% 3.49/1.01  qbf_prep_cycles:                        0
% 3.49/1.01  
% 3.49/1.01  ------ BMC1
% 3.49/1.01  
% 3.49/1.01  bmc1_current_bound:                     -1
% 3.49/1.01  bmc1_last_solved_bound:                 -1
% 3.49/1.01  bmc1_unsat_core_size:                   -1
% 3.49/1.01  bmc1_unsat_core_parents_size:           -1
% 3.49/1.01  bmc1_merge_next_fun:                    0
% 3.49/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.49/1.01  
% 3.49/1.01  ------ Instantiation
% 3.49/1.01  
% 3.49/1.01  inst_num_of_clauses:                    1096
% 3.49/1.01  inst_num_in_passive:                    177
% 3.49/1.01  inst_num_in_active:                     436
% 3.49/1.01  inst_num_in_unprocessed:                483
% 3.49/1.01  inst_num_of_loops:                      580
% 3.49/1.01  inst_num_of_learning_restarts:          0
% 3.49/1.01  inst_num_moves_active_passive:          143
% 3.49/1.01  inst_lit_activity:                      0
% 3.49/1.01  inst_lit_activity_moves:                0
% 3.49/1.01  inst_num_tautologies:                   0
% 3.49/1.01  inst_num_prop_implied:                  0
% 3.49/1.01  inst_num_existing_simplified:           0
% 3.49/1.01  inst_num_eq_res_simplified:             0
% 3.49/1.01  inst_num_child_elim:                    0
% 3.49/1.01  inst_num_of_dismatching_blockings:      1599
% 3.49/1.01  inst_num_of_non_proper_insts:           1522
% 3.49/1.01  inst_num_of_duplicates:                 0
% 3.49/1.01  inst_inst_num_from_inst_to_res:         0
% 3.49/1.01  inst_dismatching_checking_time:         0.
% 3.49/1.01  
% 3.49/1.01  ------ Resolution
% 3.49/1.01  
% 3.49/1.01  res_num_of_clauses:                     0
% 3.49/1.01  res_num_in_passive:                     0
% 3.49/1.01  res_num_in_active:                      0
% 3.49/1.01  res_num_of_loops:                       88
% 3.49/1.01  res_forward_subset_subsumed:            103
% 3.49/1.01  res_backward_subset_subsumed:           0
% 3.49/1.01  res_forward_subsumed:                   0
% 3.49/1.01  res_backward_subsumed:                  0
% 3.49/1.01  res_forward_subsumption_resolution:     0
% 3.49/1.01  res_backward_subsumption_resolution:    0
% 3.49/1.01  res_clause_to_clause_subsumption:       2151
% 3.49/1.01  res_orphan_elimination:                 0
% 3.49/1.01  res_tautology_del:                      70
% 3.49/1.01  res_num_eq_res_simplified:              0
% 3.49/1.01  res_num_sel_changes:                    0
% 3.49/1.01  res_moves_from_active_to_pass:          0
% 3.49/1.01  
% 3.49/1.01  ------ Superposition
% 3.49/1.01  
% 3.49/1.01  sup_time_total:                         0.
% 3.49/1.01  sup_time_generating:                    0.
% 3.49/1.01  sup_time_sim_full:                      0.
% 3.49/1.01  sup_time_sim_immed:                     0.
% 3.49/1.01  
% 3.49/1.01  sup_num_of_clauses:                     352
% 3.49/1.01  sup_num_in_active:                      109
% 3.49/1.01  sup_num_in_passive:                     243
% 3.49/1.01  sup_num_of_loops:                       114
% 3.49/1.01  sup_fw_superposition:                   642
% 3.49/1.01  sup_bw_superposition:                   575
% 3.49/1.01  sup_immediate_simplified:               313
% 3.49/1.01  sup_given_eliminated:                   0
% 3.49/1.01  comparisons_done:                       0
% 3.49/1.01  comparisons_avoided:                    49
% 3.49/1.01  
% 3.49/1.01  ------ Simplifications
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  sim_fw_subset_subsumed:                 54
% 3.49/1.01  sim_bw_subset_subsumed:                 21
% 3.49/1.01  sim_fw_subsumed:                        152
% 3.49/1.01  sim_bw_subsumed:                        11
% 3.49/1.01  sim_fw_subsumption_res:                 0
% 3.49/1.01  sim_bw_subsumption_res:                 0
% 3.49/1.01  sim_tautology_del:                      17
% 3.49/1.01  sim_eq_tautology_del:                   95
% 3.49/1.01  sim_eq_res_simp:                        4
% 3.49/1.01  sim_fw_demodulated:                     158
% 3.49/1.01  sim_bw_demodulated:                     0
% 3.49/1.01  sim_light_normalised:                   33
% 3.49/1.01  sim_joinable_taut:                      0
% 3.49/1.01  sim_joinable_simp:                      0
% 3.49/1.01  sim_ac_normalised:                      0
% 3.49/1.01  sim_smt_subsumption:                    0
% 3.49/1.01  
%------------------------------------------------------------------------------
