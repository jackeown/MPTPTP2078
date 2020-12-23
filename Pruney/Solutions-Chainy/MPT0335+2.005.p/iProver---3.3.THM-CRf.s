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
% DateTime   : Thu Dec  3 11:38:25 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  154 (3601 expanded)
%              Number of clauses        :   91 ( 692 expanded)
%              Number of leaves         :   17 ( 998 expanded)
%              Depth                    :   33
%              Number of atoms          :  360 (11148 expanded)
%              Number of equality atoms :  225 (5433 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f55,f55])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK3,sK5) != k1_tarski(sK6)
      & r2_hidden(sK6,sK3)
      & k3_xboole_0(sK4,sK5) = k1_tarski(sK6)
      & r1_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k3_xboole_0(sK3,sK5) != k1_tarski(sK6)
    & r2_hidden(sK6,sK3)
    & k3_xboole_0(sK4,sK5) = k1_tarski(sK6)
    & r1_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f36])).

fof(f64,plain,(
    k3_xboole_0(sK4,sK5) = k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f79,plain,(
    k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(definition_unfolding,[],[f64,f55,f68])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f85,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f76])).

fof(f86,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f85])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f56,f68])).

fof(f87,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f65,plain,(
    r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f52,f55,f55,f55,f55])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f63,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f55])).

fof(f66,plain,(
    k3_xboole_0(sK3,sK5) != k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(definition_unfolding,[],[f66,f55,f68])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_667,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) ),
    inference(demodulation,[status(thm)],[c_0,c_23])).

cnf(c_19,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_637,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_932,plain,
    ( r2_hidden(sK6,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_637])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_646,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_636,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1002,plain,
    ( sK6 = X0
    | r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_636])).

cnf(c_8136,plain,
    ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,X1) = sK6
    | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = X1
    | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_646,c_1002])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_643,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9457,plain,
    ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(X1,X2)) = sK6
    | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8136,c_643])).

cnf(c_14224,plain,
    ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X1)) = sK6
    | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X1) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) ),
    inference(superposition,[status(thm)],[c_9457,c_1002])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_635,plain,
    ( r2_hidden(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_644,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9458,plain,
    ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(X1,X2)) = sK6
    | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8136,c_644])).

cnf(c_18969,plain,
    ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X1)) = sK6
    | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X1)
    | r2_hidden(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14224,c_9458])).

cnf(c_19407,plain,
    ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)) = sK6
    | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
    inference(superposition,[status(thm)],[c_635,c_18969])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_647,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19677,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)
    | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)) = iProver_top
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19407,c_647])).

cnf(c_19723,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)
    | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)),sK3) != iProver_top
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19677,c_644])).

cnf(c_20508,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)
    | r2_hidden(sK6,X0) != iProver_top
    | r2_hidden(sK6,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14224,c_19723])).

cnf(c_26,plain,
    ( r2_hidden(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23774,plain,
    ( r2_hidden(sK6,X0) != iProver_top
    | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20508,c_26])).

cnf(c_23775,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_23774])).

cnf(c_23786,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
    inference(superposition,[status(thm)],[c_932,c_23775])).

cnf(c_16,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1068,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_16])).

cnf(c_1270,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_1068])).

cnf(c_1302,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_1270,c_1068])).

cnf(c_1392,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_0,c_1302])).

cnf(c_23992,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),sK4) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
    inference(superposition,[status(thm)],[c_23786,c_1392])).

cnf(c_14,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1078,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_14])).

cnf(c_6692,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_0,c_1078])).

cnf(c_23993,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)))))) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)) ),
    inference(superposition,[status(thm)],[c_23786,c_6692])).

cnf(c_1097,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_14])).

cnf(c_1267,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_14,c_1068])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_634,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_640,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1600,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_634,c_640])).

cnf(c_1613,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1600,c_16])).

cnf(c_6676,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) ),
    inference(superposition,[status(thm)],[c_1613,c_1078])).

cnf(c_7027,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(X0,k4_xboole_0(X0,sK3)) ),
    inference(demodulation,[status(thm)],[c_6676,c_10])).

cnf(c_8503,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_10,c_7027])).

cnf(c_8577,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_8503,c_10])).

cnf(c_8604,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_8577,c_14])).

cnf(c_8991,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_8604])).

cnf(c_24004,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,sK5)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_23993,c_1097,c_1267,c_8991])).

cnf(c_24005,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_24004,c_10])).

cnf(c_24007,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
    inference(light_normalisation,[status(thm)],[c_23992,c_24005])).

cnf(c_24009,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4) ),
    inference(demodulation,[status(thm)],[c_24007,c_23786])).

cnf(c_6668,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_1078])).

cnf(c_25298,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK4)))) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4)) ),
    inference(superposition,[status(thm)],[c_24009,c_6668])).

cnf(c_25300,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)))))) ),
    inference(superposition,[status(thm)],[c_24009,c_6692])).

cnf(c_25430,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,sK5)))) ),
    inference(demodulation,[status(thm)],[c_25300,c_1267])).

cnf(c_25431,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_25430,c_10])).

cnf(c_25435,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK4)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_25298,c_25431])).

cnf(c_2117,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_643])).

cnf(c_4741,plain,
    ( r2_hidden(sK6,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_2117])).

cnf(c_23790,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK4) ),
    inference(superposition,[status(thm)],[c_4741,c_23775])).

cnf(c_25437,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_25435,c_23790])).

cnf(c_1101,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_16,c_14])).

cnf(c_20542,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_16,c_1101])).

cnf(c_21039,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_20542,c_16])).

cnf(c_25438,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)))))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_25437,c_1097,c_21039])).

cnf(c_25439,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_25438,c_1068,c_8991])).

cnf(c_333,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_965,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) != X0
    | k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))
    | k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_5315,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
    | k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))
    | k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_977,plain,
    ( X0 != X1
    | k2_enumset1(sK6,sK6,sK6,sK6) != X1
    | k2_enumset1(sK6,sK6,sK6,sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_1977,plain,
    ( X0 != k2_enumset1(X1,X2,X3,X4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = X0
    | k2_enumset1(sK6,sK6,sK6,sK6) != k2_enumset1(X1,X2,X3,X4) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_4278,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) != k2_enumset1(sK6,sK6,sK6,sK6)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
    | k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_875,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_815,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) != X0
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != X0
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_874,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) != k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6)
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_337,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_341,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK6,sK6,sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_31,plain,
    ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_28,plain,
    ( ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25439,c_5315,c_4278,c_875,c_874,c_341,c_31,c_28,c_21,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.81/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.49  
% 7.81/1.49  ------  iProver source info
% 7.81/1.49  
% 7.81/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.49  git: non_committed_changes: false
% 7.81/1.49  git: last_make_outside_of_git: false
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    --mode clausify
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             all
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         305.
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              default
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           true
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             true
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    true
% 7.81/1.49  --inst_sos_flag                         false
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     num_symb
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       true
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    passive
% 7.81/1.49  --sup_prop_simpl_new                    true
% 7.81/1.49  --sup_prop_simpl_given                  true
% 7.81/1.49  --sup_fun_splitting                     false
% 7.81/1.49  --sup_smt_interval                      50000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   []
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_full_bw                           [BwDemod]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         3
% 7.81/1.49  --comb_sup_mult                         2
% 7.81/1.49  --comb_inst_mult                        10
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  ------ Parsing...
% 7.81/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.49  ------ Proving...
% 7.81/1.49  ------ Problem Properties 
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  clauses                                 24
% 7.81/1.49  conjectures                             4
% 7.81/1.49  EPR                                     5
% 7.81/1.49  Horn                                    18
% 7.81/1.49  unary                                   10
% 7.81/1.49  binary                                  6
% 7.81/1.49  lits                                    47
% 7.81/1.49  lits eq                                 16
% 7.81/1.49  fd_pure                                 0
% 7.81/1.49  fd_pseudo                               0
% 7.81/1.49  fd_cond                                 0
% 7.81/1.49  fd_pseudo_cond                          6
% 7.81/1.49  AC symbols                              0
% 7.81/1.49  
% 7.81/1.49  ------ Schedule dynamic 5 is on 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  Current options:
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    --mode clausify
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             all
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         305.
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              default
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           true
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             true
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    true
% 7.81/1.49  --inst_sos_flag                         false
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     none
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       false
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    passive
% 7.81/1.49  --sup_prop_simpl_new                    true
% 7.81/1.49  --sup_prop_simpl_given                  true
% 7.81/1.49  --sup_fun_splitting                     false
% 7.81/1.49  --sup_smt_interval                      50000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   []
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_full_bw                           [BwDemod]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         3
% 7.81/1.49  --comb_sup_mult                         2
% 7.81/1.49  --comb_inst_mult                        10
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ Proving...
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  % SZS status Theorem for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  fof(f1,axiom,(
% 7.81/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f38,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f1])).
% 7.81/1.49  
% 7.81/1.49  fof(f9,axiom,(
% 7.81/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f55,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f9])).
% 7.81/1.49  
% 7.81/1.49  fof(f69,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f38,f55,f55])).
% 7.81/1.49  
% 7.81/1.49  fof(f14,conjecture,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f15,negated_conjecture,(
% 7.81/1.49    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 7.81/1.49    inference(negated_conjecture,[],[f14])).
% 7.81/1.49  
% 7.81/1.49  fof(f19,plain,(
% 7.81/1.49    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 7.81/1.49    inference(ennf_transformation,[],[f15])).
% 7.81/1.49  
% 7.81/1.49  fof(f20,plain,(
% 7.81/1.49    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 7.81/1.49    inference(flattening,[],[f19])).
% 7.81/1.49  
% 7.81/1.49  fof(f36,plain,(
% 7.81/1.49    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK3,sK5) != k1_tarski(sK6) & r2_hidden(sK6,sK3) & k3_xboole_0(sK4,sK5) = k1_tarski(sK6) & r1_tarski(sK3,sK4))),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f37,plain,(
% 7.81/1.49    k3_xboole_0(sK3,sK5) != k1_tarski(sK6) & r2_hidden(sK6,sK3) & k3_xboole_0(sK4,sK5) = k1_tarski(sK6) & r1_tarski(sK3,sK4)),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f36])).
% 7.81/1.49  
% 7.81/1.49  fof(f64,plain,(
% 7.81/1.49    k3_xboole_0(sK4,sK5) = k1_tarski(sK6)),
% 7.81/1.49    inference(cnf_transformation,[],[f37])).
% 7.81/1.49  
% 7.81/1.49  fof(f11,axiom,(
% 7.81/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f60,plain,(
% 7.81/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f11])).
% 7.81/1.49  
% 7.81/1.49  fof(f12,axiom,(
% 7.81/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f61,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f12])).
% 7.81/1.49  
% 7.81/1.49  fof(f13,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f62,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f13])).
% 7.81/1.49  
% 7.81/1.49  fof(f67,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.81/1.49    inference(definition_unfolding,[],[f61,f62])).
% 7.81/1.49  
% 7.81/1.49  fof(f68,plain,(
% 7.81/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.81/1.49    inference(definition_unfolding,[],[f60,f67])).
% 7.81/1.49  
% 7.81/1.49  fof(f79,plain,(
% 7.81/1.49    k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6)),
% 7.81/1.49    inference(definition_unfolding,[],[f64,f55,f68])).
% 7.81/1.49  
% 7.81/1.49  fof(f10,axiom,(
% 7.81/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f32,plain,(
% 7.81/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.81/1.49    inference(nnf_transformation,[],[f10])).
% 7.81/1.49  
% 7.81/1.49  fof(f33,plain,(
% 7.81/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.81/1.49    inference(rectify,[],[f32])).
% 7.81/1.49  
% 7.81/1.49  fof(f34,plain,(
% 7.81/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f35,plain,(
% 7.81/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 7.81/1.49  
% 7.81/1.49  fof(f57,plain,(
% 7.81/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.81/1.49    inference(cnf_transformation,[],[f35])).
% 7.81/1.49  
% 7.81/1.49  fof(f76,plain,(
% 7.81/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.81/1.49    inference(definition_unfolding,[],[f57,f68])).
% 7.81/1.49  
% 7.81/1.49  fof(f85,plain,(
% 7.81/1.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 7.81/1.49    inference(equality_resolution,[],[f76])).
% 7.81/1.49  
% 7.81/1.49  fof(f86,plain,(
% 7.81/1.49    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 7.81/1.49    inference(equality_resolution,[],[f85])).
% 7.81/1.49  
% 7.81/1.49  fof(f3,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f25,plain,(
% 7.81/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.49    inference(nnf_transformation,[],[f3])).
% 7.81/1.49  
% 7.81/1.49  fof(f26,plain,(
% 7.81/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.49    inference(flattening,[],[f25])).
% 7.81/1.49  
% 7.81/1.49  fof(f27,plain,(
% 7.81/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.49    inference(rectify,[],[f26])).
% 7.81/1.49  
% 7.81/1.49  fof(f28,plain,(
% 7.81/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f29,plain,(
% 7.81/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 7.81/1.49  
% 7.81/1.49  fof(f45,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f29])).
% 7.81/1.49  
% 7.81/1.49  fof(f56,plain,(
% 7.81/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.81/1.49    inference(cnf_transformation,[],[f35])).
% 7.81/1.49  
% 7.81/1.49  fof(f77,plain,(
% 7.81/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.81/1.49    inference(definition_unfolding,[],[f56,f68])).
% 7.81/1.49  
% 7.81/1.49  fof(f87,plain,(
% 7.81/1.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.81/1.49    inference(equality_resolution,[],[f77])).
% 7.81/1.49  
% 7.81/1.49  fof(f42,plain,(
% 7.81/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.81/1.49    inference(cnf_transformation,[],[f29])).
% 7.81/1.49  
% 7.81/1.49  fof(f82,plain,(
% 7.81/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.81/1.49    inference(equality_resolution,[],[f42])).
% 7.81/1.49  
% 7.81/1.49  fof(f65,plain,(
% 7.81/1.49    r2_hidden(sK6,sK3)),
% 7.81/1.49    inference(cnf_transformation,[],[f37])).
% 7.81/1.49  
% 7.81/1.49  fof(f43,plain,(
% 7.81/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.81/1.49    inference(cnf_transformation,[],[f29])).
% 7.81/1.49  
% 7.81/1.49  fof(f81,plain,(
% 7.81/1.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.81/1.49    inference(equality_resolution,[],[f43])).
% 7.81/1.49  
% 7.81/1.49  fof(f46,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f29])).
% 7.81/1.49  
% 7.81/1.49  fof(f8,axiom,(
% 7.81/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f54,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f8])).
% 7.81/1.49  
% 7.81/1.49  fof(f73,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f54,f55])).
% 7.81/1.49  
% 7.81/1.49  fof(f6,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f52,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f6])).
% 7.81/1.49  
% 7.81/1.49  fof(f71,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f52,f55,f55,f55,f55])).
% 7.81/1.49  
% 7.81/1.49  fof(f4,axiom,(
% 7.81/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f16,plain,(
% 7.81/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.81/1.49    inference(rectify,[],[f4])).
% 7.81/1.49  
% 7.81/1.49  fof(f48,plain,(
% 7.81/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.81/1.49    inference(cnf_transformation,[],[f16])).
% 7.81/1.49  
% 7.81/1.49  fof(f70,plain,(
% 7.81/1.49    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.81/1.49    inference(definition_unfolding,[],[f48,f55])).
% 7.81/1.49  
% 7.81/1.49  fof(f63,plain,(
% 7.81/1.49    r1_tarski(sK3,sK4)),
% 7.81/1.49    inference(cnf_transformation,[],[f37])).
% 7.81/1.49  
% 7.81/1.49  fof(f7,axiom,(
% 7.81/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f18,plain,(
% 7.81/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.81/1.49    inference(ennf_transformation,[],[f7])).
% 7.81/1.49  
% 7.81/1.49  fof(f53,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f18])).
% 7.81/1.49  
% 7.81/1.49  fof(f72,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.81/1.49    inference(definition_unfolding,[],[f53,f55])).
% 7.81/1.49  
% 7.81/1.49  fof(f66,plain,(
% 7.81/1.49    k3_xboole_0(sK3,sK5) != k1_tarski(sK6)),
% 7.81/1.49    inference(cnf_transformation,[],[f37])).
% 7.81/1.49  
% 7.81/1.49  fof(f78,plain,(
% 7.81/1.49    k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6)),
% 7.81/1.49    inference(definition_unfolding,[],[f66,f55,f68])).
% 7.81/1.49  
% 7.81/1.49  cnf(c_0,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23,negated_conjecture,
% 7.81/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
% 7.81/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_667,plain,
% 7.81/1.49      ( k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_0,c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19,plain,
% 7.81/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_637,plain,
% 7.81/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_932,plain,
% 7.81/1.49      ( r2_hidden(sK6,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_667,c_637]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_6,plain,
% 7.81/1.49      ( r2_hidden(sK1(X0,X1,X2),X0)
% 7.81/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.81/1.49      | k4_xboole_0(X0,X1) = X2 ),
% 7.81/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_646,plain,
% 7.81/1.49      ( k4_xboole_0(X0,X1) = X2
% 7.81/1.49      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 7.81/1.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_20,plain,
% 7.81/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.81/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_636,plain,
% 7.81/1.49      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1002,plain,
% 7.81/1.49      ( sK6 = X0
% 7.81/1.49      | r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_667,c_636]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8136,plain,
% 7.81/1.49      ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,X1) = sK6
% 7.81/1.49      | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = X1
% 7.81/1.49      | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,X1),X1) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_646,c_1002]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_9,plain,
% 7.81/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_643,plain,
% 7.81/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.81/1.49      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_9457,plain,
% 7.81/1.49      ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(X1,X2)) = sK6
% 7.81/1.49      | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(X1,X2)
% 7.81/1.49      | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(X1,X2)),X1) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_8136,c_643]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_14224,plain,
% 7.81/1.49      ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X1)) = sK6
% 7.81/1.49      | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X1) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_9457,c_1002]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_22,negated_conjecture,
% 7.81/1.49      ( r2_hidden(sK6,sK3) ),
% 7.81/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_635,plain,
% 7.81/1.49      ( r2_hidden(sK6,sK3) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8,plain,
% 7.81/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_644,plain,
% 7.81/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.81/1.49      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_9458,plain,
% 7.81/1.49      ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(X1,X2)) = sK6
% 7.81/1.49      | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(X1,X2)
% 7.81/1.49      | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_8136,c_644]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_18969,plain,
% 7.81/1.49      ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X1)) = sK6
% 7.81/1.49      | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X1)
% 7.81/1.49      | r2_hidden(sK6,X1) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_14224,c_9458]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19407,plain,
% 7.81/1.49      ( sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)) = sK6
% 7.81/1.49      | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_635,c_18969]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5,plain,
% 7.81/1.49      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 7.81/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.81/1.49      | k4_xboole_0(X0,X1) = X2 ),
% 7.81/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_647,plain,
% 7.81/1.49      ( k4_xboole_0(X0,X1) = X2
% 7.81/1.49      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 7.81/1.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19677,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)
% 7.81/1.49      | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)) = iProver_top
% 7.81/1.49      | r2_hidden(sK6,X0) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_19407,c_647]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19723,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)
% 7.81/1.49      | r2_hidden(sK1(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)),sK3) != iProver_top
% 7.81/1.49      | r2_hidden(sK6,X0) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_19677,c_644]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_20508,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)
% 7.81/1.49      | r2_hidden(sK6,X0) != iProver_top
% 7.81/1.49      | r2_hidden(sK6,sK3) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_14224,c_19723]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_26,plain,
% 7.81/1.49      ( r2_hidden(sK6,sK3) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23774,plain,
% 7.81/1.49      ( r2_hidden(sK6,X0) != iProver_top
% 7.81/1.49      | k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_20508,c_26]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23775,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)
% 7.81/1.49      | r2_hidden(sK6,X0) != iProver_top ),
% 7.81/1.49      inference(renaming,[status(thm)],[c_23774]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23786,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_932,c_23775]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_16,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1068,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_16]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1270,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_1068]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1302,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_1270,c_1068]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1392,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_1302]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23992,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),sK4) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_23786,c_1392]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_14,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1078,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_14]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_6692,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_1078]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23993,plain,
% 7.81/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)))))) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_23786,c_6692]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1097,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_14]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1267,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_14,c_1068]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.81/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_24,negated_conjecture,
% 7.81/1.49      ( r1_tarski(sK3,sK4) ),
% 7.81/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_634,plain,
% 7.81/1.49      ( r1_tarski(sK3,sK4) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_15,plain,
% 7.81/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.81/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_640,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.81/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1600,plain,
% 7.81/1.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = sK3 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_634,c_640]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1613,plain,
% 7.81/1.49      ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK4) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1600,c_16]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_6676,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1613,c_1078]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_7027,plain,
% 7.81/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(X0,k4_xboole_0(X0,sK3)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_6676,c_10]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8503,plain,
% 7.81/1.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_10,c_7027]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8577,plain,
% 7.81/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = sK3 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_8503,c_10]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8604,plain,
% 7.81/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_8577,c_14]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8991,plain,
% 7.81/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_8604]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_24004,plain,
% 7.81/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,sK5)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) ),
% 7.81/1.49      inference(demodulation,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_23993,c_1097,c_1267,c_8991]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_24005,plain,
% 7.81/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_24004,c_10]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_24007,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_23992,c_24005]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_24009,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_24007,c_23786]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_6668,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_1078]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25298,plain,
% 7.81/1.49      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK4)))) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_24009,c_6668]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25300,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)))))) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_24009,c_6692]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25430,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,sK5)))) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_25300,c_1267]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25431,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)),sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_25430,c_10]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25435,plain,
% 7.81/1.49      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK4)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_25298,c_25431]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2117,plain,
% 7.81/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.81/1.49      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_643]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4741,plain,
% 7.81/1.49      ( r2_hidden(sK6,sK4) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_932,c_2117]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23790,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3) = k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK4) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_4741,c_23775]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25437,plain,
% 7.81/1.49      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),k4_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),sK3)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_25435,c_23790]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1101,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_16,c_14]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_20542,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_16,c_1101]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_21039,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_20542,c_16]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25438,plain,
% 7.81/1.49      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)))))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_25437,c_1097,c_21039]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25439,plain,
% 7.81/1.49      ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_25438,c_1068,c_8991]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_333,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_965,plain,
% 7.81/1.49      ( k2_enumset1(sK6,sK6,sK6,sK6) != X0
% 7.81/1.49      | k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))
% 7.81/1.49      | k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) != X0 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_333]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5315,plain,
% 7.81/1.49      ( k2_enumset1(sK6,sK6,sK6,sK6) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
% 7.81/1.49      | k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))
% 7.81/1.49      | k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_965]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_977,plain,
% 7.81/1.49      ( X0 != X1
% 7.81/1.49      | k2_enumset1(sK6,sK6,sK6,sK6) != X1
% 7.81/1.49      | k2_enumset1(sK6,sK6,sK6,sK6) = X0 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_333]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1977,plain,
% 7.81/1.49      ( X0 != k2_enumset1(X1,X2,X3,X4)
% 7.81/1.49      | k2_enumset1(sK6,sK6,sK6,sK6) = X0
% 7.81/1.49      | k2_enumset1(sK6,sK6,sK6,sK6) != k2_enumset1(X1,X2,X3,X4) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_977]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4278,plain,
% 7.81/1.49      ( k2_enumset1(sK6,sK6,sK6,sK6) != k2_enumset1(sK6,sK6,sK6,sK6)
% 7.81/1.49      | k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
% 7.81/1.49      | k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1977]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_875,plain,
% 7.81/1.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_815,plain,
% 7.81/1.49      ( k2_enumset1(sK6,sK6,sK6,sK6) != X0
% 7.81/1.49      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != X0
% 7.81/1.49      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_333]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_874,plain,
% 7.81/1.49      ( k2_enumset1(sK6,sK6,sK6,sK6) != k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))
% 7.81/1.49      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6)
% 7.81/1.49      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_815]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_337,plain,
% 7.81/1.49      ( X0 != X1
% 7.81/1.49      | X2 != X3
% 7.81/1.49      | X4 != X5
% 7.81/1.49      | X6 != X7
% 7.81/1.49      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 7.81/1.49      theory(equality) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_341,plain,
% 7.81/1.49      ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK6,sK6,sK6,sK6)
% 7.81/1.49      | sK6 != sK6 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_337]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_31,plain,
% 7.81/1.49      ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_28,plain,
% 7.81/1.49      ( ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) | sK6 = sK6 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_21,negated_conjecture,
% 7.81/1.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
% 7.81/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(contradiction,plain,
% 7.81/1.49      ( $false ),
% 7.81/1.49      inference(minisat,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_25439,c_5315,c_4278,c_875,c_874,c_341,c_31,c_28,c_21,
% 7.81/1.49                 c_23]) ).
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  ------                               Statistics
% 7.81/1.49  
% 7.81/1.49  ------ General
% 7.81/1.49  
% 7.81/1.49  abstr_ref_over_cycles:                  0
% 7.81/1.49  abstr_ref_under_cycles:                 0
% 7.81/1.49  gc_basic_clause_elim:                   0
% 7.81/1.49  forced_gc_time:                         0
% 7.81/1.49  parsing_time:                           0.011
% 7.81/1.49  unif_index_cands_time:                  0.
% 7.81/1.49  unif_index_add_time:                    0.
% 7.81/1.49  orderings_time:                         0.
% 7.81/1.49  out_proof_time:                         0.011
% 7.81/1.49  total_time:                             0.813
% 7.81/1.49  num_of_symbols:                         42
% 7.81/1.49  num_of_terms:                           32723
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing
% 7.81/1.49  
% 7.81/1.49  num_of_splits:                          0
% 7.81/1.49  num_of_split_atoms:                     0
% 7.81/1.49  num_of_reused_defs:                     0
% 7.81/1.49  num_eq_ax_congr_red:                    21
% 7.81/1.49  num_of_sem_filtered_clauses:            1
% 7.81/1.49  num_of_subtypes:                        0
% 7.81/1.49  monotx_restored_types:                  0
% 7.81/1.49  sat_num_of_epr_types:                   0
% 7.81/1.49  sat_num_of_non_cyclic_types:            0
% 7.81/1.49  sat_guarded_non_collapsed_types:        0
% 7.81/1.49  num_pure_diseq_elim:                    0
% 7.81/1.49  simp_replaced_by:                       0
% 7.81/1.49  res_preprocessed:                       109
% 7.81/1.49  prep_upred:                             0
% 7.81/1.49  prep_unflattend:                        0
% 7.81/1.49  smt_new_axioms:                         0
% 7.81/1.49  pred_elim_cands:                        2
% 7.81/1.49  pred_elim:                              0
% 7.81/1.49  pred_elim_cl:                           0
% 7.81/1.49  pred_elim_cycles:                       2
% 7.81/1.49  merged_defs:                            0
% 7.81/1.49  merged_defs_ncl:                        0
% 7.81/1.49  bin_hyper_res:                          0
% 7.81/1.49  prep_cycles:                            4
% 7.81/1.49  pred_elim_time:                         0.
% 7.81/1.49  splitting_time:                         0.
% 7.81/1.49  sem_filter_time:                        0.
% 7.81/1.49  monotx_time:                            0.
% 7.81/1.49  subtype_inf_time:                       0.
% 7.81/1.49  
% 7.81/1.49  ------ Problem properties
% 7.81/1.49  
% 7.81/1.49  clauses:                                24
% 7.81/1.49  conjectures:                            4
% 7.81/1.49  epr:                                    5
% 7.81/1.49  horn:                                   18
% 7.81/1.49  ground:                                 4
% 7.81/1.49  unary:                                  10
% 7.81/1.49  binary:                                 6
% 7.81/1.49  lits:                                   47
% 7.81/1.49  lits_eq:                                16
% 7.81/1.49  fd_pure:                                0
% 7.81/1.49  fd_pseudo:                              0
% 7.81/1.49  fd_cond:                                0
% 7.81/1.49  fd_pseudo_cond:                         6
% 7.81/1.49  ac_symbols:                             0
% 7.81/1.49  
% 7.81/1.49  ------ Propositional Solver
% 7.81/1.49  
% 7.81/1.49  prop_solver_calls:                      29
% 7.81/1.49  prop_fast_solver_calls:                 740
% 7.81/1.49  smt_solver_calls:                       0
% 7.81/1.49  smt_fast_solver_calls:                  0
% 7.81/1.49  prop_num_of_clauses:                    7466
% 7.81/1.49  prop_preprocess_simplified:             12270
% 7.81/1.49  prop_fo_subsumed:                       5
% 7.81/1.49  prop_solver_time:                       0.
% 7.81/1.49  smt_solver_time:                        0.
% 7.81/1.49  smt_fast_solver_time:                   0.
% 7.81/1.49  prop_fast_solver_time:                  0.
% 7.81/1.49  prop_unsat_core_time:                   0.
% 7.81/1.49  
% 7.81/1.49  ------ QBF
% 7.81/1.49  
% 7.81/1.49  qbf_q_res:                              0
% 7.81/1.49  qbf_num_tautologies:                    0
% 7.81/1.49  qbf_prep_cycles:                        0
% 7.81/1.49  
% 7.81/1.49  ------ BMC1
% 7.81/1.49  
% 7.81/1.49  bmc1_current_bound:                     -1
% 7.81/1.49  bmc1_last_solved_bound:                 -1
% 7.81/1.49  bmc1_unsat_core_size:                   -1
% 7.81/1.49  bmc1_unsat_core_parents_size:           -1
% 7.81/1.49  bmc1_merge_next_fun:                    0
% 7.81/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation
% 7.81/1.49  
% 7.81/1.49  inst_num_of_clauses:                    1508
% 7.81/1.49  inst_num_in_passive:                    567
% 7.81/1.49  inst_num_in_active:                     500
% 7.81/1.49  inst_num_in_unprocessed:                444
% 7.81/1.49  inst_num_of_loops:                      650
% 7.81/1.49  inst_num_of_learning_restarts:          0
% 7.81/1.49  inst_num_moves_active_passive:          148
% 7.81/1.49  inst_lit_activity:                      0
% 7.81/1.49  inst_lit_activity_moves:                0
% 7.81/1.49  inst_num_tautologies:                   0
% 7.81/1.49  inst_num_prop_implied:                  0
% 7.81/1.49  inst_num_existing_simplified:           0
% 7.81/1.49  inst_num_eq_res_simplified:             0
% 7.81/1.49  inst_num_child_elim:                    0
% 7.81/1.49  inst_num_of_dismatching_blockings:      1337
% 7.81/1.49  inst_num_of_non_proper_insts:           1804
% 7.81/1.49  inst_num_of_duplicates:                 0
% 7.81/1.49  inst_inst_num_from_inst_to_res:         0
% 7.81/1.49  inst_dismatching_checking_time:         0.
% 7.81/1.49  
% 7.81/1.49  ------ Resolution
% 7.81/1.49  
% 7.81/1.49  res_num_of_clauses:                     0
% 7.81/1.49  res_num_in_passive:                     0
% 7.81/1.49  res_num_in_active:                      0
% 7.81/1.49  res_num_of_loops:                       113
% 7.81/1.49  res_forward_subset_subsumed:            145
% 7.81/1.49  res_backward_subset_subsumed:           14
% 7.81/1.49  res_forward_subsumed:                   0
% 7.81/1.49  res_backward_subsumed:                  0
% 7.81/1.49  res_forward_subsumption_resolution:     0
% 7.81/1.49  res_backward_subsumption_resolution:    0
% 7.81/1.49  res_clause_to_clause_subsumption:       30695
% 7.81/1.49  res_orphan_elimination:                 0
% 7.81/1.49  res_tautology_del:                      67
% 7.81/1.49  res_num_eq_res_simplified:              0
% 7.81/1.49  res_num_sel_changes:                    0
% 7.81/1.49  res_moves_from_active_to_pass:          0
% 7.81/1.49  
% 7.81/1.49  ------ Superposition
% 7.81/1.49  
% 7.81/1.49  sup_time_total:                         0.
% 7.81/1.49  sup_time_generating:                    0.
% 7.81/1.49  sup_time_sim_full:                      0.
% 7.81/1.49  sup_time_sim_immed:                     0.
% 7.81/1.49  
% 7.81/1.49  sup_num_of_clauses:                     1255
% 7.81/1.49  sup_num_in_active:                      119
% 7.81/1.49  sup_num_in_passive:                     1136
% 7.81/1.49  sup_num_of_loops:                       129
% 7.81/1.49  sup_fw_superposition:                   2254
% 7.81/1.49  sup_bw_superposition:                   2306
% 7.81/1.49  sup_immediate_simplified:               1886
% 7.81/1.49  sup_given_eliminated:                   9
% 7.81/1.49  comparisons_done:                       0
% 7.81/1.49  comparisons_avoided:                    50
% 7.81/1.49  
% 7.81/1.49  ------ Simplifications
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  sim_fw_subset_subsumed:                 81
% 7.81/1.49  sim_bw_subset_subsumed:                 16
% 7.81/1.49  sim_fw_subsumed:                        343
% 7.81/1.49  sim_bw_subsumed:                        68
% 7.81/1.49  sim_fw_subsumption_res:                 5
% 7.81/1.49  sim_bw_subsumption_res:                 1
% 7.81/1.49  sim_tautology_del:                      55
% 7.81/1.49  sim_eq_tautology_del:                   331
% 7.81/1.49  sim_eq_res_simp:                        1
% 7.81/1.49  sim_fw_demodulated:                     1136
% 7.81/1.49  sim_bw_demodulated:                     89
% 7.81/1.49  sim_light_normalised:                   749
% 7.81/1.49  sim_joinable_taut:                      0
% 7.81/1.49  sim_joinable_simp:                      0
% 7.81/1.49  sim_ac_normalised:                      0
% 7.81/1.49  sim_smt_subsumption:                    0
% 7.81/1.49  
%------------------------------------------------------------------------------
