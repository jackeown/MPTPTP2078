%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:55 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 228 expanded)
%              Number of clauses        :   40 (  52 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  274 ( 533 expanded)
%              Number of equality atoms :  191 ( 382 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f30])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f85,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f57,f68,f68])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK3 != sK5
      & sK3 != sK4
      & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( sK3 != sK5
    & sK3 != sK4
    & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f27,f37])).

fof(f65,plain,(
    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f87,plain,(
    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f65,f70,f69])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f48,f62,f70])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f88,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f89,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f88])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f67,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_394,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_396,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_398,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2568,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_396,c_398])).

cnf(c_3273,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_394,c_2568])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4474,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3273,c_0])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4486,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4474,c_7])).

cnf(c_4487,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4486,c_3273])).

cnf(c_17,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_385,plain,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_988,plain,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17,c_385])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_395,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1755,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_988,c_395])).

cnf(c_1758,plain,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_1755,c_0])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_902,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_1760,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_1758,c_902])).

cnf(c_5730,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4487,c_1760])).

cnf(c_1,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1287,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X0,X0,X0,X1,X2))) = k3_enumset1(X2,X2,X1,X0,X3) ),
    inference(superposition,[status(thm)],[c_17,c_1])).

cnf(c_5759,plain,
    ( k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK4,sK4),k1_xboole_0) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_5730,c_1287])).

cnf(c_5761,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK5,sK3) = k3_enumset1(sK5,sK5,sK5,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_5759,c_7])).

cnf(c_13,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_389,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5885,plain,
    ( r2_hidden(sK3,k3_enumset1(sK5,sK5,sK5,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5761,c_389])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_547,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(X0,X0,X0,X1,sK4))
    | sK3 = X0
    | sK3 = X1
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1348,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(X0,X0,X0,sK4,sK4))
    | sK3 = X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_6014,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK5,sK5,sK5,sK4,sK4))
    | sK3 = sK4
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_6015,plain,
    ( sK3 = sK4
    | sK3 = sK5
    | r2_hidden(sK3,k3_enumset1(sK5,sK5,sK5,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6014])).

cnf(c_19,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_20,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5885,c_6015,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:58:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.56/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/0.98  
% 3.56/0.98  ------  iProver source info
% 3.56/0.98  
% 3.56/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.56/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/0.98  git: non_committed_changes: false
% 3.56/0.98  git: last_make_outside_of_git: false
% 3.56/0.98  
% 3.56/0.98  ------ 
% 3.56/0.98  ------ Parsing...
% 3.56/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/0.98  ------ Proving...
% 3.56/0.98  ------ Problem Properties 
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  clauses                                 22
% 3.56/0.98  conjectures                             3
% 3.56/0.98  EPR                                     3
% 3.56/0.98  Horn                                    18
% 3.56/0.98  unary                                   13
% 3.56/0.98  binary                                  4
% 3.56/0.98  lits                                    39
% 3.56/0.98  lits eq                                 23
% 3.56/0.98  fd_pure                                 0
% 3.56/0.98  fd_pseudo                               0
% 3.56/0.98  fd_cond                                 1
% 3.56/0.98  fd_pseudo_cond                          4
% 3.56/0.98  AC symbols                              0
% 3.56/0.98  
% 3.56/0.98  ------ Input Options Time Limit: Unbounded
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  ------ 
% 3.56/0.98  Current options:
% 3.56/0.98  ------ 
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  ------ Proving...
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  % SZS status Theorem for theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  fof(f8,axiom,(
% 3.56/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f47,plain,(
% 3.56/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f8])).
% 3.56/0.98  
% 3.56/0.98  fof(f3,axiom,(
% 3.56/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f24,plain,(
% 3.56/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.56/0.98    inference(ennf_transformation,[],[f3])).
% 3.56/0.98  
% 3.56/0.98  fof(f30,plain,(
% 3.56/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.56/0.98    introduced(choice_axiom,[])).
% 3.56/0.98  
% 3.56/0.98  fof(f31,plain,(
% 3.56/0.98    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f30])).
% 3.56/0.98  
% 3.56/0.98  fof(f42,plain,(
% 3.56/0.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.56/0.98    inference(cnf_transformation,[],[f31])).
% 3.56/0.98  
% 3.56/0.98  fof(f2,axiom,(
% 3.56/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f22,plain,(
% 3.56/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.56/0.98    inference(rectify,[],[f2])).
% 3.56/0.98  
% 3.56/0.98  fof(f23,plain,(
% 3.56/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.56/0.98    inference(ennf_transformation,[],[f22])).
% 3.56/0.98  
% 3.56/0.98  fof(f28,plain,(
% 3.56/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.56/0.98    introduced(choice_axiom,[])).
% 3.56/0.98  
% 3.56/0.98  fof(f29,plain,(
% 3.56/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).
% 3.56/0.98  
% 3.56/0.98  fof(f41,plain,(
% 3.56/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.56/0.98    inference(cnf_transformation,[],[f29])).
% 3.56/0.98  
% 3.56/0.98  fof(f6,axiom,(
% 3.56/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f45,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.56/0.98    inference(cnf_transformation,[],[f6])).
% 3.56/0.98  
% 3.56/0.98  fof(f74,plain,(
% 3.56/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.56/0.98    inference(definition_unfolding,[],[f41,f45])).
% 3.56/0.98  
% 3.56/0.98  fof(f4,axiom,(
% 3.56/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f43,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.56/0.98    inference(cnf_transformation,[],[f4])).
% 3.56/0.98  
% 3.56/0.98  fof(f71,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.56/0.98    inference(definition_unfolding,[],[f43,f45])).
% 3.56/0.98  
% 3.56/0.98  fof(f7,axiom,(
% 3.56/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f46,plain,(
% 3.56/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.56/0.98    inference(cnf_transformation,[],[f7])).
% 3.56/0.98  
% 3.56/0.98  fof(f11,axiom,(
% 3.56/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f57,plain,(
% 3.56/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f11])).
% 3.56/0.98  
% 3.56/0.98  fof(f15,axiom,(
% 3.56/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f61,plain,(
% 3.56/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f15])).
% 3.56/0.98  
% 3.56/0.98  fof(f16,axiom,(
% 3.56/0.98    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f62,plain,(
% 3.56/0.98    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f16])).
% 3.56/0.98  
% 3.56/0.98  fof(f68,plain,(
% 3.56/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f61,f62])).
% 3.56/0.98  
% 3.56/0.98  fof(f85,plain,(
% 3.56/0.98    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f57,f68,f68])).
% 3.56/0.98  
% 3.56/0.98  fof(f19,conjecture,(
% 3.56/0.98    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f20,negated_conjecture,(
% 3.56/0.98    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.56/0.98    inference(negated_conjecture,[],[f19])).
% 3.56/0.98  
% 3.56/0.98  fof(f27,plain,(
% 3.56/0.98    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.56/0.98    inference(ennf_transformation,[],[f20])).
% 3.56/0.98  
% 3.56/0.98  fof(f37,plain,(
% 3.56/0.98    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)))),
% 3.56/0.98    introduced(choice_axiom,[])).
% 3.56/0.98  
% 3.56/0.98  fof(f38,plain,(
% 3.56/0.98    sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 3.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f27,f37])).
% 3.56/0.98  
% 3.56/0.98  fof(f65,plain,(
% 3.56/0.98    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 3.56/0.98    inference(cnf_transformation,[],[f38])).
% 3.56/0.98  
% 3.56/0.98  fof(f13,axiom,(
% 3.56/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f59,plain,(
% 3.56/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f13])).
% 3.56/0.98  
% 3.56/0.98  fof(f70,plain,(
% 3.56/0.98    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f59,f69])).
% 3.56/0.98  
% 3.56/0.98  fof(f14,axiom,(
% 3.56/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f60,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f14])).
% 3.56/0.98  
% 3.56/0.98  fof(f69,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f60,f68])).
% 3.56/0.98  
% 3.56/0.98  fof(f87,plain,(
% 3.56/0.98    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))),
% 3.56/0.98    inference(definition_unfolding,[],[f65,f70,f69])).
% 3.56/0.98  
% 3.56/0.98  fof(f5,axiom,(
% 3.56/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f25,plain,(
% 3.56/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.56/0.98    inference(ennf_transformation,[],[f5])).
% 3.56/0.98  
% 3.56/0.98  fof(f44,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f25])).
% 3.56/0.98  
% 3.56/0.98  fof(f76,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f44,f45])).
% 3.56/0.98  
% 3.56/0.98  fof(f1,axiom,(
% 3.56/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f21,plain,(
% 3.56/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.56/0.98    inference(rectify,[],[f1])).
% 3.56/0.98  
% 3.56/0.98  fof(f39,plain,(
% 3.56/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.56/0.98    inference(cnf_transformation,[],[f21])).
% 3.56/0.98  
% 3.56/0.98  fof(f73,plain,(
% 3.56/0.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.56/0.98    inference(definition_unfolding,[],[f39,f45])).
% 3.56/0.98  
% 3.56/0.98  fof(f12,axiom,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f58,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f12])).
% 3.56/0.98  
% 3.56/0.98  fof(f9,axiom,(
% 3.56/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f48,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f9])).
% 3.56/0.98  
% 3.56/0.98  fof(f72,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f58,f48,f62,f70])).
% 3.56/0.98  
% 3.56/0.98  fof(f10,axiom,(
% 3.56/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f26,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.56/0.98    inference(ennf_transformation,[],[f10])).
% 3.56/0.98  
% 3.56/0.98  fof(f32,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.56/0.98    inference(nnf_transformation,[],[f26])).
% 3.56/0.98  
% 3.56/0.98  fof(f33,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.56/0.98    inference(flattening,[],[f32])).
% 3.56/0.98  
% 3.56/0.98  fof(f34,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.56/0.98    inference(rectify,[],[f33])).
% 3.56/0.98  
% 3.56/0.98  fof(f35,plain,(
% 3.56/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.56/0.98    introduced(choice_axiom,[])).
% 3.56/0.98  
% 3.56/0.98  fof(f36,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 3.56/0.98  
% 3.56/0.98  fof(f52,plain,(
% 3.56/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.56/0.98    inference(cnf_transformation,[],[f36])).
% 3.56/0.98  
% 3.56/0.98  fof(f81,plain,(
% 3.56/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.56/0.98    inference(definition_unfolding,[],[f52,f68])).
% 3.56/0.98  
% 3.56/0.98  fof(f88,plain,(
% 3.56/0.98    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 3.56/0.98    inference(equality_resolution,[],[f81])).
% 3.56/0.98  
% 3.56/0.98  fof(f89,plain,(
% 3.56/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 3.56/0.98    inference(equality_resolution,[],[f88])).
% 3.56/0.98  
% 3.56/0.98  fof(f49,plain,(
% 3.56/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.56/0.98    inference(cnf_transformation,[],[f36])).
% 3.56/0.98  
% 3.56/0.98  fof(f84,plain,(
% 3.56/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.56/0.98    inference(definition_unfolding,[],[f49,f68])).
% 3.56/0.98  
% 3.56/0.98  fof(f94,plain,(
% 3.56/0.98    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 3.56/0.98    inference(equality_resolution,[],[f84])).
% 3.56/0.98  
% 3.56/0.98  fof(f67,plain,(
% 3.56/0.98    sK3 != sK5),
% 3.56/0.98    inference(cnf_transformation,[],[f38])).
% 3.56/0.98  
% 3.56/0.98  fof(f66,plain,(
% 3.56/0.98    sK3 != sK4),
% 3.56/0.98    inference(cnf_transformation,[],[f38])).
% 3.56/0.98  
% 3.56/0.98  cnf(c_8,plain,
% 3.56/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.56/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_394,plain,
% 3.56/0.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_5,plain,
% 3.56/0.98      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.56/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_396,plain,
% 3.56/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3,plain,
% 3.56/0.98      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.56/0.98      | ~ r1_xboole_0(X1,X2) ),
% 3.56/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_398,plain,
% 3.56/0.98      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.56/0.98      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_2568,plain,
% 3.56/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.56/0.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_396,c_398]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3273,plain,
% 3.56/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_394,c_2568]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_0,plain,
% 3.56/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.56/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_4474,plain,
% 3.56/0.98      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_3273,c_0]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_7,plain,
% 3.56/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.56/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_4486,plain,
% 3.56/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.56/0.98      inference(light_normalisation,[status(thm)],[c_4474,c_7]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_4487,plain,
% 3.56/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.56/0.98      inference(demodulation,[status(thm)],[c_4486,c_3273]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_17,plain,
% 3.56/0.98      ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
% 3.56/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_21,negated_conjecture,
% 3.56/0.98      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 3.56/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_385,plain,
% 3.56/0.98      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_988,plain,
% 3.56/0.98      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4)) = iProver_top ),
% 3.56/0.98      inference(demodulation,[status(thm)],[c_17,c_385]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_6,plain,
% 3.56/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.56/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_395,plain,
% 3.56/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.56/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1755,plain,
% 3.56/0.98      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_988,c_395]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1758,plain,
% 3.56/0.98      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4)) ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1755,c_0]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_2,plain,
% 3.56/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.56/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_902,plain,
% 3.56/0.98      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1760,plain,
% 3.56/0.98      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 3.56/0.98      inference(demodulation,[status(thm)],[c_1758,c_902]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_5730,plain,
% 3.56/0.98      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK5,sK5,sK5,sK4,sK4)) = k1_xboole_0 ),
% 3.56/0.98      inference(demodulation,[status(thm)],[c_4487,c_1760]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1,plain,
% 3.56/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 3.56/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1287,plain,
% 3.56/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X0,X0,X0,X1,X2))) = k3_enumset1(X2,X2,X1,X0,X3) ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_17,c_1]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_5759,plain,
% 3.56/0.98      ( k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK4,sK4),k1_xboole_0) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_5730,c_1287]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_5761,plain,
% 3.56/0.98      ( k3_enumset1(sK4,sK4,sK4,sK5,sK3) = k3_enumset1(sK5,sK5,sK5,sK4,sK4) ),
% 3.56/0.98      inference(demodulation,[status(thm)],[c_5759,c_7]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_13,plain,
% 3.56/0.98      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
% 3.56/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_389,plain,
% 3.56/0.98      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_5885,plain,
% 3.56/0.98      ( r2_hidden(sK3,k3_enumset1(sK5,sK5,sK5,sK4,sK4)) = iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_5761,c_389]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_16,plain,
% 3.56/0.98      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 3.56/0.98      | X0 = X1
% 3.56/0.98      | X0 = X2
% 3.56/0.98      | X0 = X3 ),
% 3.56/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_547,plain,
% 3.56/0.98      ( ~ r2_hidden(sK3,k3_enumset1(X0,X0,X0,X1,sK4))
% 3.56/0.98      | sK3 = X0
% 3.56/0.98      | sK3 = X1
% 3.56/0.98      | sK3 = sK4 ),
% 3.56/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1348,plain,
% 3.56/0.98      ( ~ r2_hidden(sK3,k3_enumset1(X0,X0,X0,sK4,sK4))
% 3.56/0.98      | sK3 = X0
% 3.56/0.98      | sK3 = sK4 ),
% 3.56/0.98      inference(instantiation,[status(thm)],[c_547]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_6014,plain,
% 3.56/0.98      ( ~ r2_hidden(sK3,k3_enumset1(sK5,sK5,sK5,sK4,sK4))
% 3.56/0.98      | sK3 = sK4
% 3.56/0.98      | sK3 = sK5 ),
% 3.56/0.98      inference(instantiation,[status(thm)],[c_1348]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_6015,plain,
% 3.56/0.98      ( sK3 = sK4
% 3.56/0.98      | sK3 = sK5
% 3.56/0.98      | r2_hidden(sK3,k3_enumset1(sK5,sK5,sK5,sK4,sK4)) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_6014]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_19,negated_conjecture,
% 3.56/0.98      ( sK3 != sK5 ),
% 3.56/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_20,negated_conjecture,
% 3.56/0.98      ( sK3 != sK4 ),
% 3.56/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(contradiction,plain,
% 3.56/0.98      ( $false ),
% 3.56/0.98      inference(minisat,[status(thm)],[c_5885,c_6015,c_19,c_20]) ).
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  ------                               Statistics
% 3.56/0.98  
% 3.56/0.98  ------ Selected
% 3.56/0.98  
% 3.56/0.98  total_time:                             0.302
% 3.56/0.98  
%------------------------------------------------------------------------------
