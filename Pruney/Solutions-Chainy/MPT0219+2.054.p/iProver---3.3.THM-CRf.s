%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:18 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 213 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :   16 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  234 ( 458 expanded)
%              Number of equality atoms :  177 ( 363 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f31,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK4 != sK5
      & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( sK4 != sK5
    & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f45])).

fof(f79,plain,(
    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f59,f53])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f82])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f83])).

fof(f85,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f103,plain,(
    k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f79,f81,f86,f86,f86])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f72,f81,f78,f86])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f63,f84])).

fof(f104,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f95])).

fof(f105,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f104])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f113,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f86])).

fof(f111,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f101])).

fof(f112,plain,(
    ! [X3] : r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f111])).

fof(f80,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_25,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_936,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_25,c_0])).

cnf(c_16,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_481,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9093,plain,
    ( r2_hidden(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_481])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_721,plain,
    ( ~ r2_hidden(sK5,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_722,plain,
    ( sK5 = X0
    | r2_hidden(sK5,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_724,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_180,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_649,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_650,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_22,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_30,plain,
    ( r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_27,plain,
    ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9093,c_724,c_650,c_30,c_27,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:26:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.71/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/0.99  
% 3.71/0.99  ------  iProver source info
% 3.71/0.99  
% 3.71/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.71/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/0.99  git: non_committed_changes: false
% 3.71/0.99  git: last_make_outside_of_git: false
% 3.71/0.99  
% 3.71/0.99  ------ 
% 3.71/0.99  
% 3.71/0.99  ------ Input Options
% 3.71/0.99  
% 3.71/0.99  --out_options                           all
% 3.71/0.99  --tptp_safe_out                         true
% 3.71/0.99  --problem_path                          ""
% 3.71/0.99  --include_path                          ""
% 3.71/0.99  --clausifier                            res/vclausify_rel
% 3.71/0.99  --clausifier_options                    --mode clausify
% 3.71/0.99  --stdin                                 false
% 3.71/0.99  --stats_out                             sel
% 3.71/0.99  
% 3.71/0.99  ------ General Options
% 3.71/0.99  
% 3.71/0.99  --fof                                   false
% 3.71/0.99  --time_out_real                         604.99
% 3.71/0.99  --time_out_virtual                      -1.
% 3.71/0.99  --symbol_type_check                     false
% 3.71/0.99  --clausify_out                          false
% 3.71/0.99  --sig_cnt_out                           false
% 3.71/0.99  --trig_cnt_out                          false
% 3.71/0.99  --trig_cnt_out_tolerance                1.
% 3.71/0.99  --trig_cnt_out_sk_spl                   false
% 3.71/0.99  --abstr_cl_out                          false
% 3.71/0.99  
% 3.71/0.99  ------ Global Options
% 3.71/0.99  
% 3.71/0.99  --schedule                              none
% 3.71/0.99  --add_important_lit                     false
% 3.71/0.99  --prop_solver_per_cl                    1000
% 3.71/0.99  --min_unsat_core                        false
% 3.71/0.99  --soft_assumptions                      false
% 3.71/0.99  --soft_lemma_size                       3
% 3.71/0.99  --prop_impl_unit_size                   0
% 3.71/0.99  --prop_impl_unit                        []
% 3.71/0.99  --share_sel_clauses                     true
% 3.71/0.99  --reset_solvers                         false
% 3.71/0.99  --bc_imp_inh                            [conj_cone]
% 3.71/0.99  --conj_cone_tolerance                   3.
% 3.71/0.99  --extra_neg_conj                        none
% 3.71/0.99  --large_theory_mode                     true
% 3.71/0.99  --prolific_symb_bound                   200
% 3.71/0.99  --lt_threshold                          2000
% 3.71/0.99  --clause_weak_htbl                      true
% 3.71/0.99  --gc_record_bc_elim                     false
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing Options
% 3.71/0.99  
% 3.71/0.99  --preprocessing_flag                    true
% 3.71/0.99  --time_out_prep_mult                    0.1
% 3.71/0.99  --splitting_mode                        input
% 3.71/0.99  --splitting_grd                         true
% 3.71/0.99  --splitting_cvd                         false
% 3.71/0.99  --splitting_cvd_svl                     false
% 3.71/0.99  --splitting_nvd                         32
% 3.71/0.99  --sub_typing                            true
% 3.71/0.99  --prep_gs_sim                           false
% 3.71/0.99  --prep_unflatten                        true
% 3.71/0.99  --prep_res_sim                          true
% 3.71/0.99  --prep_upred                            true
% 3.71/0.99  --prep_sem_filter                       exhaustive
% 3.71/0.99  --prep_sem_filter_out                   false
% 3.71/0.99  --pred_elim                             false
% 3.71/0.99  --res_sim_input                         true
% 3.71/0.99  --eq_ax_congr_red                       true
% 3.71/0.99  --pure_diseq_elim                       true
% 3.71/0.99  --brand_transform                       false
% 3.71/0.99  --non_eq_to_eq                          false
% 3.71/0.99  --prep_def_merge                        true
% 3.71/0.99  --prep_def_merge_prop_impl              false
% 3.71/0.99  --prep_def_merge_mbd                    true
% 3.71/0.99  --prep_def_merge_tr_red                 false
% 3.71/0.99  --prep_def_merge_tr_cl                  false
% 3.71/0.99  --smt_preprocessing                     true
% 3.71/0.99  --smt_ac_axioms                         fast
% 3.71/0.99  --preprocessed_out                      false
% 3.71/0.99  --preprocessed_stats                    false
% 3.71/0.99  
% 3.71/0.99  ------ Abstraction refinement Options
% 3.71/0.99  
% 3.71/0.99  --abstr_ref                             []
% 3.71/0.99  --abstr_ref_prep                        false
% 3.71/0.99  --abstr_ref_until_sat                   false
% 3.71/0.99  --abstr_ref_sig_restrict                funpre
% 3.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.99  --abstr_ref_under                       []
% 3.71/0.99  
% 3.71/0.99  ------ SAT Options
% 3.71/0.99  
% 3.71/0.99  --sat_mode                              false
% 3.71/0.99  --sat_fm_restart_options                ""
% 3.71/0.99  --sat_gr_def                            false
% 3.71/0.99  --sat_epr_types                         true
% 3.71/0.99  --sat_non_cyclic_types                  false
% 3.71/0.99  --sat_finite_models                     false
% 3.71/0.99  --sat_fm_lemmas                         false
% 3.71/0.99  --sat_fm_prep                           false
% 3.71/0.99  --sat_fm_uc_incr                        true
% 3.71/0.99  --sat_out_model                         small
% 3.71/0.99  --sat_out_clauses                       false
% 3.71/0.99  
% 3.71/0.99  ------ QBF Options
% 3.71/0.99  
% 3.71/0.99  --qbf_mode                              false
% 3.71/0.99  --qbf_elim_univ                         false
% 3.71/0.99  --qbf_dom_inst                          none
% 3.71/0.99  --qbf_dom_pre_inst                      false
% 3.71/0.99  --qbf_sk_in                             false
% 3.71/0.99  --qbf_pred_elim                         true
% 3.71/0.99  --qbf_split                             512
% 3.71/0.99  
% 3.71/0.99  ------ BMC1 Options
% 3.71/0.99  
% 3.71/0.99  --bmc1_incremental                      false
% 3.71/0.99  --bmc1_axioms                           reachable_all
% 3.71/0.99  --bmc1_min_bound                        0
% 3.71/0.99  --bmc1_max_bound                        -1
% 3.71/0.99  --bmc1_max_bound_default                -1
% 3.71/0.99  --bmc1_symbol_reachability              true
% 3.71/0.99  --bmc1_property_lemmas                  false
% 3.71/0.99  --bmc1_k_induction                      false
% 3.71/0.99  --bmc1_non_equiv_states                 false
% 3.71/0.99  --bmc1_deadlock                         false
% 3.71/0.99  --bmc1_ucm                              false
% 3.71/0.99  --bmc1_add_unsat_core                   none
% 3.71/0.99  --bmc1_unsat_core_children              false
% 3.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.99  --bmc1_out_stat                         full
% 3.71/0.99  --bmc1_ground_init                      false
% 3.71/0.99  --bmc1_pre_inst_next_state              false
% 3.71/0.99  --bmc1_pre_inst_state                   false
% 3.71/0.99  --bmc1_pre_inst_reach_state             false
% 3.71/0.99  --bmc1_out_unsat_core                   false
% 3.71/0.99  --bmc1_aig_witness_out                  false
% 3.71/0.99  --bmc1_verbose                          false
% 3.71/0.99  --bmc1_dump_clauses_tptp                false
% 3.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.99  --bmc1_dump_file                        -
% 3.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.99  --bmc1_ucm_extend_mode                  1
% 3.71/0.99  --bmc1_ucm_init_mode                    2
% 3.71/0.99  --bmc1_ucm_cone_mode                    none
% 3.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.99  --bmc1_ucm_relax_model                  4
% 3.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.99  --bmc1_ucm_layered_model                none
% 3.71/0.99  --bmc1_ucm_max_lemma_size               10
% 3.71/0.99  
% 3.71/0.99  ------ AIG Options
% 3.71/0.99  
% 3.71/0.99  --aig_mode                              false
% 3.71/0.99  
% 3.71/0.99  ------ Instantiation Options
% 3.71/0.99  
% 3.71/0.99  --instantiation_flag                    true
% 3.71/0.99  --inst_sos_flag                         false
% 3.71/0.99  --inst_sos_phase                        true
% 3.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel_side                     num_symb
% 3.71/0.99  --inst_solver_per_active                1400
% 3.71/0.99  --inst_solver_calls_frac                1.
% 3.71/0.99  --inst_passive_queue_type               priority_queues
% 3.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.99  --inst_passive_queues_freq              [25;2]
% 3.71/0.99  --inst_dismatching                      true
% 3.71/0.99  --inst_eager_unprocessed_to_passive     true
% 3.71/0.99  --inst_prop_sim_given                   true
% 3.71/0.99  --inst_prop_sim_new                     false
% 3.71/0.99  --inst_subs_new                         false
% 3.71/0.99  --inst_eq_res_simp                      false
% 3.71/0.99  --inst_subs_given                       false
% 3.71/0.99  --inst_orphan_elimination               true
% 3.71/0.99  --inst_learning_loop_flag               true
% 3.71/0.99  --inst_learning_start                   3000
% 3.71/0.99  --inst_learning_factor                  2
% 3.71/0.99  --inst_start_prop_sim_after_learn       3
% 3.71/0.99  --inst_sel_renew                        solver
% 3.71/0.99  --inst_lit_activity_flag                true
% 3.71/0.99  --inst_restr_to_given                   false
% 3.71/0.99  --inst_activity_threshold               500
% 3.71/0.99  --inst_out_proof                        true
% 3.71/0.99  
% 3.71/0.99  ------ Resolution Options
% 3.71/0.99  
% 3.71/0.99  --resolution_flag                       true
% 3.71/0.99  --res_lit_sel                           adaptive
% 3.71/0.99  --res_lit_sel_side                      none
% 3.71/0.99  --res_ordering                          kbo
% 3.71/0.99  --res_to_prop_solver                    active
% 3.71/0.99  --res_prop_simpl_new                    false
% 3.71/0.99  --res_prop_simpl_given                  true
% 3.71/0.99  --res_passive_queue_type                priority_queues
% 3.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.99  --res_passive_queues_freq               [15;5]
% 3.71/0.99  --res_forward_subs                      full
% 3.71/0.99  --res_backward_subs                     full
% 3.71/0.99  --res_forward_subs_resolution           true
% 3.71/0.99  --res_backward_subs_resolution          true
% 3.71/0.99  --res_orphan_elimination                true
% 3.71/0.99  --res_time_limit                        2.
% 3.71/0.99  --res_out_proof                         true
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Options
% 3.71/0.99  
% 3.71/0.99  --superposition_flag                    true
% 3.71/0.99  --sup_passive_queue_type                priority_queues
% 3.71/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.99  --sup_passive_queues_freq               [1;4]
% 3.71/0.99  --demod_completeness_check              fast
% 3.71/0.99  --demod_use_ground                      true
% 3.71/0.99  --sup_to_prop_solver                    passive
% 3.71/0.99  --sup_prop_simpl_new                    true
% 3.71/0.99  --sup_prop_simpl_given                  true
% 3.71/0.99  --sup_fun_splitting                     false
% 3.71/0.99  --sup_smt_interval                      50000
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Simplification Setup
% 3.71/0.99  
% 3.71/0.99  --sup_indices_passive                   []
% 3.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_full_bw                           [BwDemod]
% 3.71/0.99  --sup_immed_triv                        [TrivRules]
% 3.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_immed_bw_main                     []
% 3.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.99  
% 3.71/0.99  ------ Combination Options
% 3.71/0.99  
% 3.71/0.99  --comb_res_mult                         3
% 3.71/0.99  --comb_sup_mult                         2
% 3.71/0.99  --comb_inst_mult                        10
% 3.71/0.99  
% 3.71/0.99  ------ Debug Options
% 3.71/0.99  
% 3.71/0.99  --dbg_backtrace                         false
% 3.71/0.99  --dbg_dump_prop_clauses                 false
% 3.71/0.99  --dbg_dump_prop_clauses_file            -
% 3.71/0.99  --dbg_out_stat                          false
% 3.71/0.99  ------ Parsing...
% 3.71/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/0.99  ------ Proving...
% 3.71/0.99  ------ Problem Properties 
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  clauses                                 26
% 3.71/0.99  conjectures                             2
% 3.71/0.99  EPR                                     1
% 3.71/0.99  Horn                                    21
% 3.71/0.99  unary                                   14
% 3.71/0.99  binary                                  5
% 3.71/0.99  lits                                    48
% 3.71/0.99  lits eq                                 28
% 3.71/0.99  fd_pure                                 0
% 3.71/0.99  fd_pseudo                               0
% 3.71/0.99  fd_cond                                 1
% 3.71/0.99  fd_pseudo_cond                          6
% 3.71/0.99  AC symbols                              0
% 3.71/0.99  
% 3.71/0.99  ------ Input Options Time Limit: Unbounded
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ 
% 3.71/0.99  Current options:
% 3.71/0.99  ------ 
% 3.71/0.99  
% 3.71/0.99  ------ Input Options
% 3.71/0.99  
% 3.71/0.99  --out_options                           all
% 3.71/0.99  --tptp_safe_out                         true
% 3.71/0.99  --problem_path                          ""
% 3.71/0.99  --include_path                          ""
% 3.71/0.99  --clausifier                            res/vclausify_rel
% 3.71/0.99  --clausifier_options                    --mode clausify
% 3.71/0.99  --stdin                                 false
% 3.71/0.99  --stats_out                             sel
% 3.71/0.99  
% 3.71/0.99  ------ General Options
% 3.71/0.99  
% 3.71/0.99  --fof                                   false
% 3.71/0.99  --time_out_real                         604.99
% 3.71/0.99  --time_out_virtual                      -1.
% 3.71/0.99  --symbol_type_check                     false
% 3.71/0.99  --clausify_out                          false
% 3.71/0.99  --sig_cnt_out                           false
% 3.71/0.99  --trig_cnt_out                          false
% 3.71/0.99  --trig_cnt_out_tolerance                1.
% 3.71/0.99  --trig_cnt_out_sk_spl                   false
% 3.71/0.99  --abstr_cl_out                          false
% 3.71/0.99  
% 3.71/0.99  ------ Global Options
% 3.71/0.99  
% 3.71/0.99  --schedule                              none
% 3.71/0.99  --add_important_lit                     false
% 3.71/0.99  --prop_solver_per_cl                    1000
% 3.71/0.99  --min_unsat_core                        false
% 3.71/0.99  --soft_assumptions                      false
% 3.71/0.99  --soft_lemma_size                       3
% 3.71/0.99  --prop_impl_unit_size                   0
% 3.71/0.99  --prop_impl_unit                        []
% 3.71/0.99  --share_sel_clauses                     true
% 3.71/0.99  --reset_solvers                         false
% 3.71/0.99  --bc_imp_inh                            [conj_cone]
% 3.71/0.99  --conj_cone_tolerance                   3.
% 3.71/0.99  --extra_neg_conj                        none
% 3.71/0.99  --large_theory_mode                     true
% 3.71/0.99  --prolific_symb_bound                   200
% 3.71/0.99  --lt_threshold                          2000
% 3.71/0.99  --clause_weak_htbl                      true
% 3.71/0.99  --gc_record_bc_elim                     false
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing Options
% 3.71/0.99  
% 3.71/0.99  --preprocessing_flag                    true
% 3.71/0.99  --time_out_prep_mult                    0.1
% 3.71/0.99  --splitting_mode                        input
% 3.71/0.99  --splitting_grd                         true
% 3.71/0.99  --splitting_cvd                         false
% 3.71/0.99  --splitting_cvd_svl                     false
% 3.71/0.99  --splitting_nvd                         32
% 3.71/0.99  --sub_typing                            true
% 3.71/0.99  --prep_gs_sim                           false
% 3.71/0.99  --prep_unflatten                        true
% 3.71/0.99  --prep_res_sim                          true
% 3.71/0.99  --prep_upred                            true
% 3.71/0.99  --prep_sem_filter                       exhaustive
% 3.71/0.99  --prep_sem_filter_out                   false
% 3.71/0.99  --pred_elim                             false
% 3.71/0.99  --res_sim_input                         true
% 3.71/0.99  --eq_ax_congr_red                       true
% 3.71/0.99  --pure_diseq_elim                       true
% 3.71/0.99  --brand_transform                       false
% 3.71/0.99  --non_eq_to_eq                          false
% 3.71/0.99  --prep_def_merge                        true
% 3.71/0.99  --prep_def_merge_prop_impl              false
% 3.71/0.99  --prep_def_merge_mbd                    true
% 3.71/0.99  --prep_def_merge_tr_red                 false
% 3.71/0.99  --prep_def_merge_tr_cl                  false
% 3.71/0.99  --smt_preprocessing                     true
% 3.71/0.99  --smt_ac_axioms                         fast
% 3.71/0.99  --preprocessed_out                      false
% 3.71/0.99  --preprocessed_stats                    false
% 3.71/0.99  
% 3.71/0.99  ------ Abstraction refinement Options
% 3.71/0.99  
% 3.71/0.99  --abstr_ref                             []
% 3.71/0.99  --abstr_ref_prep                        false
% 3.71/0.99  --abstr_ref_until_sat                   false
% 3.71/0.99  --abstr_ref_sig_restrict                funpre
% 3.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.99  --abstr_ref_under                       []
% 3.71/0.99  
% 3.71/0.99  ------ SAT Options
% 3.71/0.99  
% 3.71/0.99  --sat_mode                              false
% 3.71/0.99  --sat_fm_restart_options                ""
% 3.71/0.99  --sat_gr_def                            false
% 3.71/0.99  --sat_epr_types                         true
% 3.71/0.99  --sat_non_cyclic_types                  false
% 3.71/0.99  --sat_finite_models                     false
% 3.71/0.99  --sat_fm_lemmas                         false
% 3.71/0.99  --sat_fm_prep                           false
% 3.71/0.99  --sat_fm_uc_incr                        true
% 3.71/0.99  --sat_out_model                         small
% 3.71/0.99  --sat_out_clauses                       false
% 3.71/0.99  
% 3.71/0.99  ------ QBF Options
% 3.71/0.99  
% 3.71/0.99  --qbf_mode                              false
% 3.71/0.99  --qbf_elim_univ                         false
% 3.71/0.99  --qbf_dom_inst                          none
% 3.71/0.99  --qbf_dom_pre_inst                      false
% 3.71/0.99  --qbf_sk_in                             false
% 3.71/0.99  --qbf_pred_elim                         true
% 3.71/0.99  --qbf_split                             512
% 3.71/0.99  
% 3.71/0.99  ------ BMC1 Options
% 3.71/0.99  
% 3.71/0.99  --bmc1_incremental                      false
% 3.71/0.99  --bmc1_axioms                           reachable_all
% 3.71/0.99  --bmc1_min_bound                        0
% 3.71/0.99  --bmc1_max_bound                        -1
% 3.71/0.99  --bmc1_max_bound_default                -1
% 3.71/0.99  --bmc1_symbol_reachability              true
% 3.71/0.99  --bmc1_property_lemmas                  false
% 3.71/0.99  --bmc1_k_induction                      false
% 3.71/0.99  --bmc1_non_equiv_states                 false
% 3.71/0.99  --bmc1_deadlock                         false
% 3.71/0.99  --bmc1_ucm                              false
% 3.71/0.99  --bmc1_add_unsat_core                   none
% 3.71/0.99  --bmc1_unsat_core_children              false
% 3.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.99  --bmc1_out_stat                         full
% 3.71/0.99  --bmc1_ground_init                      false
% 3.71/0.99  --bmc1_pre_inst_next_state              false
% 3.71/0.99  --bmc1_pre_inst_state                   false
% 3.71/0.99  --bmc1_pre_inst_reach_state             false
% 3.71/0.99  --bmc1_out_unsat_core                   false
% 3.71/0.99  --bmc1_aig_witness_out                  false
% 3.71/0.99  --bmc1_verbose                          false
% 3.71/0.99  --bmc1_dump_clauses_tptp                false
% 3.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.99  --bmc1_dump_file                        -
% 3.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.99  --bmc1_ucm_extend_mode                  1
% 3.71/0.99  --bmc1_ucm_init_mode                    2
% 3.71/0.99  --bmc1_ucm_cone_mode                    none
% 3.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.99  --bmc1_ucm_relax_model                  4
% 3.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.99  --bmc1_ucm_layered_model                none
% 3.71/0.99  --bmc1_ucm_max_lemma_size               10
% 3.71/0.99  
% 3.71/0.99  ------ AIG Options
% 3.71/0.99  
% 3.71/0.99  --aig_mode                              false
% 3.71/0.99  
% 3.71/0.99  ------ Instantiation Options
% 3.71/0.99  
% 3.71/0.99  --instantiation_flag                    true
% 3.71/0.99  --inst_sos_flag                         false
% 3.71/0.99  --inst_sos_phase                        true
% 3.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel_side                     num_symb
% 3.71/0.99  --inst_solver_per_active                1400
% 3.71/0.99  --inst_solver_calls_frac                1.
% 3.71/0.99  --inst_passive_queue_type               priority_queues
% 3.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.99  --inst_passive_queues_freq              [25;2]
% 3.71/0.99  --inst_dismatching                      true
% 3.71/0.99  --inst_eager_unprocessed_to_passive     true
% 3.71/0.99  --inst_prop_sim_given                   true
% 3.71/0.99  --inst_prop_sim_new                     false
% 3.71/0.99  --inst_subs_new                         false
% 3.71/0.99  --inst_eq_res_simp                      false
% 3.71/0.99  --inst_subs_given                       false
% 3.71/0.99  --inst_orphan_elimination               true
% 3.71/0.99  --inst_learning_loop_flag               true
% 3.71/0.99  --inst_learning_start                   3000
% 3.71/0.99  --inst_learning_factor                  2
% 3.71/0.99  --inst_start_prop_sim_after_learn       3
% 3.71/0.99  --inst_sel_renew                        solver
% 3.71/0.99  --inst_lit_activity_flag                true
% 3.71/0.99  --inst_restr_to_given                   false
% 3.71/0.99  --inst_activity_threshold               500
% 3.71/0.99  --inst_out_proof                        true
% 3.71/0.99  
% 3.71/0.99  ------ Resolution Options
% 3.71/0.99  
% 3.71/0.99  --resolution_flag                       true
% 3.71/0.99  --res_lit_sel                           adaptive
% 3.71/0.99  --res_lit_sel_side                      none
% 3.71/0.99  --res_ordering                          kbo
% 3.71/0.99  --res_to_prop_solver                    active
% 3.71/0.99  --res_prop_simpl_new                    false
% 3.71/0.99  --res_prop_simpl_given                  true
% 3.71/0.99  --res_passive_queue_type                priority_queues
% 3.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.99  --res_passive_queues_freq               [15;5]
% 3.71/0.99  --res_forward_subs                      full
% 3.71/0.99  --res_backward_subs                     full
% 3.71/0.99  --res_forward_subs_resolution           true
% 3.71/0.99  --res_backward_subs_resolution          true
% 3.71/0.99  --res_orphan_elimination                true
% 3.71/0.99  --res_time_limit                        2.
% 3.71/0.99  --res_out_proof                         true
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Options
% 3.71/0.99  
% 3.71/0.99  --superposition_flag                    true
% 3.71/0.99  --sup_passive_queue_type                priority_queues
% 3.71/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.99  --sup_passive_queues_freq               [1;4]
% 3.71/0.99  --demod_completeness_check              fast
% 3.71/0.99  --demod_use_ground                      true
% 3.71/0.99  --sup_to_prop_solver                    passive
% 3.71/0.99  --sup_prop_simpl_new                    true
% 3.71/0.99  --sup_prop_simpl_given                  true
% 3.71/0.99  --sup_fun_splitting                     false
% 3.71/0.99  --sup_smt_interval                      50000
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Simplification Setup
% 3.71/0.99  
% 3.71/0.99  --sup_indices_passive                   []
% 3.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_full_bw                           [BwDemod]
% 3.71/0.99  --sup_immed_triv                        [TrivRules]
% 3.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_immed_bw_main                     []
% 3.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.99  
% 3.71/0.99  ------ Combination Options
% 3.71/0.99  
% 3.71/0.99  --comb_res_mult                         3
% 3.71/0.99  --comb_sup_mult                         2
% 3.71/0.99  --comb_inst_mult                        10
% 3.71/0.99  
% 3.71/0.99  ------ Debug Options
% 3.71/0.99  
% 3.71/0.99  --dbg_backtrace                         false
% 3.71/0.99  --dbg_dump_prop_clauses                 false
% 3.71/0.99  --dbg_dump_prop_clauses_file            -
% 3.71/0.99  --dbg_out_stat                          false
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ Proving...
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  % SZS status Theorem for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  fof(f22,conjecture,(
% 3.71/0.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f23,negated_conjecture,(
% 3.71/0.99    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.71/0.99    inference(negated_conjecture,[],[f22])).
% 3.71/0.99  
% 3.71/0.99  fof(f31,plain,(
% 3.71/0.99    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.71/0.99    inference(ennf_transformation,[],[f23])).
% 3.71/0.99  
% 3.71/0.99  fof(f45,plain,(
% 3.71/0.99    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f46,plain,(
% 3.71/0.99    sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 3.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f45])).
% 3.71/0.99  
% 3.71/0.99  fof(f79,plain,(
% 3.71/0.99    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 3.71/0.99    inference(cnf_transformation,[],[f46])).
% 3.71/0.99  
% 3.71/0.99  fof(f12,axiom,(
% 3.71/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f59,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f12])).
% 3.71/0.99  
% 3.71/0.99  fof(f6,axiom,(
% 3.71/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f53,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f6])).
% 3.71/0.99  
% 3.71/0.99  fof(f81,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.71/0.99    inference(definition_unfolding,[],[f59,f53])).
% 3.71/0.99  
% 3.71/0.99  fof(f16,axiom,(
% 3.71/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f73,plain,(
% 3.71/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f16])).
% 3.71/0.99  
% 3.71/0.99  fof(f17,axiom,(
% 3.71/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f74,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f17])).
% 3.71/0.99  
% 3.71/0.99  fof(f18,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f75,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f18])).
% 3.71/0.99  
% 3.71/0.99  fof(f19,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f76,plain,(
% 3.71/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f19])).
% 3.71/0.99  
% 3.71/0.99  fof(f20,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f77,plain,(
% 3.71/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f20])).
% 3.71/0.99  
% 3.71/0.99  fof(f21,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f78,plain,(
% 3.71/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f21])).
% 3.71/0.99  
% 3.71/0.99  fof(f82,plain,(
% 3.71/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f77,f78])).
% 3.71/0.99  
% 3.71/0.99  fof(f83,plain,(
% 3.71/0.99    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f76,f82])).
% 3.71/0.99  
% 3.71/0.99  fof(f84,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f75,f83])).
% 3.71/0.99  
% 3.71/0.99  fof(f85,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f74,f84])).
% 3.71/0.99  
% 3.71/0.99  fof(f86,plain,(
% 3.71/0.99    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f73,f85])).
% 3.71/0.99  
% 3.71/0.99  fof(f103,plain,(
% 3.71/0.99    k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 3.71/0.99    inference(definition_unfolding,[],[f79,f81,f86,f86,f86])).
% 3.71/0.99  
% 3.71/0.99  fof(f15,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f72,plain,(
% 3.71/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f15])).
% 3.71/0.99  
% 3.71/0.99  fof(f87,plain,(
% 3.71/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f72,f81,f78,f86])).
% 3.71/0.99  
% 3.71/0.99  fof(f13,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f30,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.71/0.99    inference(ennf_transformation,[],[f13])).
% 3.71/0.99  
% 3.71/0.99  fof(f36,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.71/0.99    inference(nnf_transformation,[],[f30])).
% 3.71/0.99  
% 3.71/0.99  fof(f37,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.71/0.99    inference(flattening,[],[f36])).
% 3.71/0.99  
% 3.71/0.99  fof(f38,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.71/0.99    inference(rectify,[],[f37])).
% 3.71/0.99  
% 3.71/0.99  fof(f39,plain,(
% 3.71/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f40,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 3.71/0.99  
% 3.71/0.99  fof(f63,plain,(
% 3.71/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.71/0.99    inference(cnf_transformation,[],[f40])).
% 3.71/0.99  
% 3.71/0.99  fof(f95,plain,(
% 3.71/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.71/0.99    inference(definition_unfolding,[],[f63,f84])).
% 3.71/0.99  
% 3.71/0.99  fof(f104,plain,(
% 3.71/0.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 3.71/0.99    inference(equality_resolution,[],[f95])).
% 3.71/0.99  
% 3.71/0.99  fof(f105,plain,(
% 3.71/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 3.71/0.99    inference(equality_resolution,[],[f104])).
% 3.71/0.99  
% 3.71/0.99  fof(f14,axiom,(
% 3.71/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f41,plain,(
% 3.71/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.71/0.99    inference(nnf_transformation,[],[f14])).
% 3.71/0.99  
% 3.71/0.99  fof(f42,plain,(
% 3.71/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.71/0.99    inference(rectify,[],[f41])).
% 3.71/0.99  
% 3.71/0.99  fof(f43,plain,(
% 3.71/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f44,plain,(
% 3.71/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 3.71/0.99  
% 3.71/0.99  fof(f68,plain,(
% 3.71/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.71/0.99    inference(cnf_transformation,[],[f44])).
% 3.71/0.99  
% 3.71/0.99  fof(f102,plain,(
% 3.71/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.71/0.99    inference(definition_unfolding,[],[f68,f86])).
% 3.71/0.99  
% 3.71/0.99  fof(f113,plain,(
% 3.71/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 3.71/0.99    inference(equality_resolution,[],[f102])).
% 3.71/0.99  
% 3.71/0.99  fof(f69,plain,(
% 3.71/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.71/0.99    inference(cnf_transformation,[],[f44])).
% 3.71/0.99  
% 3.71/0.99  fof(f101,plain,(
% 3.71/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.71/0.99    inference(definition_unfolding,[],[f69,f86])).
% 3.71/0.99  
% 3.71/0.99  fof(f111,plain,(
% 3.71/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 3.71/0.99    inference(equality_resolution,[],[f101])).
% 3.71/0.99  
% 3.71/0.99  fof(f112,plain,(
% 3.71/0.99    ( ! [X3] : (r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) )),
% 3.71/0.99    inference(equality_resolution,[],[f111])).
% 3.71/0.99  
% 3.71/0.99  fof(f80,plain,(
% 3.71/0.99    sK4 != sK5),
% 3.71/0.99    inference(cnf_transformation,[],[f46])).
% 3.71/0.99  
% 3.71/0.99  cnf(c_25,negated_conjecture,
% 3.71/0.99      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.71/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_0,plain,
% 3.71/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.71/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_936,plain,
% 3.71/0.99      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_25,c_0]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_16,plain,
% 3.71/0.99      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 3.71/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_481,plain,
% 3.71/0.99      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9093,plain,
% 3.71/0.99      ( r2_hidden(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_936,c_481]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_23,plain,
% 3.71/0.99      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.71/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_721,plain,
% 3.71/0.99      ( ~ r2_hidden(sK5,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | sK5 = X0 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_722,plain,
% 3.71/0.99      ( sK5 = X0
% 3.71/0.99      | r2_hidden(sK5,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_724,plain,
% 3.71/0.99      ( sK5 = sK4
% 3.71/0.99      | r2_hidden(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_722]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_180,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_649,plain,
% 3.71/0.99      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_180]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_650,plain,
% 3.71/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_649]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_22,plain,
% 3.71/0.99      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
% 3.71/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_30,plain,
% 3.71/0.99      ( r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_27,plain,
% 3.71/0.99      ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.71/0.99      | sK4 = sK4 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_24,negated_conjecture,
% 3.71/0.99      ( sK4 != sK5 ),
% 3.71/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(contradiction,plain,
% 3.71/0.99      ( $false ),
% 3.71/0.99      inference(minisat,[status(thm)],[c_9093,c_724,c_650,c_30,c_27,c_24]) ).
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  ------                               Statistics
% 3.71/0.99  
% 3.71/0.99  ------ Selected
% 3.71/0.99  
% 3.71/0.99  total_time:                             0.332
% 3.71/0.99  
%------------------------------------------------------------------------------
