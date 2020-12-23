%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:32 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 482 expanded)
%              Number of clauses        :   32 (  93 expanded)
%              Number of leaves         :   13 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  328 (2893 expanded)
%              Number of equality atoms :  168 (1113 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK4,sK3)
        | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3 )
      & ( ~ r2_hidden(sK4,sK3)
        | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3 ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( r2_hidden(sK4,sK3)
      | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3 )
    & ( ~ r2_hidden(sK4,sK3)
      | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f43])).

fof(f81,plain,
    ( r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3 ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f82])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f75,f83])).

fof(f103,plain,
    ( r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK3 ),
    inference(definition_unfolding,[],[f81,f84])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,
    ( ~ r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3 ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,
    ( ~ r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(definition_unfolding,[],[f80,f84])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f22])).

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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f119,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f117,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f100])).

fof(f118,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f117])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3145,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | r2_hidden(sK4,sK3) ),
    inference(resolution,[status(thm)],[c_10,c_30])).

cnf(c_5392,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_8,c_3145])).

cnf(c_1583,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1614,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5407,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5392,c_1583,c_1614])).

cnf(c_9,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5644,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_5407,c_9])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_38,plain,
    ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_27,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_41,plain,
    ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_633,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1899,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_637,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1578,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4,sK3)
    | sK3 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1898,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK4,sK3)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_2526,plain,
    ( ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | r2_hidden(sK4,sK3)
    | sK3 != sK3
    | sK4 != sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1898])).

cnf(c_634,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2983,plain,
    ( X0 != X1
    | X0 = sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3)
    | sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_2984,plain,
    ( sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) != sK4
    | sK4 = sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2983])).

cnf(c_5646,plain,
    ( sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) = sK4
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_5407,c_28])).

cnf(c_5648,plain,
    ( k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5644,c_31,c_38,c_41,c_1583,c_1899,c_2526,c_2984,c_5646])).

cnf(c_5663,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
    | ~ r2_hidden(X1,sK3)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_5648,c_637])).

cnf(c_6793,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_5663,c_633])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_7414,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_6793,c_12])).

cnf(c_7416,plain,
    ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_7414])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7416,c_5648,c_41,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:49:19 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.38/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/0.97  
% 3.38/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.38/0.97  
% 3.38/0.97  ------  iProver source info
% 3.38/0.97  
% 3.38/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.38/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.38/0.97  git: non_committed_changes: false
% 3.38/0.97  git: last_make_outside_of_git: false
% 3.38/0.97  
% 3.38/0.97  ------ 
% 3.38/0.97  ------ Parsing...
% 3.38/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.38/0.97  
% 3.38/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.38/0.97  
% 3.38/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.38/0.97  
% 3.38/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.38/0.97  ------ Proving...
% 3.38/0.97  ------ Problem Properties 
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  clauses                                 31
% 3.38/0.97  conjectures                             2
% 3.38/0.97  EPR                                     2
% 3.38/0.97  Horn                                    22
% 3.38/0.97  unary                                   8
% 3.38/0.97  binary                                  9
% 3.38/0.97  lits                                    73
% 3.38/0.97  lits eq                                 28
% 3.38/0.97  fd_pure                                 0
% 3.38/0.97  fd_pseudo                               0
% 3.38/0.97  fd_cond                                 0
% 3.38/0.97  fd_pseudo_cond                          11
% 3.38/0.97  AC symbols                              0
% 3.38/0.97  
% 3.38/0.97  ------ Input Options Time Limit: Unbounded
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  ------ 
% 3.38/0.97  Current options:
% 3.38/0.97  ------ 
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  ------ Proving...
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  % SZS status Theorem for theBenchmark.p
% 3.38/0.97  
% 3.38/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.38/0.97  
% 3.38/0.97  fof(f3,axiom,(
% 3.38/0.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.38/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.97  
% 3.38/0.97  fof(f30,plain,(
% 3.38/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.38/0.97    inference(nnf_transformation,[],[f3])).
% 3.38/0.97  
% 3.38/0.97  fof(f31,plain,(
% 3.38/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.38/0.97    inference(flattening,[],[f30])).
% 3.38/0.97  
% 3.38/0.97  fof(f32,plain,(
% 3.38/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.38/0.97    inference(rectify,[],[f31])).
% 3.38/0.97  
% 3.38/0.97  fof(f33,plain,(
% 3.38/0.97    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.38/0.97    introduced(choice_axiom,[])).
% 3.38/0.97  
% 3.38/0.97  fof(f34,plain,(
% 3.38/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.38/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 3.38/0.97  
% 3.38/0.97  fof(f57,plain,(
% 3.38/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.38/0.97    inference(cnf_transformation,[],[f34])).
% 3.38/0.97  
% 3.38/0.97  fof(f55,plain,(
% 3.38/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.38/0.97    inference(cnf_transformation,[],[f34])).
% 3.38/0.97  
% 3.38/0.97  fof(f17,conjecture,(
% 3.38/0.97    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.38/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.97  
% 3.38/0.97  fof(f18,negated_conjecture,(
% 3.38/0.97    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.38/0.97    inference(negated_conjecture,[],[f17])).
% 3.38/0.97  
% 3.38/0.97  fof(f24,plain,(
% 3.38/0.97    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.38/0.97    inference(ennf_transformation,[],[f18])).
% 3.38/0.97  
% 3.38/0.97  fof(f42,plain,(
% 3.38/0.97    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.38/0.97    inference(nnf_transformation,[],[f24])).
% 3.38/0.97  
% 3.38/0.97  fof(f43,plain,(
% 3.38/0.97    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3) & (~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3))),
% 3.38/0.97    introduced(choice_axiom,[])).
% 3.38/0.97  
% 3.38/0.97  fof(f44,plain,(
% 3.38/0.97    (r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3) & (~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3)),
% 3.38/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f43])).
% 3.38/0.97  
% 3.38/0.97  fof(f81,plain,(
% 3.38/0.97    r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3),
% 3.38/0.97    inference(cnf_transformation,[],[f44])).
% 3.38/0.97  
% 3.38/0.97  fof(f12,axiom,(
% 3.38/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.38/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.97  
% 3.38/0.97  fof(f75,plain,(
% 3.38/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.38/0.97    inference(cnf_transformation,[],[f12])).
% 3.38/0.97  
% 3.38/0.97  fof(f13,axiom,(
% 3.38/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.38/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.97  
% 3.38/0.97  fof(f76,plain,(
% 3.38/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.38/0.97    inference(cnf_transformation,[],[f13])).
% 3.38/0.97  
% 3.38/0.97  fof(f14,axiom,(
% 3.38/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.38/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.97  
% 3.38/0.97  fof(f77,plain,(
% 3.38/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.38/0.97    inference(cnf_transformation,[],[f14])).
% 3.38/0.97  
% 3.38/0.97  fof(f15,axiom,(
% 3.38/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.38/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.97  
% 3.38/0.97  fof(f78,plain,(
% 3.38/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.38/0.97    inference(cnf_transformation,[],[f15])).
% 3.38/0.97  
% 3.38/0.97  fof(f82,plain,(
% 3.38/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.38/0.97    inference(definition_unfolding,[],[f77,f78])).
% 3.38/0.97  
% 3.38/0.97  fof(f83,plain,(
% 3.38/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.38/0.97    inference(definition_unfolding,[],[f76,f82])).
% 3.38/0.97  
% 3.38/0.97  fof(f84,plain,(
% 3.38/0.97    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.38/0.97    inference(definition_unfolding,[],[f75,f83])).
% 3.38/0.97  
% 3.38/0.97  fof(f103,plain,(
% 3.38/0.97    r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK3),
% 3.38/0.97    inference(definition_unfolding,[],[f81,f84])).
% 3.38/0.97  
% 3.38/0.97  fof(f56,plain,(
% 3.38/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.38/0.97    inference(cnf_transformation,[],[f34])).
% 3.38/0.97  
% 3.38/0.97  fof(f80,plain,(
% 3.38/0.97    ~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3),
% 3.38/0.97    inference(cnf_transformation,[],[f44])).
% 3.38/0.97  
% 3.38/0.97  fof(f104,plain,(
% 3.38/0.97    ~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3),
% 3.38/0.97    inference(definition_unfolding,[],[f80,f84])).
% 3.38/0.97  
% 3.38/0.97  fof(f11,axiom,(
% 3.38/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.38/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.97  
% 3.38/0.97  fof(f22,plain,(
% 3.38/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.38/0.97    inference(ennf_transformation,[],[f11])).
% 3.38/0.97  
% 3.38/0.97  fof(f37,plain,(
% 3.38/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/0.97    inference(nnf_transformation,[],[f22])).
% 3.38/0.97  
% 3.38/0.97  fof(f38,plain,(
% 3.38/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/0.97    inference(flattening,[],[f37])).
% 3.38/0.97  
% 3.38/0.97  fof(f39,plain,(
% 3.38/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/0.97    inference(rectify,[],[f38])).
% 3.38/0.97  
% 3.38/0.97  fof(f40,plain,(
% 3.38/0.97    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.38/0.97    introduced(choice_axiom,[])).
% 3.38/0.97  
% 3.38/0.97  fof(f41,plain,(
% 3.38/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 3.38/0.97  
% 3.38/0.97  fof(f67,plain,(
% 3.38/0.97    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.38/0.97    inference(cnf_transformation,[],[f41])).
% 3.38/0.97  
% 3.38/0.97  fof(f101,plain,(
% 3.38/0.97    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.38/0.97    inference(definition_unfolding,[],[f67,f82])).
% 3.38/0.97  
% 3.38/0.97  fof(f119,plain,(
% 3.38/0.97    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 3.38/0.97    inference(equality_resolution,[],[f101])).
% 3.38/0.97  
% 3.38/0.97  fof(f68,plain,(
% 3.38/0.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.38/0.97    inference(cnf_transformation,[],[f41])).
% 3.38/0.97  
% 3.38/0.97  fof(f100,plain,(
% 3.38/0.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.38/0.97    inference(definition_unfolding,[],[f68,f82])).
% 3.38/0.97  
% 3.38/0.97  fof(f117,plain,(
% 3.38/0.97    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 3.38/0.97    inference(equality_resolution,[],[f100])).
% 3.38/0.97  
% 3.38/0.97  fof(f118,plain,(
% 3.38/0.97    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 3.38/0.97    inference(equality_resolution,[],[f117])).
% 3.38/0.97  
% 3.38/0.97  fof(f53,plain,(
% 3.38/0.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.38/0.97    inference(cnf_transformation,[],[f34])).
% 3.38/0.97  
% 3.38/0.97  fof(f109,plain,(
% 3.38/0.97    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.38/0.97    inference(equality_resolution,[],[f53])).
% 3.38/0.97  
% 3.38/0.97  cnf(c_8,plain,
% 3.38/0.97      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 3.38/0.97      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.38/0.97      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.38/0.97      | k4_xboole_0(X0,X1) = X2 ),
% 3.38/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_10,plain,
% 3.38/0.97      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.38/0.97      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.38/0.97      | k4_xboole_0(X0,X1) = X2 ),
% 3.38/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_30,negated_conjecture,
% 3.38/0.97      ( r2_hidden(sK4,sK3)
% 3.38/0.97      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK3 ),
% 3.38/0.97      inference(cnf_transformation,[],[f103]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_3145,plain,
% 3.38/0.97      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.38/0.97      | r2_hidden(sK4,sK3) ),
% 3.38/0.97      inference(resolution,[status(thm)],[c_10,c_30]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_5392,plain,
% 3.38/0.97      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.38/0.97      | ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.38/0.97      | r2_hidden(sK4,sK3)
% 3.38/0.97      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.38/0.97      inference(resolution,[status(thm)],[c_8,c_3145]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_1583,plain,
% 3.38/0.97      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.38/0.97      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_1614,plain,
% 3.38/0.97      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.38/0.97      | ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.38/0.97      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_5407,plain,
% 3.38/0.97      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.38/0.97      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.38/0.97      inference(global_propositional_subsumption,
% 3.38/0.97                [status(thm)],
% 3.38/0.97                [c_5392,c_1583,c_1614]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_9,plain,
% 3.38/0.97      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 3.38/0.97      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.38/0.97      | k4_xboole_0(X0,X1) = X2 ),
% 3.38/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_5644,plain,
% 3.38/0.97      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.38/0.97      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.38/0.97      inference(resolution,[status(thm)],[c_5407,c_9]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_31,negated_conjecture,
% 3.38/0.97      ( ~ r2_hidden(sK4,sK3)
% 3.38/0.97      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.38/0.97      inference(cnf_transformation,[],[f104]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_28,plain,
% 3.38/0.97      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 3.38/0.97      | X0 = X1
% 3.38/0.97      | X0 = X2
% 3.38/0.97      | X0 = X3 ),
% 3.38/0.97      inference(cnf_transformation,[],[f119]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_38,plain,
% 3.38/0.97      ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_28]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_27,plain,
% 3.38/0.97      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 3.38/0.97      inference(cnf_transformation,[],[f118]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_41,plain,
% 3.38/0.97      ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_27]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_633,plain,( X0 = X0 ),theory(equality) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_1899,plain,
% 3.38/0.97      ( sK3 = sK3 ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_633]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_637,plain,
% 3.38/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.38/0.97      theory(equality) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_1578,plain,
% 3.38/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(sK4,sK3) | sK3 != X1 | sK4 != X0 ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_637]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_1898,plain,
% 3.38/0.97      ( ~ r2_hidden(X0,sK3)
% 3.38/0.97      | r2_hidden(sK4,sK3)
% 3.38/0.97      | sK3 != sK3
% 3.38/0.97      | sK4 != X0 ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_1578]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_2526,plain,
% 3.38/0.97      ( ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.38/0.97      | r2_hidden(sK4,sK3)
% 3.38/0.97      | sK3 != sK3
% 3.38/0.97      | sK4 != sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_1898]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_634,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_2983,plain,
% 3.38/0.97      ( X0 != X1
% 3.38/0.97      | X0 = sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3)
% 3.38/0.97      | sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) != X1 ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_634]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_2984,plain,
% 3.38/0.97      ( sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) != sK4
% 3.38/0.97      | sK4 = sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3)
% 3.38/0.97      | sK4 != sK4 ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_2983]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_5646,plain,
% 3.38/0.97      ( sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) = sK4
% 3.38/0.97      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.38/0.97      inference(resolution,[status(thm)],[c_5407,c_28]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_5648,plain,
% 3.38/0.97      ( k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.38/0.97      inference(global_propositional_subsumption,
% 3.38/0.97                [status(thm)],
% 3.38/0.97                [c_5644,c_31,c_38,c_41,c_1583,c_1899,c_2526,c_2984,
% 3.38/0.97                 c_5646]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_5663,plain,
% 3.38/0.97      ( r2_hidden(X0,k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
% 3.38/0.97      | ~ r2_hidden(X1,sK3)
% 3.38/0.97      | X0 != X1 ),
% 3.38/0.97      inference(resolution,[status(thm)],[c_5648,c_637]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_6793,plain,
% 3.38/0.97      ( r2_hidden(X0,k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
% 3.38/0.97      | ~ r2_hidden(X0,sK3) ),
% 3.38/0.97      inference(resolution,[status(thm)],[c_5663,c_633]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_12,plain,
% 3.38/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.38/0.97      inference(cnf_transformation,[],[f109]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_7414,plain,
% 3.38/0.97      ( ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.38/0.97      | ~ r2_hidden(X0,sK3) ),
% 3.38/0.97      inference(resolution,[status(thm)],[c_6793,c_12]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(c_7416,plain,
% 3.38/0.97      ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.38/0.97      | ~ r2_hidden(sK4,sK3) ),
% 3.38/0.97      inference(instantiation,[status(thm)],[c_7414]) ).
% 3.38/0.97  
% 3.38/0.97  cnf(contradiction,plain,
% 3.38/0.97      ( $false ),
% 3.38/0.97      inference(minisat,[status(thm)],[c_7416,c_5648,c_41,c_30]) ).
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.38/0.97  
% 3.38/0.97  ------                               Statistics
% 3.38/0.97  
% 3.38/0.97  ------ Selected
% 3.38/0.97  
% 3.38/0.97  total_time:                             0.223
% 3.38/0.97  
%------------------------------------------------------------------------------
