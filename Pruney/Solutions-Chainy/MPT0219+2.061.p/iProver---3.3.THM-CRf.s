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
% DateTime   : Thu Dec  3 11:29:19 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 267 expanded)
%              Number of clauses        :   28 (  31 expanded)
%              Number of leaves         :   17 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  258 ( 529 expanded)
%              Number of equality atoms :  186 ( 419 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f93,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f94,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f93])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f58,f45,f64,f72])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f35])).

fof(f66,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f66,f45,f72,f72,f72])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f100,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f98,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f88])).

fof(f99,plain,(
    ! [X3] : r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f98])).

fof(f67,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4918,plain,
    ( r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,sK3,X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4920,plain,
    ( r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_4918])).

cnf(c_1300,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1615,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k5_enumset1(X3,X3,X3,X3,X3,X2,X4))
    | X0 != X2
    | X1 != k5_enumset1(X3,X3,X3,X3,X3,X2,X4) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_1731,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2))
    | r2_hidden(X3,k5_enumset1(X4,X4,X4,X4,X4,X4,X4))
    | X3 != X0
    | k5_enumset1(X4,X4,X4,X4,X4,X4,X4) != k5_enumset1(X1,X1,X1,X1,X1,X0,X2) ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_2074,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2))
    | r2_hidden(sK3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))
    | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != k5_enumset1(X1,X1,X1,X1,X1,X0,X2)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_2672,plain,
    ( r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | ~ r2_hidden(sK3,k5_enumset1(X1,X1,X1,X1,X1,sK3,X2))
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k5_enumset1(X1,X1,X1,X1,X1,sK3,X2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_2674,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK2))
    | r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2350,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1,c_22])).

cnf(c_2357,plain,
    ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,X0) ),
    inference(superposition,[status(thm)],[c_2350,c_1])).

cnf(c_2359,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,X0) ),
    inference(demodulation,[status(thm)],[c_2357,c_1])).

cnf(c_2360,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2359])).

cnf(c_1295,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1801,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1638,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1640,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_1296,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1606,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_1607,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_18,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_28,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_21,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f67])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4920,c_2674,c_2360,c_1801,c_1640,c_1607,c_28,c_25,c_21])).

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
% 0.14/0.34  % DateTime   : Tue Dec  1 13:54:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.12/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/1.00  
% 3.12/1.00  ------  iProver source info
% 3.12/1.00  
% 3.12/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.12/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/1.00  git: non_committed_changes: false
% 3.12/1.00  git: last_make_outside_of_git: false
% 3.12/1.00  
% 3.12/1.00  ------ 
% 3.12/1.00  
% 3.12/1.00  ------ Input Options
% 3.12/1.00  
% 3.12/1.00  --out_options                           all
% 3.12/1.00  --tptp_safe_out                         true
% 3.12/1.00  --problem_path                          ""
% 3.12/1.00  --include_path                          ""
% 3.12/1.00  --clausifier                            res/vclausify_rel
% 3.12/1.00  --clausifier_options                    --mode clausify
% 3.12/1.00  --stdin                                 false
% 3.12/1.00  --stats_out                             all
% 3.12/1.00  
% 3.12/1.00  ------ General Options
% 3.12/1.00  
% 3.12/1.00  --fof                                   false
% 3.12/1.00  --time_out_real                         305.
% 3.12/1.00  --time_out_virtual                      -1.
% 3.12/1.00  --symbol_type_check                     false
% 3.12/1.00  --clausify_out                          false
% 3.12/1.00  --sig_cnt_out                           false
% 3.12/1.00  --trig_cnt_out                          false
% 3.12/1.00  --trig_cnt_out_tolerance                1.
% 3.12/1.00  --trig_cnt_out_sk_spl                   false
% 3.12/1.00  --abstr_cl_out                          false
% 3.12/1.00  
% 3.12/1.00  ------ Global Options
% 3.12/1.00  
% 3.12/1.00  --schedule                              default
% 3.12/1.00  --add_important_lit                     false
% 3.12/1.00  --prop_solver_per_cl                    1000
% 3.12/1.00  --min_unsat_core                        false
% 3.12/1.00  --soft_assumptions                      false
% 3.12/1.00  --soft_lemma_size                       3
% 3.12/1.00  --prop_impl_unit_size                   0
% 3.12/1.00  --prop_impl_unit                        []
% 3.12/1.00  --share_sel_clauses                     true
% 3.12/1.00  --reset_solvers                         false
% 3.12/1.00  --bc_imp_inh                            [conj_cone]
% 3.12/1.00  --conj_cone_tolerance                   3.
% 3.12/1.00  --extra_neg_conj                        none
% 3.12/1.00  --large_theory_mode                     true
% 3.12/1.00  --prolific_symb_bound                   200
% 3.12/1.00  --lt_threshold                          2000
% 3.12/1.00  --clause_weak_htbl                      true
% 3.12/1.00  --gc_record_bc_elim                     false
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing Options
% 3.12/1.00  
% 3.12/1.00  --preprocessing_flag                    true
% 3.12/1.00  --time_out_prep_mult                    0.1
% 3.12/1.00  --splitting_mode                        input
% 3.12/1.00  --splitting_grd                         true
% 3.12/1.00  --splitting_cvd                         false
% 3.12/1.00  --splitting_cvd_svl                     false
% 3.12/1.00  --splitting_nvd                         32
% 3.12/1.00  --sub_typing                            true
% 3.12/1.00  --prep_gs_sim                           true
% 3.12/1.00  --prep_unflatten                        true
% 3.12/1.00  --prep_res_sim                          true
% 3.12/1.00  --prep_upred                            true
% 3.12/1.00  --prep_sem_filter                       exhaustive
% 3.12/1.00  --prep_sem_filter_out                   false
% 3.12/1.00  --pred_elim                             true
% 3.12/1.00  --res_sim_input                         true
% 3.12/1.00  --eq_ax_congr_red                       true
% 3.12/1.00  --pure_diseq_elim                       true
% 3.12/1.00  --brand_transform                       false
% 3.12/1.00  --non_eq_to_eq                          false
% 3.12/1.00  --prep_def_merge                        true
% 3.12/1.00  --prep_def_merge_prop_impl              false
% 3.12/1.00  --prep_def_merge_mbd                    true
% 3.12/1.00  --prep_def_merge_tr_red                 false
% 3.12/1.00  --prep_def_merge_tr_cl                  false
% 3.12/1.00  --smt_preprocessing                     true
% 3.12/1.00  --smt_ac_axioms                         fast
% 3.12/1.00  --preprocessed_out                      false
% 3.12/1.00  --preprocessed_stats                    false
% 3.12/1.00  
% 3.12/1.00  ------ Abstraction refinement Options
% 3.12/1.00  
% 3.12/1.00  --abstr_ref                             []
% 3.12/1.00  --abstr_ref_prep                        false
% 3.12/1.00  --abstr_ref_until_sat                   false
% 3.12/1.00  --abstr_ref_sig_restrict                funpre
% 3.12/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.00  --abstr_ref_under                       []
% 3.12/1.00  
% 3.12/1.00  ------ SAT Options
% 3.12/1.00  
% 3.12/1.00  --sat_mode                              false
% 3.12/1.00  --sat_fm_restart_options                ""
% 3.12/1.00  --sat_gr_def                            false
% 3.12/1.00  --sat_epr_types                         true
% 3.12/1.00  --sat_non_cyclic_types                  false
% 3.12/1.00  --sat_finite_models                     false
% 3.12/1.00  --sat_fm_lemmas                         false
% 3.12/1.00  --sat_fm_prep                           false
% 3.12/1.00  --sat_fm_uc_incr                        true
% 3.12/1.00  --sat_out_model                         small
% 3.12/1.00  --sat_out_clauses                       false
% 3.12/1.00  
% 3.12/1.00  ------ QBF Options
% 3.12/1.00  
% 3.12/1.00  --qbf_mode                              false
% 3.12/1.00  --qbf_elim_univ                         false
% 3.12/1.00  --qbf_dom_inst                          none
% 3.12/1.00  --qbf_dom_pre_inst                      false
% 3.12/1.00  --qbf_sk_in                             false
% 3.12/1.00  --qbf_pred_elim                         true
% 3.12/1.00  --qbf_split                             512
% 3.12/1.00  
% 3.12/1.00  ------ BMC1 Options
% 3.12/1.00  
% 3.12/1.00  --bmc1_incremental                      false
% 3.12/1.00  --bmc1_axioms                           reachable_all
% 3.12/1.00  --bmc1_min_bound                        0
% 3.12/1.00  --bmc1_max_bound                        -1
% 3.12/1.00  --bmc1_max_bound_default                -1
% 3.12/1.00  --bmc1_symbol_reachability              true
% 3.12/1.00  --bmc1_property_lemmas                  false
% 3.12/1.00  --bmc1_k_induction                      false
% 3.12/1.00  --bmc1_non_equiv_states                 false
% 3.12/1.00  --bmc1_deadlock                         false
% 3.12/1.00  --bmc1_ucm                              false
% 3.12/1.00  --bmc1_add_unsat_core                   none
% 3.12/1.00  --bmc1_unsat_core_children              false
% 3.12/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.00  --bmc1_out_stat                         full
% 3.12/1.00  --bmc1_ground_init                      false
% 3.12/1.00  --bmc1_pre_inst_next_state              false
% 3.12/1.00  --bmc1_pre_inst_state                   false
% 3.12/1.00  --bmc1_pre_inst_reach_state             false
% 3.12/1.00  --bmc1_out_unsat_core                   false
% 3.12/1.00  --bmc1_aig_witness_out                  false
% 3.12/1.00  --bmc1_verbose                          false
% 3.12/1.00  --bmc1_dump_clauses_tptp                false
% 3.12/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.00  --bmc1_dump_file                        -
% 3.12/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.00  --bmc1_ucm_extend_mode                  1
% 3.12/1.00  --bmc1_ucm_init_mode                    2
% 3.12/1.00  --bmc1_ucm_cone_mode                    none
% 3.12/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.00  --bmc1_ucm_relax_model                  4
% 3.12/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.00  --bmc1_ucm_layered_model                none
% 3.12/1.00  --bmc1_ucm_max_lemma_size               10
% 3.12/1.00  
% 3.12/1.00  ------ AIG Options
% 3.12/1.00  
% 3.12/1.00  --aig_mode                              false
% 3.12/1.00  
% 3.12/1.00  ------ Instantiation Options
% 3.12/1.00  
% 3.12/1.00  --instantiation_flag                    true
% 3.12/1.00  --inst_sos_flag                         false
% 3.12/1.00  --inst_sos_phase                        true
% 3.12/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel_side                     num_symb
% 3.12/1.00  --inst_solver_per_active                1400
% 3.12/1.00  --inst_solver_calls_frac                1.
% 3.12/1.00  --inst_passive_queue_type               priority_queues
% 3.12/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.00  --inst_passive_queues_freq              [25;2]
% 3.12/1.00  --inst_dismatching                      true
% 3.12/1.00  --inst_eager_unprocessed_to_passive     true
% 3.12/1.00  --inst_prop_sim_given                   true
% 3.12/1.00  --inst_prop_sim_new                     false
% 3.12/1.00  --inst_subs_new                         false
% 3.12/1.00  --inst_eq_res_simp                      false
% 3.12/1.00  --inst_subs_given                       false
% 3.12/1.00  --inst_orphan_elimination               true
% 3.12/1.00  --inst_learning_loop_flag               true
% 3.12/1.00  --inst_learning_start                   3000
% 3.12/1.00  --inst_learning_factor                  2
% 3.12/1.00  --inst_start_prop_sim_after_learn       3
% 3.12/1.00  --inst_sel_renew                        solver
% 3.12/1.00  --inst_lit_activity_flag                true
% 3.12/1.00  --inst_restr_to_given                   false
% 3.12/1.00  --inst_activity_threshold               500
% 3.12/1.00  --inst_out_proof                        true
% 3.12/1.00  
% 3.12/1.00  ------ Resolution Options
% 3.12/1.00  
% 3.12/1.00  --resolution_flag                       true
% 3.12/1.00  --res_lit_sel                           adaptive
% 3.12/1.00  --res_lit_sel_side                      none
% 3.12/1.00  --res_ordering                          kbo
% 3.12/1.00  --res_to_prop_solver                    active
% 3.12/1.00  --res_prop_simpl_new                    false
% 3.12/1.00  --res_prop_simpl_given                  true
% 3.12/1.00  --res_passive_queue_type                priority_queues
% 3.12/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.00  --res_passive_queues_freq               [15;5]
% 3.12/1.00  --res_forward_subs                      full
% 3.12/1.00  --res_backward_subs                     full
% 3.12/1.00  --res_forward_subs_resolution           true
% 3.12/1.00  --res_backward_subs_resolution          true
% 3.12/1.00  --res_orphan_elimination                true
% 3.12/1.00  --res_time_limit                        2.
% 3.12/1.00  --res_out_proof                         true
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Options
% 3.12/1.00  
% 3.12/1.00  --superposition_flag                    true
% 3.12/1.00  --sup_passive_queue_type                priority_queues
% 3.12/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.00  --demod_completeness_check              fast
% 3.12/1.00  --demod_use_ground                      true
% 3.12/1.00  --sup_to_prop_solver                    passive
% 3.12/1.00  --sup_prop_simpl_new                    true
% 3.12/1.00  --sup_prop_simpl_given                  true
% 3.12/1.00  --sup_fun_splitting                     false
% 3.12/1.00  --sup_smt_interval                      50000
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Simplification Setup
% 3.12/1.00  
% 3.12/1.00  --sup_indices_passive                   []
% 3.12/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_full_bw                           [BwDemod]
% 3.12/1.00  --sup_immed_triv                        [TrivRules]
% 3.12/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_immed_bw_main                     []
% 3.12/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  
% 3.12/1.00  ------ Combination Options
% 3.12/1.00  
% 3.12/1.00  --comb_res_mult                         3
% 3.12/1.00  --comb_sup_mult                         2
% 3.12/1.00  --comb_inst_mult                        10
% 3.12/1.00  
% 3.12/1.00  ------ Debug Options
% 3.12/1.00  
% 3.12/1.00  --dbg_backtrace                         false
% 3.12/1.00  --dbg_dump_prop_clauses                 false
% 3.12/1.00  --dbg_dump_prop_clauses_file            -
% 3.12/1.00  --dbg_out_stat                          false
% 3.12/1.00  ------ Parsing...
% 3.12/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/1.00  ------ Proving...
% 3.12/1.00  ------ Problem Properties 
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  clauses                                 22
% 3.12/1.00  conjectures                             2
% 3.12/1.00  EPR                                     1
% 3.12/1.00  Horn                                    19
% 3.12/1.00  unary                                   14
% 3.12/1.00  binary                                  1
% 3.12/1.00  lits                                    40
% 3.12/1.00  lits eq                                 28
% 3.12/1.00  fd_pure                                 0
% 3.12/1.00  fd_pseudo                               0
% 3.12/1.00  fd_cond                                 0
% 3.12/1.00  fd_pseudo_cond                          6
% 3.12/1.00  AC symbols                              0
% 3.12/1.00  
% 3.12/1.00  ------ Schedule dynamic 5 is on 
% 3.12/1.00  
% 3.12/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  ------ 
% 3.12/1.00  Current options:
% 3.12/1.00  ------ 
% 3.12/1.00  
% 3.12/1.00  ------ Input Options
% 3.12/1.00  
% 3.12/1.00  --out_options                           all
% 3.12/1.00  --tptp_safe_out                         true
% 3.12/1.00  --problem_path                          ""
% 3.12/1.00  --include_path                          ""
% 3.12/1.00  --clausifier                            res/vclausify_rel
% 3.12/1.00  --clausifier_options                    --mode clausify
% 3.12/1.00  --stdin                                 false
% 3.12/1.00  --stats_out                             all
% 3.12/1.00  
% 3.12/1.00  ------ General Options
% 3.12/1.00  
% 3.12/1.00  --fof                                   false
% 3.12/1.00  --time_out_real                         305.
% 3.12/1.00  --time_out_virtual                      -1.
% 3.12/1.00  --symbol_type_check                     false
% 3.12/1.00  --clausify_out                          false
% 3.12/1.00  --sig_cnt_out                           false
% 3.12/1.00  --trig_cnt_out                          false
% 3.12/1.00  --trig_cnt_out_tolerance                1.
% 3.12/1.00  --trig_cnt_out_sk_spl                   false
% 3.12/1.00  --abstr_cl_out                          false
% 3.12/1.00  
% 3.12/1.00  ------ Global Options
% 3.12/1.00  
% 3.12/1.00  --schedule                              default
% 3.12/1.00  --add_important_lit                     false
% 3.12/1.00  --prop_solver_per_cl                    1000
% 3.12/1.00  --min_unsat_core                        false
% 3.12/1.00  --soft_assumptions                      false
% 3.12/1.00  --soft_lemma_size                       3
% 3.12/1.00  --prop_impl_unit_size                   0
% 3.12/1.00  --prop_impl_unit                        []
% 3.12/1.00  --share_sel_clauses                     true
% 3.12/1.00  --reset_solvers                         false
% 3.12/1.00  --bc_imp_inh                            [conj_cone]
% 3.12/1.00  --conj_cone_tolerance                   3.
% 3.12/1.00  --extra_neg_conj                        none
% 3.12/1.00  --large_theory_mode                     true
% 3.12/1.00  --prolific_symb_bound                   200
% 3.12/1.00  --lt_threshold                          2000
% 3.12/1.00  --clause_weak_htbl                      true
% 3.12/1.00  --gc_record_bc_elim                     false
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing Options
% 3.12/1.00  
% 3.12/1.00  --preprocessing_flag                    true
% 3.12/1.00  --time_out_prep_mult                    0.1
% 3.12/1.00  --splitting_mode                        input
% 3.12/1.00  --splitting_grd                         true
% 3.12/1.00  --splitting_cvd                         false
% 3.12/1.00  --splitting_cvd_svl                     false
% 3.12/1.00  --splitting_nvd                         32
% 3.12/1.00  --sub_typing                            true
% 3.12/1.00  --prep_gs_sim                           true
% 3.12/1.00  --prep_unflatten                        true
% 3.12/1.00  --prep_res_sim                          true
% 3.12/1.00  --prep_upred                            true
% 3.12/1.00  --prep_sem_filter                       exhaustive
% 3.12/1.00  --prep_sem_filter_out                   false
% 3.12/1.00  --pred_elim                             true
% 3.12/1.00  --res_sim_input                         true
% 3.12/1.00  --eq_ax_congr_red                       true
% 3.12/1.00  --pure_diseq_elim                       true
% 3.12/1.00  --brand_transform                       false
% 3.12/1.00  --non_eq_to_eq                          false
% 3.12/1.00  --prep_def_merge                        true
% 3.12/1.00  --prep_def_merge_prop_impl              false
% 3.12/1.00  --prep_def_merge_mbd                    true
% 3.12/1.00  --prep_def_merge_tr_red                 false
% 3.12/1.00  --prep_def_merge_tr_cl                  false
% 3.12/1.00  --smt_preprocessing                     true
% 3.12/1.00  --smt_ac_axioms                         fast
% 3.12/1.00  --preprocessed_out                      false
% 3.12/1.00  --preprocessed_stats                    false
% 3.12/1.00  
% 3.12/1.00  ------ Abstraction refinement Options
% 3.12/1.00  
% 3.12/1.00  --abstr_ref                             []
% 3.12/1.00  --abstr_ref_prep                        false
% 3.12/1.00  --abstr_ref_until_sat                   false
% 3.12/1.00  --abstr_ref_sig_restrict                funpre
% 3.12/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.00  --abstr_ref_under                       []
% 3.12/1.00  
% 3.12/1.00  ------ SAT Options
% 3.12/1.00  
% 3.12/1.00  --sat_mode                              false
% 3.12/1.00  --sat_fm_restart_options                ""
% 3.12/1.00  --sat_gr_def                            false
% 3.12/1.00  --sat_epr_types                         true
% 3.12/1.00  --sat_non_cyclic_types                  false
% 3.12/1.00  --sat_finite_models                     false
% 3.12/1.00  --sat_fm_lemmas                         false
% 3.12/1.00  --sat_fm_prep                           false
% 3.12/1.00  --sat_fm_uc_incr                        true
% 3.12/1.00  --sat_out_model                         small
% 3.12/1.00  --sat_out_clauses                       false
% 3.12/1.00  
% 3.12/1.00  ------ QBF Options
% 3.12/1.00  
% 3.12/1.00  --qbf_mode                              false
% 3.12/1.00  --qbf_elim_univ                         false
% 3.12/1.00  --qbf_dom_inst                          none
% 3.12/1.00  --qbf_dom_pre_inst                      false
% 3.12/1.00  --qbf_sk_in                             false
% 3.12/1.00  --qbf_pred_elim                         true
% 3.12/1.00  --qbf_split                             512
% 3.12/1.00  
% 3.12/1.00  ------ BMC1 Options
% 3.12/1.00  
% 3.12/1.00  --bmc1_incremental                      false
% 3.12/1.00  --bmc1_axioms                           reachable_all
% 3.12/1.00  --bmc1_min_bound                        0
% 3.12/1.00  --bmc1_max_bound                        -1
% 3.12/1.00  --bmc1_max_bound_default                -1
% 3.12/1.00  --bmc1_symbol_reachability              true
% 3.12/1.00  --bmc1_property_lemmas                  false
% 3.12/1.00  --bmc1_k_induction                      false
% 3.12/1.00  --bmc1_non_equiv_states                 false
% 3.12/1.00  --bmc1_deadlock                         false
% 3.12/1.00  --bmc1_ucm                              false
% 3.12/1.00  --bmc1_add_unsat_core                   none
% 3.12/1.00  --bmc1_unsat_core_children              false
% 3.12/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.00  --bmc1_out_stat                         full
% 3.12/1.00  --bmc1_ground_init                      false
% 3.12/1.00  --bmc1_pre_inst_next_state              false
% 3.12/1.00  --bmc1_pre_inst_state                   false
% 3.12/1.00  --bmc1_pre_inst_reach_state             false
% 3.12/1.00  --bmc1_out_unsat_core                   false
% 3.12/1.00  --bmc1_aig_witness_out                  false
% 3.12/1.00  --bmc1_verbose                          false
% 3.12/1.00  --bmc1_dump_clauses_tptp                false
% 3.12/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.00  --bmc1_dump_file                        -
% 3.12/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.00  --bmc1_ucm_extend_mode                  1
% 3.12/1.00  --bmc1_ucm_init_mode                    2
% 3.12/1.00  --bmc1_ucm_cone_mode                    none
% 3.12/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.00  --bmc1_ucm_relax_model                  4
% 3.12/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.00  --bmc1_ucm_layered_model                none
% 3.12/1.00  --bmc1_ucm_max_lemma_size               10
% 3.12/1.00  
% 3.12/1.00  ------ AIG Options
% 3.12/1.00  
% 3.12/1.00  --aig_mode                              false
% 3.12/1.00  
% 3.12/1.00  ------ Instantiation Options
% 3.12/1.00  
% 3.12/1.00  --instantiation_flag                    true
% 3.12/1.00  --inst_sos_flag                         false
% 3.12/1.00  --inst_sos_phase                        true
% 3.12/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel_side                     none
% 3.12/1.00  --inst_solver_per_active                1400
% 3.12/1.00  --inst_solver_calls_frac                1.
% 3.12/1.00  --inst_passive_queue_type               priority_queues
% 3.12/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.00  --inst_passive_queues_freq              [25;2]
% 3.12/1.00  --inst_dismatching                      true
% 3.12/1.00  --inst_eager_unprocessed_to_passive     true
% 3.12/1.00  --inst_prop_sim_given                   true
% 3.12/1.00  --inst_prop_sim_new                     false
% 3.12/1.00  --inst_subs_new                         false
% 3.12/1.00  --inst_eq_res_simp                      false
% 3.12/1.00  --inst_subs_given                       false
% 3.12/1.00  --inst_orphan_elimination               true
% 3.12/1.00  --inst_learning_loop_flag               true
% 3.12/1.00  --inst_learning_start                   3000
% 3.12/1.00  --inst_learning_factor                  2
% 3.12/1.00  --inst_start_prop_sim_after_learn       3
% 3.12/1.00  --inst_sel_renew                        solver
% 3.12/1.00  --inst_lit_activity_flag                true
% 3.12/1.00  --inst_restr_to_given                   false
% 3.12/1.00  --inst_activity_threshold               500
% 3.12/1.00  --inst_out_proof                        true
% 3.12/1.00  
% 3.12/1.00  ------ Resolution Options
% 3.12/1.00  
% 3.12/1.00  --resolution_flag                       false
% 3.12/1.00  --res_lit_sel                           adaptive
% 3.12/1.00  --res_lit_sel_side                      none
% 3.12/1.00  --res_ordering                          kbo
% 3.12/1.00  --res_to_prop_solver                    active
% 3.12/1.00  --res_prop_simpl_new                    false
% 3.12/1.00  --res_prop_simpl_given                  true
% 3.12/1.00  --res_passive_queue_type                priority_queues
% 3.12/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.00  --res_passive_queues_freq               [15;5]
% 3.12/1.00  --res_forward_subs                      full
% 3.12/1.00  --res_backward_subs                     full
% 3.12/1.00  --res_forward_subs_resolution           true
% 3.12/1.00  --res_backward_subs_resolution          true
% 3.12/1.00  --res_orphan_elimination                true
% 3.12/1.00  --res_time_limit                        2.
% 3.12/1.00  --res_out_proof                         true
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Options
% 3.12/1.00  
% 3.12/1.00  --superposition_flag                    true
% 3.12/1.00  --sup_passive_queue_type                priority_queues
% 3.12/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.00  --demod_completeness_check              fast
% 3.12/1.00  --demod_use_ground                      true
% 3.12/1.00  --sup_to_prop_solver                    passive
% 3.12/1.00  --sup_prop_simpl_new                    true
% 3.12/1.00  --sup_prop_simpl_given                  true
% 3.12/1.00  --sup_fun_splitting                     false
% 3.12/1.00  --sup_smt_interval                      50000
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Simplification Setup
% 3.12/1.00  
% 3.12/1.00  --sup_indices_passive                   []
% 3.12/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_full_bw                           [BwDemod]
% 3.12/1.00  --sup_immed_triv                        [TrivRules]
% 3.12/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_immed_bw_main                     []
% 3.12/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  
% 3.12/1.00  ------ Combination Options
% 3.12/1.00  
% 3.12/1.00  --comb_res_mult                         3
% 3.12/1.00  --comb_sup_mult                         2
% 3.12/1.00  --comb_inst_mult                        10
% 3.12/1.00  
% 3.12/1.00  ------ Debug Options
% 3.12/1.00  
% 3.12/1.00  --dbg_backtrace                         false
% 3.12/1.00  --dbg_dump_prop_clauses                 false
% 3.12/1.00  --dbg_dump_prop_clauses_file            -
% 3.12/1.00  --dbg_out_stat                          false
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  ------ Proving...
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  % SZS status Theorem for theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  fof(f10,axiom,(
% 3.12/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f24,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.12/1.00    inference(ennf_transformation,[],[f10])).
% 3.12/1.00  
% 3.12/1.00  fof(f26,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.12/1.00    inference(nnf_transformation,[],[f24])).
% 3.12/1.00  
% 3.12/1.00  fof(f27,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.12/1.00    inference(flattening,[],[f26])).
% 3.12/1.00  
% 3.12/1.00  fof(f28,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.12/1.00    inference(rectify,[],[f27])).
% 3.12/1.00  
% 3.12/1.00  fof(f29,plain,(
% 3.12/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f30,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.12/1.00  
% 3.12/1.00  fof(f48,plain,(
% 3.12/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.12/1.00    inference(cnf_transformation,[],[f30])).
% 3.12/1.00  
% 3.12/1.00  fof(f15,axiom,(
% 3.12/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f61,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f15])).
% 3.12/1.00  
% 3.12/1.00  fof(f16,axiom,(
% 3.12/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f62,plain,(
% 3.12/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f16])).
% 3.12/1.00  
% 3.12/1.00  fof(f17,axiom,(
% 3.12/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f63,plain,(
% 3.12/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f17])).
% 3.12/1.00  
% 3.12/1.00  fof(f18,axiom,(
% 3.12/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f64,plain,(
% 3.12/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f18])).
% 3.12/1.00  
% 3.12/1.00  fof(f68,plain,(
% 3.12/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.12/1.00    inference(definition_unfolding,[],[f63,f64])).
% 3.12/1.00  
% 3.12/1.00  fof(f69,plain,(
% 3.12/1.00    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.12/1.00    inference(definition_unfolding,[],[f62,f68])).
% 3.12/1.00  
% 3.12/1.00  fof(f70,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.12/1.00    inference(definition_unfolding,[],[f61,f69])).
% 3.12/1.00  
% 3.12/1.00  fof(f83,plain,(
% 3.12/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.12/1.00    inference(definition_unfolding,[],[f48,f70])).
% 3.12/1.00  
% 3.12/1.00  fof(f93,plain,(
% 3.12/1.00    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 3.12/1.00    inference(equality_resolution,[],[f83])).
% 3.12/1.00  
% 3.12/1.00  fof(f94,plain,(
% 3.12/1.00    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2))) )),
% 3.12/1.00    inference(equality_resolution,[],[f93])).
% 3.12/1.00  
% 3.12/1.00  fof(f12,axiom,(
% 3.12/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f58,plain,(
% 3.12/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f12])).
% 3.12/1.00  
% 3.12/1.00  fof(f9,axiom,(
% 3.12/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f45,plain,(
% 3.12/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f9])).
% 3.12/1.00  
% 3.12/1.00  fof(f13,axiom,(
% 3.12/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f59,plain,(
% 3.12/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f13])).
% 3.12/1.00  
% 3.12/1.00  fof(f14,axiom,(
% 3.12/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f60,plain,(
% 3.12/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f14])).
% 3.12/1.00  
% 3.12/1.00  fof(f71,plain,(
% 3.12/1.00    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.12/1.00    inference(definition_unfolding,[],[f60,f70])).
% 3.12/1.00  
% 3.12/1.00  fof(f72,plain,(
% 3.12/1.00    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.12/1.00    inference(definition_unfolding,[],[f59,f71])).
% 3.12/1.00  
% 3.12/1.00  fof(f74,plain,(
% 3.12/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.12/1.00    inference(definition_unfolding,[],[f58,f45,f64,f72])).
% 3.12/1.00  
% 3.12/1.00  fof(f20,conjecture,(
% 3.12/1.00    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f21,negated_conjecture,(
% 3.12/1.00    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.12/1.00    inference(negated_conjecture,[],[f20])).
% 3.12/1.00  
% 3.12/1.00  fof(f25,plain,(
% 3.12/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.12/1.00    inference(ennf_transformation,[],[f21])).
% 3.12/1.00  
% 3.12/1.00  fof(f35,plain,(
% 3.12/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f36,plain,(
% 3.12/1.00    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f35])).
% 3.12/1.00  
% 3.12/1.00  fof(f66,plain,(
% 3.12/1.00    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.12/1.00    inference(cnf_transformation,[],[f36])).
% 3.12/1.00  
% 3.12/1.00  fof(f90,plain,(
% 3.12/1.00    k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 3.12/1.00    inference(definition_unfolding,[],[f66,f45,f72,f72,f72])).
% 3.12/1.00  
% 3.12/1.00  fof(f11,axiom,(
% 3.12/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.12/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f31,plain,(
% 3.12/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.12/1.00    inference(nnf_transformation,[],[f11])).
% 3.12/1.00  
% 3.12/1.00  fof(f32,plain,(
% 3.12/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.12/1.00    inference(rectify,[],[f31])).
% 3.12/1.00  
% 3.12/1.00  fof(f33,plain,(
% 3.12/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f34,plain,(
% 3.12/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 3.12/1.00  
% 3.12/1.00  fof(f54,plain,(
% 3.12/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.12/1.00    inference(cnf_transformation,[],[f34])).
% 3.12/1.00  
% 3.12/1.00  fof(f89,plain,(
% 3.12/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.12/1.00    inference(definition_unfolding,[],[f54,f72])).
% 3.12/1.00  
% 3.12/1.00  fof(f100,plain,(
% 3.12/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 3.12/1.00    inference(equality_resolution,[],[f89])).
% 3.12/1.00  
% 3.12/1.00  fof(f55,plain,(
% 3.12/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.12/1.00    inference(cnf_transformation,[],[f34])).
% 3.12/1.00  
% 3.12/1.00  fof(f88,plain,(
% 3.12/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.12/1.00    inference(definition_unfolding,[],[f55,f72])).
% 3.12/1.00  
% 3.12/1.00  fof(f98,plain,(
% 3.12/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 3.12/1.00    inference(equality_resolution,[],[f88])).
% 3.12/1.00  
% 3.12/1.00  fof(f99,plain,(
% 3.12/1.00    ( ! [X3] : (r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) )),
% 3.12/1.00    inference(equality_resolution,[],[f98])).
% 3.12/1.00  
% 3.12/1.00  fof(f67,plain,(
% 3.12/1.00    sK2 != sK3),
% 3.12/1.00    inference(cnf_transformation,[],[f36])).
% 3.12/1.00  
% 3.12/1.00  cnf(c_13,plain,
% 3.12/1.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
% 3.12/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4918,plain,
% 3.12/1.00      ( r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,sK3,X1)) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4920,plain,
% 3.12/1.00      ( r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK2)) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_4918]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1300,plain,
% 3.12/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.12/1.00      theory(equality) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1615,plain,
% 3.12/1.00      ( r2_hidden(X0,X1)
% 3.12/1.00      | ~ r2_hidden(X2,k5_enumset1(X3,X3,X3,X3,X3,X2,X4))
% 3.12/1.00      | X0 != X2
% 3.12/1.00      | X1 != k5_enumset1(X3,X3,X3,X3,X3,X2,X4) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_1300]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1731,plain,
% 3.12/1.00      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2))
% 3.12/1.00      | r2_hidden(X3,k5_enumset1(X4,X4,X4,X4,X4,X4,X4))
% 3.12/1.00      | X3 != X0
% 3.12/1.00      | k5_enumset1(X4,X4,X4,X4,X4,X4,X4) != k5_enumset1(X1,X1,X1,X1,X1,X0,X2) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_1615]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2074,plain,
% 3.12/1.00      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2))
% 3.12/1.00      | r2_hidden(sK3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))
% 3.12/1.00      | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != k5_enumset1(X1,X1,X1,X1,X1,X0,X2)
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_1731]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2672,plain,
% 3.12/1.00      ( r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
% 3.12/1.00      | ~ r2_hidden(sK3,k5_enumset1(X1,X1,X1,X1,X1,sK3,X2))
% 3.12/1.00      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k5_enumset1(X1,X1,X1,X1,X1,sK3,X2)
% 3.12/1.00      | sK3 != sK3 ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_2074]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2674,plain,
% 3.12/1.00      ( ~ r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK2))
% 3.12/1.00      | r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.12/1.00      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK2)
% 3.12/1.00      | sK3 != sK3 ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_2672]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1,plain,
% 3.12/1.00      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.12/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_22,negated_conjecture,
% 3.12/1.00      ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.12/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2350,plain,
% 3.12/1.00      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_1,c_22]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2357,plain,
% 3.12/1.00      ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,X0) ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_2350,c_1]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2359,plain,
% 3.12/1.00      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,X0) ),
% 3.12/1.00      inference(demodulation,[status(thm)],[c_2357,c_1]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2360,plain,
% 3.12/1.00      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK2) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_2359]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1295,plain,( X0 = X0 ),theory(equality) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1801,plain,
% 3.12/1.00      ( sK3 = sK3 ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_1295]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_19,plain,
% 3.12/1.00      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.12/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1638,plain,
% 3.12/1.00      ( ~ r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | sK3 = X0 ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1640,plain,
% 3.12/1.00      ( ~ r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.12/1.00      | sK3 = sK2 ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_1638]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1296,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1606,plain,
% 3.12/1.00      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_1296]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1607,plain,
% 3.12/1.00      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_1606]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_18,plain,
% 3.12/1.00      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
% 3.12/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_28,plain,
% 3.12/1.00      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_25,plain,
% 3.12/1.00      ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.12/1.00      | sK2 = sK2 ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_21,negated_conjecture,
% 3.12/1.00      ( sK2 != sK3 ),
% 3.12/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(contradiction,plain,
% 3.12/1.00      ( $false ),
% 3.12/1.00      inference(minisat,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_4920,c_2674,c_2360,c_1801,c_1640,c_1607,c_28,c_25,
% 3.12/1.00                 c_21]) ).
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  ------                               Statistics
% 3.12/1.00  
% 3.12/1.00  ------ General
% 3.12/1.00  
% 3.12/1.00  abstr_ref_over_cycles:                  0
% 3.12/1.00  abstr_ref_under_cycles:                 0
% 3.12/1.00  gc_basic_clause_elim:                   0
% 3.12/1.00  forced_gc_time:                         0
% 3.12/1.00  parsing_time:                           0.014
% 3.12/1.00  unif_index_cands_time:                  0.
% 3.12/1.00  unif_index_add_time:                    0.
% 3.12/1.00  orderings_time:                         0.
% 3.12/1.00  out_proof_time:                         0.012
% 3.12/1.00  total_time:                             0.302
% 3.12/1.00  num_of_symbols:                         42
% 3.12/1.00  num_of_terms:                           6994
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing
% 3.12/1.00  
% 3.12/1.00  num_of_splits:                          0
% 3.12/1.00  num_of_split_atoms:                     0
% 3.12/1.00  num_of_reused_defs:                     0
% 3.12/1.00  num_eq_ax_congr_red:                    43
% 3.12/1.00  num_of_sem_filtered_clauses:            1
% 3.12/1.00  num_of_subtypes:                        0
% 3.12/1.00  monotx_restored_types:                  0
% 3.12/1.00  sat_num_of_epr_types:                   0
% 3.12/1.00  sat_num_of_non_cyclic_types:            0
% 3.12/1.00  sat_guarded_non_collapsed_types:        0
% 3.12/1.00  num_pure_diseq_elim:                    0
% 3.12/1.00  simp_replaced_by:                       0
% 3.12/1.00  res_preprocessed:                       102
% 3.12/1.00  prep_upred:                             0
% 3.12/1.00  prep_unflattend:                        74
% 3.12/1.00  smt_new_axioms:                         0
% 3.12/1.00  pred_elim_cands:                        1
% 3.12/1.00  pred_elim:                              1
% 3.12/1.00  pred_elim_cl:                           1
% 3.12/1.00  pred_elim_cycles:                       3
% 3.12/1.00  merged_defs:                            0
% 3.12/1.00  merged_defs_ncl:                        0
% 3.12/1.00  bin_hyper_res:                          0
% 3.12/1.00  prep_cycles:                            4
% 3.12/1.00  pred_elim_time:                         0.015
% 3.12/1.00  splitting_time:                         0.
% 3.12/1.00  sem_filter_time:                        0.
% 3.12/1.00  monotx_time:                            0.
% 3.12/1.00  subtype_inf_time:                       0.
% 3.12/1.00  
% 3.12/1.00  ------ Problem properties
% 3.12/1.00  
% 3.12/1.00  clauses:                                22
% 3.12/1.00  conjectures:                            2
% 3.12/1.00  epr:                                    1
% 3.12/1.00  horn:                                   19
% 3.12/1.00  ground:                                 2
% 3.12/1.00  unary:                                  14
% 3.12/1.00  binary:                                 1
% 3.12/1.00  lits:                                   40
% 3.12/1.00  lits_eq:                                28
% 3.12/1.00  fd_pure:                                0
% 3.12/1.00  fd_pseudo:                              0
% 3.12/1.00  fd_cond:                                0
% 3.12/1.00  fd_pseudo_cond:                         6
% 3.12/1.00  ac_symbols:                             0
% 3.12/1.00  
% 3.12/1.00  ------ Propositional Solver
% 3.12/1.00  
% 3.12/1.00  prop_solver_calls:                      26
% 3.12/1.00  prop_fast_solver_calls:                 680
% 3.12/1.00  smt_solver_calls:                       0
% 3.12/1.00  smt_fast_solver_calls:                  0
% 3.12/1.00  prop_num_of_clauses:                    1609
% 3.12/1.00  prop_preprocess_simplified:             5563
% 3.12/1.00  prop_fo_subsumed:                       0
% 3.12/1.00  prop_solver_time:                       0.
% 3.12/1.00  smt_solver_time:                        0.
% 3.12/1.00  smt_fast_solver_time:                   0.
% 3.12/1.00  prop_fast_solver_time:                  0.
% 3.12/1.00  prop_unsat_core_time:                   0.
% 3.12/1.00  
% 3.12/1.00  ------ QBF
% 3.12/1.00  
% 3.12/1.00  qbf_q_res:                              0
% 3.12/1.00  qbf_num_tautologies:                    0
% 3.12/1.00  qbf_prep_cycles:                        0
% 3.12/1.00  
% 3.12/1.00  ------ BMC1
% 3.12/1.00  
% 3.12/1.00  bmc1_current_bound:                     -1
% 3.12/1.00  bmc1_last_solved_bound:                 -1
% 3.12/1.00  bmc1_unsat_core_size:                   -1
% 3.12/1.00  bmc1_unsat_core_parents_size:           -1
% 3.12/1.00  bmc1_merge_next_fun:                    0
% 3.12/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.12/1.00  
% 3.12/1.00  ------ Instantiation
% 3.12/1.00  
% 3.12/1.00  inst_num_of_clauses:                    531
% 3.12/1.00  inst_num_in_passive:                    102
% 3.12/1.00  inst_num_in_active:                     163
% 3.12/1.00  inst_num_in_unprocessed:                265
% 3.12/1.00  inst_num_of_loops:                      171
% 3.12/1.00  inst_num_of_learning_restarts:          0
% 3.12/1.00  inst_num_moves_active_passive:          6
% 3.12/1.00  inst_lit_activity:                      0
% 3.12/1.00  inst_lit_activity_moves:                0
% 3.12/1.00  inst_num_tautologies:                   0
% 3.12/1.00  inst_num_prop_implied:                  0
% 3.12/1.00  inst_num_existing_simplified:           0
% 3.12/1.00  inst_num_eq_res_simplified:             0
% 3.12/1.00  inst_num_child_elim:                    0
% 3.12/1.00  inst_num_of_dismatching_blockings:      241
% 3.12/1.00  inst_num_of_non_proper_insts:           463
% 3.12/1.00  inst_num_of_duplicates:                 0
% 3.12/1.00  inst_inst_num_from_inst_to_res:         0
% 3.12/1.00  inst_dismatching_checking_time:         0.
% 3.12/1.00  
% 3.12/1.00  ------ Resolution
% 3.12/1.00  
% 3.12/1.00  res_num_of_clauses:                     0
% 3.12/1.00  res_num_in_passive:                     0
% 3.12/1.00  res_num_in_active:                      0
% 3.12/1.00  res_num_of_loops:                       106
% 3.12/1.00  res_forward_subset_subsumed:            65
% 3.12/1.00  res_backward_subset_subsumed:           0
% 3.12/1.00  res_forward_subsumed:                   2
% 3.12/1.00  res_backward_subsumed:                  0
% 3.12/1.00  res_forward_subsumption_resolution:     0
% 3.12/1.00  res_backward_subsumption_resolution:    0
% 3.12/1.00  res_clause_to_clause_subsumption:       344
% 3.12/1.00  res_orphan_elimination:                 0
% 3.12/1.00  res_tautology_del:                      16
% 3.12/1.00  res_num_eq_res_simplified:              0
% 3.12/1.00  res_num_sel_changes:                    0
% 3.12/1.00  res_moves_from_active_to_pass:          0
% 3.12/1.00  
% 3.12/1.00  ------ Superposition
% 3.12/1.00  
% 3.12/1.00  sup_time_total:                         0.
% 3.12/1.00  sup_time_generating:                    0.
% 3.12/1.00  sup_time_sim_full:                      0.
% 3.12/1.00  sup_time_sim_immed:                     0.
% 3.12/1.00  
% 3.12/1.00  sup_num_of_clauses:                     87
% 3.12/1.00  sup_num_in_active:                      31
% 3.12/1.00  sup_num_in_passive:                     56
% 3.12/1.00  sup_num_of_loops:                       34
% 3.12/1.00  sup_fw_superposition:                   109
% 3.12/1.00  sup_bw_superposition:                   88
% 3.12/1.00  sup_immediate_simplified:               87
% 3.12/1.00  sup_given_eliminated:                   2
% 3.12/1.00  comparisons_done:                       0
% 3.12/1.00  comparisons_avoided:                    2
% 3.12/1.00  
% 3.12/1.00  ------ Simplifications
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  sim_fw_subset_subsumed:                 0
% 3.12/1.00  sim_bw_subset_subsumed:                 0
% 3.12/1.00  sim_fw_subsumed:                        14
% 3.12/1.00  sim_bw_subsumed:                        7
% 3.12/1.00  sim_fw_subsumption_res:                 0
% 3.12/1.00  sim_bw_subsumption_res:                 0
% 3.12/1.00  sim_tautology_del:                      0
% 3.12/1.00  sim_eq_tautology_del:                   26
% 3.12/1.00  sim_eq_res_simp:                        0
% 3.12/1.00  sim_fw_demodulated:                     34
% 3.12/1.00  sim_bw_demodulated:                     5
% 3.12/1.00  sim_light_normalised:                   56
% 3.12/1.00  sim_joinable_taut:                      0
% 3.12/1.00  sim_joinable_simp:                      0
% 3.12/1.00  sim_ac_normalised:                      0
% 3.12/1.00  sim_smt_subsumption:                    0
% 3.12/1.00  
%------------------------------------------------------------------------------
