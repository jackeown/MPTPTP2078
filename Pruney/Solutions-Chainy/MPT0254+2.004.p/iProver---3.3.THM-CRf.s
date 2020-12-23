%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:46 EST 2020

% Result     : Theorem 27.69s
% Output     : CNFRefutation 27.69s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 230 expanded)
%              Number of clauses        :   36 (  44 expanded)
%              Number of leaves         :   23 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  253 ( 463 expanded)
%              Number of equality atoms :  145 ( 330 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f22,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f22])).

fof(f25,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f23])).

fof(f34,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f34])).

fof(f67,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f72])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f69])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f70])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f86,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f67,f73,f76])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f73])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f13])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f91,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f84])).

fof(f92,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f91])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f72])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f85])).

cnf(c_226,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_70718,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_70893,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | r2_hidden(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(instantiation,[status(thm)],[c_70718])).

cnf(c_70895,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_70893])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_3,c_12,c_0])).

cnf(c_70802,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k1_xboole_0))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_70804,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
    | ~ r2_hidden(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_70802])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_70764,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_70765,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_70764])).

cnf(c_70733,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | r2_hidden(X2,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0))
    | X2 != X0
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(instantiation,[status(thm)],[c_70718])).

cnf(c_70735,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_70733])).

cnf(c_224,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_42865,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_224,c_5])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_54891,plain,
    ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))
    | ~ r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)),X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42865,c_21])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_223,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_43162,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_227,c_223])).

cnf(c_42872,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_224,c_223])).

cnf(c_43373,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42872,c_21])).

cnf(c_45672,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_43162,c_43373])).

cnf(c_57257,plain,
    ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))
    | X0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_54891,c_8,c_45672])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_57276,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57257,c_11])).

cnf(c_57280,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(resolution,[status(thm)],[c_57276,c_42872])).

cnf(c_19,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_26,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_70895,c_70804,c_70765,c_70735,c_57280,c_26,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:16:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 27.69/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.69/3.99  
% 27.69/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.69/3.99  
% 27.69/3.99  ------  iProver source info
% 27.69/3.99  
% 27.69/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.69/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.69/3.99  git: non_committed_changes: false
% 27.69/3.99  git: last_make_outside_of_git: false
% 27.69/3.99  
% 27.69/3.99  ------ 
% 27.69/3.99  ------ Parsing...
% 27.69/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  ------ Proving...
% 27.69/3.99  ------ Problem Properties 
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  clauses                                 21
% 27.69/3.99  conjectures                             1
% 27.69/3.99  EPR                                     3
% 27.69/3.99  Horn                                    16
% 27.69/3.99  unary                                   12
% 27.69/3.99  binary                                  0
% 27.69/3.99  lits                                    40
% 27.69/3.99  lits eq                                 16
% 27.69/3.99  fd_pure                                 0
% 27.69/3.99  fd_pseudo                               0
% 27.69/3.99  fd_cond                                 0
% 27.69/3.99  fd_pseudo_cond                          4
% 27.69/3.99  AC symbols                              1
% 27.69/3.99  
% 27.69/3.99  ------ Input Options Time Limit: Unbounded
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing...
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 27.69/3.99  Current options:
% 27.69/3.99  ------ 
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing...
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.69/3.99  
% 27.69/3.99  ------ Proving...
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  % SZS status Theorem for theBenchmark.p
% 27.69/3.99  
% 27.69/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.69/3.99  
% 27.69/3.99  fof(f2,axiom,(
% 27.69/3.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f24,plain,(
% 27.69/3.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 27.69/3.99    inference(ennf_transformation,[],[f2])).
% 27.69/3.99  
% 27.69/3.99  fof(f26,plain,(
% 27.69/3.99    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 27.69/3.99    inference(nnf_transformation,[],[f24])).
% 27.69/3.99  
% 27.69/3.99  fof(f38,plain,(
% 27.69/3.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 27.69/3.99    inference(cnf_transformation,[],[f26])).
% 27.69/3.99  
% 27.69/3.99  fof(f9,axiom,(
% 27.69/3.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f49,plain,(
% 27.69/3.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f9])).
% 27.69/3.99  
% 27.69/3.99  fof(f1,axiom,(
% 27.69/3.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f36,plain,(
% 27.69/3.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f1])).
% 27.69/3.99  
% 27.69/3.99  fof(f7,axiom,(
% 27.69/3.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f47,plain,(
% 27.69/3.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.69/3.99    inference(cnf_transformation,[],[f7])).
% 27.69/3.99  
% 27.69/3.99  fof(f3,axiom,(
% 27.69/3.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f27,plain,(
% 27.69/3.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.69/3.99    inference(nnf_transformation,[],[f3])).
% 27.69/3.99  
% 27.69/3.99  fof(f28,plain,(
% 27.69/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.69/3.99    inference(flattening,[],[f27])).
% 27.69/3.99  
% 27.69/3.99  fof(f43,plain,(
% 27.69/3.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f28])).
% 27.69/3.99  
% 27.69/3.99  fof(f22,conjecture,(
% 27.69/3.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f23,negated_conjecture,(
% 27.69/3.99    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 27.69/3.99    inference(negated_conjecture,[],[f22])).
% 27.69/3.99  
% 27.69/3.99  fof(f25,plain,(
% 27.69/3.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 27.69/3.99    inference(ennf_transformation,[],[f23])).
% 27.69/3.99  
% 27.69/3.99  fof(f34,plain,(
% 27.69/3.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 27.69/3.99    introduced(choice_axiom,[])).
% 27.69/3.99  
% 27.69/3.99  fof(f35,plain,(
% 27.69/3.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 27.69/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f34])).
% 27.69/3.99  
% 27.69/3.99  fof(f67,plain,(
% 27.69/3.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 27.69/3.99    inference(cnf_transformation,[],[f35])).
% 27.69/3.99  
% 27.69/3.99  fof(f21,axiom,(
% 27.69/3.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f66,plain,(
% 27.69/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 27.69/3.99    inference(cnf_transformation,[],[f21])).
% 27.69/3.99  
% 27.69/3.99  fof(f73,plain,(
% 27.69/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 27.69/3.99    inference(definition_unfolding,[],[f66,f72])).
% 27.69/3.99  
% 27.69/3.99  fof(f14,axiom,(
% 27.69/3.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f59,plain,(
% 27.69/3.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f14])).
% 27.69/3.99  
% 27.69/3.99  fof(f15,axiom,(
% 27.69/3.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f60,plain,(
% 27.69/3.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f15])).
% 27.69/3.99  
% 27.69/3.99  fof(f16,axiom,(
% 27.69/3.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f61,plain,(
% 27.69/3.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f16])).
% 27.69/3.99  
% 27.69/3.99  fof(f17,axiom,(
% 27.69/3.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f62,plain,(
% 27.69/3.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f17])).
% 27.69/3.99  
% 27.69/3.99  fof(f18,axiom,(
% 27.69/3.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f63,plain,(
% 27.69/3.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f18])).
% 27.69/3.99  
% 27.69/3.99  fof(f19,axiom,(
% 27.69/3.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f64,plain,(
% 27.69/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f19])).
% 27.69/3.99  
% 27.69/3.99  fof(f20,axiom,(
% 27.69/3.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f65,plain,(
% 27.69/3.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f20])).
% 27.69/3.99  
% 27.69/3.99  fof(f68,plain,(
% 27.69/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 27.69/3.99    inference(definition_unfolding,[],[f64,f65])).
% 27.69/3.99  
% 27.69/3.99  fof(f69,plain,(
% 27.69/3.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 27.69/3.99    inference(definition_unfolding,[],[f63,f68])).
% 27.69/3.99  
% 27.69/3.99  fof(f70,plain,(
% 27.69/3.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.69/3.99    inference(definition_unfolding,[],[f62,f69])).
% 27.69/3.99  
% 27.69/3.99  fof(f71,plain,(
% 27.69/3.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.69/3.99    inference(definition_unfolding,[],[f61,f70])).
% 27.69/3.99  
% 27.69/3.99  fof(f72,plain,(
% 27.69/3.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.69/3.99    inference(definition_unfolding,[],[f60,f71])).
% 27.69/3.99  
% 27.69/3.99  fof(f76,plain,(
% 27.69/3.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 27.69/3.99    inference(definition_unfolding,[],[f59,f72])).
% 27.69/3.99  
% 27.69/3.99  fof(f86,plain,(
% 27.69/3.99    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))),
% 27.69/3.99    inference(definition_unfolding,[],[f67,f73,f76])).
% 27.69/3.99  
% 27.69/3.99  fof(f5,axiom,(
% 27.69/3.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f45,plain,(
% 27.69/3.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.69/3.99    inference(cnf_transformation,[],[f5])).
% 27.69/3.99  
% 27.69/3.99  fof(f8,axiom,(
% 27.69/3.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f48,plain,(
% 27.69/3.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.69/3.99    inference(cnf_transformation,[],[f8])).
% 27.69/3.99  
% 27.69/3.99  fof(f78,plain,(
% 27.69/3.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 27.69/3.99    inference(definition_unfolding,[],[f48,f73])).
% 27.69/3.99  
% 27.69/3.99  fof(f13,axiom,(
% 27.69/3.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 27.69/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/3.99  
% 27.69/3.99  fof(f29,plain,(
% 27.69/3.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.69/3.99    inference(nnf_transformation,[],[f13])).
% 27.69/3.99  
% 27.69/3.99  fof(f30,plain,(
% 27.69/3.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.69/3.99    inference(flattening,[],[f29])).
% 27.69/3.99  
% 27.69/3.99  fof(f31,plain,(
% 27.69/3.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.69/3.99    inference(rectify,[],[f30])).
% 27.69/3.99  
% 27.69/3.99  fof(f32,plain,(
% 27.69/3.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 27.69/3.99    introduced(choice_axiom,[])).
% 27.69/3.99  
% 27.69/3.99  fof(f33,plain,(
% 27.69/3.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.69/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 27.69/3.99  
% 27.69/3.99  fof(f54,plain,(
% 27.69/3.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 27.69/3.99    inference(cnf_transformation,[],[f33])).
% 27.69/3.99  
% 27.69/3.99  fof(f84,plain,(
% 27.69/3.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 27.69/3.99    inference(definition_unfolding,[],[f54,f72])).
% 27.69/3.99  
% 27.69/3.99  fof(f91,plain,(
% 27.69/3.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 27.69/3.99    inference(equality_resolution,[],[f84])).
% 27.69/3.99  
% 27.69/3.99  fof(f92,plain,(
% 27.69/3.99    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 27.69/3.99    inference(equality_resolution,[],[f91])).
% 27.69/3.99  
% 27.69/3.99  fof(f53,plain,(
% 27.69/3.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 27.69/3.99    inference(cnf_transformation,[],[f33])).
% 27.69/3.99  
% 27.69/3.99  fof(f85,plain,(
% 27.69/3.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 27.69/3.99    inference(definition_unfolding,[],[f53,f72])).
% 27.69/3.99  
% 27.69/3.99  fof(f93,plain,(
% 27.69/3.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 27.69/3.99    inference(equality_resolution,[],[f85])).
% 27.69/3.99  
% 27.69/3.99  cnf(c_226,plain,
% 27.69/3.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.69/3.99      theory(equality) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_70718,plain,
% 27.69/3.99      ( r2_hidden(X0,X1)
% 27.69/3.99      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))
% 27.69/3.99      | X0 != X2
% 27.69/3.99      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2) ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_226]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_70893,plain,
% 27.69/3.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
% 27.69/3.99      | r2_hidden(X2,k1_xboole_0)
% 27.69/3.99      | X2 != X0
% 27.69/3.99      | k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_70718]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_70895,plain,
% 27.69/3.99      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 27.69/3.99      | r2_hidden(sK1,k1_xboole_0)
% 27.69/3.99      | sK1 != sK1
% 27.69/3.99      | k1_xboole_0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_70893]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_3,plain,
% 27.69/3.99      ( ~ r2_hidden(X0,X1)
% 27.69/3.99      | ~ r2_hidden(X0,X2)
% 27.69/3.99      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 27.69/3.99      inference(cnf_transformation,[],[f38]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_12,plain,
% 27.69/3.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 27.69/3.99      inference(cnf_transformation,[],[f49]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_0,plain,
% 27.69/3.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 27.69/3.99      inference(cnf_transformation,[],[f36]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_220,plain,
% 27.69/3.99      ( ~ r2_hidden(X0,X1)
% 27.69/3.99      | ~ r2_hidden(X0,X2)
% 27.69/3.99      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 27.69/3.99      inference(theory_normalisation,[status(thm)],[c_3,c_12,c_0]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_70802,plain,
% 27.69/3.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 27.69/3.99      | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k1_xboole_0))
% 27.69/3.99      | ~ r2_hidden(X0,k1_xboole_0) ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_220]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_70804,plain,
% 27.69/3.99      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 27.69/3.99      | ~ r2_hidden(sK1,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
% 27.69/3.99      | ~ r2_hidden(sK1,k1_xboole_0) ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_70802]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_10,plain,
% 27.69/3.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.69/3.99      inference(cnf_transformation,[],[f47]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_70764,plain,
% 27.69/3.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_10]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_70765,plain,
% 27.69/3.99      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_70764]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_70733,plain,
% 27.69/3.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
% 27.69/3.99      | r2_hidden(X2,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0))
% 27.69/3.99      | X2 != X0
% 27.69/3.99      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_70718]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_70735,plain,
% 27.69/3.99      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 27.69/3.99      | r2_hidden(sK1,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
% 27.69/3.99      | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 27.69/3.99      | sK1 != sK1 ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_70733]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_224,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_5,plain,
% 27.69/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.69/3.99      inference(cnf_transformation,[],[f43]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_42865,plain,
% 27.69/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 27.69/3.99      inference(resolution,[status(thm)],[c_224,c_5]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_21,negated_conjecture,
% 27.69/3.99      ( k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
% 27.69/3.99      inference(cnf_transformation,[],[f86]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_54891,plain,
% 27.69/3.99      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))
% 27.69/3.99      | ~ r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)),X0)
% 27.69/3.99      | X0 = k1_xboole_0 ),
% 27.69/3.99      inference(resolution,[status(thm)],[c_42865,c_21]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_8,plain,
% 27.69/3.99      ( r1_tarski(k1_xboole_0,X0) ),
% 27.69/3.99      inference(cnf_transformation,[],[f45]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_227,plain,
% 27.69/3.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.69/3.99      theory(equality) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_223,plain,( X0 = X0 ),theory(equality) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_43162,plain,
% 27.69/3.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 27.69/3.99      inference(resolution,[status(thm)],[c_227,c_223]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_42872,plain,
% 27.69/3.99      ( X0 != X1 | X1 = X0 ),
% 27.69/3.99      inference(resolution,[status(thm)],[c_224,c_223]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_43373,plain,
% 27.69/3.99      ( k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0 ),
% 27.69/3.99      inference(resolution,[status(thm)],[c_42872,c_21]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_45672,plain,
% 27.69/3.99      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)),X0)
% 27.69/3.99      | ~ r1_tarski(k1_xboole_0,X0) ),
% 27.69/3.99      inference(resolution,[status(thm)],[c_43162,c_43373]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_57257,plain,
% 27.69/3.99      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))
% 27.69/3.99      | X0 = k1_xboole_0 ),
% 27.69/3.99      inference(global_propositional_subsumption,
% 27.69/3.99                [status(thm)],
% 27.69/3.99                [c_54891,c_8,c_45672]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_11,plain,
% 27.69/3.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 27.69/3.99      inference(cnf_transformation,[],[f78]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_57276,plain,
% 27.69/3.99      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
% 27.69/3.99      inference(resolution,[status(thm)],[c_57257,c_11]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_57280,plain,
% 27.69/3.99      ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 27.69/3.99      inference(resolution,[status(thm)],[c_57276,c_42872]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_19,plain,
% 27.69/3.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 27.69/3.99      inference(cnf_transformation,[],[f92]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_26,plain,
% 27.69/3.99      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_19]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_20,plain,
% 27.69/3.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 27.69/3.99      | X0 = X1
% 27.69/3.99      | X0 = X2 ),
% 27.69/3.99      inference(cnf_transformation,[],[f93]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(c_23,plain,
% 27.69/3.99      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 27.69/3.99      | sK1 = sK1 ),
% 27.69/3.99      inference(instantiation,[status(thm)],[c_20]) ).
% 27.69/3.99  
% 27.69/3.99  cnf(contradiction,plain,
% 27.69/3.99      ( $false ),
% 27.69/3.99      inference(minisat,
% 27.69/3.99                [status(thm)],
% 27.69/3.99                [c_70895,c_70804,c_70765,c_70735,c_57280,c_26,c_23]) ).
% 27.69/3.99  
% 27.69/3.99  
% 27.69/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.69/3.99  
% 27.69/3.99  ------                               Statistics
% 27.69/3.99  
% 27.69/3.99  ------ Selected
% 27.69/3.99  
% 27.69/3.99  total_time:                             3.24
% 27.69/3.99  
%------------------------------------------------------------------------------
