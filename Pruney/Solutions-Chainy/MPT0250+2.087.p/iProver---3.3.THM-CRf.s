%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:57 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 284 expanded)
%              Number of clauses        :   40 (  62 expanded)
%              Number of leaves         :   17 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  295 ( 842 expanded)
%              Number of equality atoms :  143 ( 500 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f69,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f86,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f87,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f82,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f83,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f82])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK2,sK3)
      & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_hidden(sK2,sK3)
    & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f36])).

fof(f63,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) ),
    inference(definition_unfolding,[],[f63,f62,f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_303,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_726,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,X3),X4)
    | X4 != X1
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,X3) != X0 ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_966,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,X3),k3_tarski(X4))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,X3) != X0
    | k3_tarski(X4) != X1 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_2024,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,sK2) != X0
    | k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_3468,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X1,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,X1,sK2) != X0
    | k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_4212,plain,
    ( r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
    | ~ r1_tarski(k2_tarski(sK2,sK2),sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k2_tarski(sK2,sK2)
    | k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_3468])).

cnf(c_0,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_543,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_769,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_543])).

cnf(c_11,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_545,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_946,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_545])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_541,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_539,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_180,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_5,c_6])).

cnf(c_538,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1632,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3
    | r1_tarski(sK3,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_538])).

cnf(c_1690,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3
    | r2_hidden(sK3,k2_tarski(k2_tarski(sK2,sK2),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_1632])).

cnf(c_1693,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_946,c_1690])).

cnf(c_1720,plain,
    ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK2),sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_541])).

cnf(c_2076,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_769,c_1720])).

cnf(c_2081,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2076])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_580,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_625,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,X1,X2))
    | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X1,X2),X0) ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_721,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,X1))
    | r2_hidden(sK2,k3_tarski(X2))
    | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,X1),k3_tarski(X2)) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1009,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK2))
    | r2_hidden(sK2,k3_tarski(X1))
    | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK2),k3_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1672,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK2))
    | r2_hidden(sK2,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
    | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_1674,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
    | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_570,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,sK3)
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_875,plain,
    ( ~ r2_hidden(sK2,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
    | r2_hidden(sK2,sK3)
    | ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_56,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_31,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4212,c_2081,c_1693,c_1674,c_875,c_56,c_31,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:15:00 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.19/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/0.98  
% 3.19/0.98  ------  iProver source info
% 3.19/0.98  
% 3.19/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.19/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/0.98  git: non_committed_changes: false
% 3.19/0.98  git: last_make_outside_of_git: false
% 3.19/0.98  
% 3.19/0.98  ------ 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options
% 3.19/0.98  
% 3.19/0.98  --out_options                           all
% 3.19/0.98  --tptp_safe_out                         true
% 3.19/0.98  --problem_path                          ""
% 3.19/0.98  --include_path                          ""
% 3.19/0.98  --clausifier                            res/vclausify_rel
% 3.19/0.98  --clausifier_options                    ""
% 3.19/0.98  --stdin                                 false
% 3.19/0.98  --stats_out                             all
% 3.19/0.98  
% 3.19/0.98  ------ General Options
% 3.19/0.98  
% 3.19/0.98  --fof                                   false
% 3.19/0.98  --time_out_real                         305.
% 3.19/0.98  --time_out_virtual                      -1.
% 3.19/0.98  --symbol_type_check                     false
% 3.19/0.98  --clausify_out                          false
% 3.19/0.98  --sig_cnt_out                           false
% 3.19/0.98  --trig_cnt_out                          false
% 3.19/0.98  --trig_cnt_out_tolerance                1.
% 3.19/0.98  --trig_cnt_out_sk_spl                   false
% 3.19/0.98  --abstr_cl_out                          false
% 3.19/0.98  
% 3.19/0.98  ------ Global Options
% 3.19/0.98  
% 3.19/0.98  --schedule                              default
% 3.19/0.98  --add_important_lit                     false
% 3.19/0.98  --prop_solver_per_cl                    1000
% 3.19/0.98  --min_unsat_core                        false
% 3.19/0.98  --soft_assumptions                      false
% 3.19/0.98  --soft_lemma_size                       3
% 3.19/0.98  --prop_impl_unit_size                   0
% 3.19/0.98  --prop_impl_unit                        []
% 3.19/0.98  --share_sel_clauses                     true
% 3.19/0.98  --reset_solvers                         false
% 3.19/0.98  --bc_imp_inh                            [conj_cone]
% 3.19/0.98  --conj_cone_tolerance                   3.
% 3.19/0.98  --extra_neg_conj                        none
% 3.19/0.98  --large_theory_mode                     true
% 3.19/0.98  --prolific_symb_bound                   200
% 3.19/0.98  --lt_threshold                          2000
% 3.19/0.98  --clause_weak_htbl                      true
% 3.19/0.98  --gc_record_bc_elim                     false
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing Options
% 3.19/0.98  
% 3.19/0.98  --preprocessing_flag                    true
% 3.19/0.98  --time_out_prep_mult                    0.1
% 3.19/0.98  --splitting_mode                        input
% 3.19/0.98  --splitting_grd                         true
% 3.19/0.98  --splitting_cvd                         false
% 3.19/0.98  --splitting_cvd_svl                     false
% 3.19/0.98  --splitting_nvd                         32
% 3.19/0.98  --sub_typing                            true
% 3.19/0.98  --prep_gs_sim                           true
% 3.19/0.98  --prep_unflatten                        true
% 3.19/0.98  --prep_res_sim                          true
% 3.19/0.98  --prep_upred                            true
% 3.19/0.98  --prep_sem_filter                       exhaustive
% 3.19/0.98  --prep_sem_filter_out                   false
% 3.19/0.98  --pred_elim                             true
% 3.19/0.98  --res_sim_input                         true
% 3.19/0.98  --eq_ax_congr_red                       true
% 3.19/0.98  --pure_diseq_elim                       true
% 3.19/0.98  --brand_transform                       false
% 3.19/0.98  --non_eq_to_eq                          false
% 3.19/0.98  --prep_def_merge                        true
% 3.19/0.98  --prep_def_merge_prop_impl              false
% 3.19/0.98  --prep_def_merge_mbd                    true
% 3.19/0.98  --prep_def_merge_tr_red                 false
% 3.19/0.98  --prep_def_merge_tr_cl                  false
% 3.19/0.98  --smt_preprocessing                     true
% 3.19/0.98  --smt_ac_axioms                         fast
% 3.19/0.98  --preprocessed_out                      false
% 3.19/0.98  --preprocessed_stats                    false
% 3.19/0.98  
% 3.19/0.98  ------ Abstraction refinement Options
% 3.19/0.98  
% 3.19/0.98  --abstr_ref                             []
% 3.19/0.98  --abstr_ref_prep                        false
% 3.19/0.98  --abstr_ref_until_sat                   false
% 3.19/0.98  --abstr_ref_sig_restrict                funpre
% 3.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.98  --abstr_ref_under                       []
% 3.19/0.98  
% 3.19/0.98  ------ SAT Options
% 3.19/0.98  
% 3.19/0.98  --sat_mode                              false
% 3.19/0.98  --sat_fm_restart_options                ""
% 3.19/0.98  --sat_gr_def                            false
% 3.19/0.98  --sat_epr_types                         true
% 3.19/0.98  --sat_non_cyclic_types                  false
% 3.19/0.98  --sat_finite_models                     false
% 3.19/0.98  --sat_fm_lemmas                         false
% 3.19/0.98  --sat_fm_prep                           false
% 3.19/0.98  --sat_fm_uc_incr                        true
% 3.19/0.98  --sat_out_model                         small
% 3.19/0.98  --sat_out_clauses                       false
% 3.19/0.98  
% 3.19/0.98  ------ QBF Options
% 3.19/0.98  
% 3.19/0.98  --qbf_mode                              false
% 3.19/0.98  --qbf_elim_univ                         false
% 3.19/0.98  --qbf_dom_inst                          none
% 3.19/0.98  --qbf_dom_pre_inst                      false
% 3.19/0.98  --qbf_sk_in                             false
% 3.19/0.98  --qbf_pred_elim                         true
% 3.19/0.98  --qbf_split                             512
% 3.19/0.98  
% 3.19/0.98  ------ BMC1 Options
% 3.19/0.98  
% 3.19/0.98  --bmc1_incremental                      false
% 3.19/0.98  --bmc1_axioms                           reachable_all
% 3.19/0.98  --bmc1_min_bound                        0
% 3.19/0.98  --bmc1_max_bound                        -1
% 3.19/0.98  --bmc1_max_bound_default                -1
% 3.19/0.98  --bmc1_symbol_reachability              true
% 3.19/0.98  --bmc1_property_lemmas                  false
% 3.19/0.98  --bmc1_k_induction                      false
% 3.19/0.98  --bmc1_non_equiv_states                 false
% 3.19/0.98  --bmc1_deadlock                         false
% 3.19/0.98  --bmc1_ucm                              false
% 3.19/0.98  --bmc1_add_unsat_core                   none
% 3.19/0.98  --bmc1_unsat_core_children              false
% 3.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.98  --bmc1_out_stat                         full
% 3.19/0.98  --bmc1_ground_init                      false
% 3.19/0.98  --bmc1_pre_inst_next_state              false
% 3.19/0.98  --bmc1_pre_inst_state                   false
% 3.19/0.98  --bmc1_pre_inst_reach_state             false
% 3.19/0.98  --bmc1_out_unsat_core                   false
% 3.19/0.98  --bmc1_aig_witness_out                  false
% 3.19/0.98  --bmc1_verbose                          false
% 3.19/0.98  --bmc1_dump_clauses_tptp                false
% 3.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.98  --bmc1_dump_file                        -
% 3.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.98  --bmc1_ucm_extend_mode                  1
% 3.19/0.98  --bmc1_ucm_init_mode                    2
% 3.19/0.98  --bmc1_ucm_cone_mode                    none
% 3.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.98  --bmc1_ucm_relax_model                  4
% 3.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.98  --bmc1_ucm_layered_model                none
% 3.19/0.98  --bmc1_ucm_max_lemma_size               10
% 3.19/0.98  
% 3.19/0.98  ------ AIG Options
% 3.19/0.98  
% 3.19/0.98  --aig_mode                              false
% 3.19/0.98  
% 3.19/0.98  ------ Instantiation Options
% 3.19/0.98  
% 3.19/0.98  --instantiation_flag                    true
% 3.19/0.98  --inst_sos_flag                         true
% 3.19/0.98  --inst_sos_phase                        true
% 3.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel_side                     num_symb
% 3.19/0.98  --inst_solver_per_active                1400
% 3.19/0.98  --inst_solver_calls_frac                1.
% 3.19/0.98  --inst_passive_queue_type               priority_queues
% 3.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.98  --inst_passive_queues_freq              [25;2]
% 3.19/0.98  --inst_dismatching                      true
% 3.19/0.98  --inst_eager_unprocessed_to_passive     true
% 3.19/0.98  --inst_prop_sim_given                   true
% 3.19/0.98  --inst_prop_sim_new                     false
% 3.19/0.98  --inst_subs_new                         false
% 3.19/0.98  --inst_eq_res_simp                      false
% 3.19/0.98  --inst_subs_given                       false
% 3.19/0.98  --inst_orphan_elimination               true
% 3.19/0.98  --inst_learning_loop_flag               true
% 3.19/0.98  --inst_learning_start                   3000
% 3.19/0.98  --inst_learning_factor                  2
% 3.19/0.98  --inst_start_prop_sim_after_learn       3
% 3.19/0.98  --inst_sel_renew                        solver
% 3.19/0.98  --inst_lit_activity_flag                true
% 3.19/0.98  --inst_restr_to_given                   false
% 3.19/0.98  --inst_activity_threshold               500
% 3.19/0.98  --inst_out_proof                        true
% 3.19/0.98  
% 3.19/0.98  ------ Resolution Options
% 3.19/0.98  
% 3.19/0.98  --resolution_flag                       true
% 3.19/0.98  --res_lit_sel                           adaptive
% 3.19/0.98  --res_lit_sel_side                      none
% 3.19/0.98  --res_ordering                          kbo
% 3.19/0.98  --res_to_prop_solver                    active
% 3.19/0.98  --res_prop_simpl_new                    false
% 3.19/0.98  --res_prop_simpl_given                  true
% 3.19/0.98  --res_passive_queue_type                priority_queues
% 3.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.98  --res_passive_queues_freq               [15;5]
% 3.19/0.98  --res_forward_subs                      full
% 3.19/0.98  --res_backward_subs                     full
% 3.19/0.98  --res_forward_subs_resolution           true
% 3.19/0.98  --res_backward_subs_resolution          true
% 3.19/0.98  --res_orphan_elimination                true
% 3.19/0.98  --res_time_limit                        2.
% 3.19/0.98  --res_out_proof                         true
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Options
% 3.19/0.98  
% 3.19/0.98  --superposition_flag                    true
% 3.19/0.98  --sup_passive_queue_type                priority_queues
% 3.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.98  --demod_completeness_check              fast
% 3.19/0.98  --demod_use_ground                      true
% 3.19/0.98  --sup_to_prop_solver                    passive
% 3.19/0.98  --sup_prop_simpl_new                    true
% 3.19/0.98  --sup_prop_simpl_given                  true
% 3.19/0.98  --sup_fun_splitting                     true
% 3.19/0.98  --sup_smt_interval                      50000
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Simplification Setup
% 3.19/0.98  
% 3.19/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.19/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.19/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.19/0.98  --sup_immed_triv                        [TrivRules]
% 3.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_bw_main                     []
% 3.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_input_bw                          []
% 3.19/0.98  
% 3.19/0.98  ------ Combination Options
% 3.19/0.98  
% 3.19/0.98  --comb_res_mult                         3
% 3.19/0.98  --comb_sup_mult                         2
% 3.19/0.98  --comb_inst_mult                        10
% 3.19/0.98  
% 3.19/0.98  ------ Debug Options
% 3.19/0.98  
% 3.19/0.98  --dbg_backtrace                         false
% 3.19/0.98  --dbg_dump_prop_clauses                 false
% 3.19/0.98  --dbg_dump_prop_clauses_file            -
% 3.19/0.98  --dbg_out_stat                          false
% 3.19/0.98  ------ Parsing...
% 3.19/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/0.98  ------ Proving...
% 3.19/0.98  ------ Problem Properties 
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  clauses                                 19
% 3.19/0.98  conjectures                             2
% 3.19/0.98  EPR                                     3
% 3.19/0.98  Horn                                    16
% 3.19/0.98  unary                                   9
% 3.19/0.98  binary                                  3
% 3.19/0.98  lits                                    39
% 3.19/0.98  lits eq                                 18
% 3.19/0.98  fd_pure                                 0
% 3.19/0.98  fd_pseudo                               0
% 3.19/0.98  fd_cond                                 0
% 3.19/0.98  fd_pseudo_cond                          5
% 3.19/0.98  AC symbols                              0
% 3.19/0.98  
% 3.19/0.98  ------ Schedule dynamic 5 is on 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  ------ 
% 3.19/0.98  Current options:
% 3.19/0.98  ------ 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options
% 3.19/0.98  
% 3.19/0.98  --out_options                           all
% 3.19/0.98  --tptp_safe_out                         true
% 3.19/0.98  --problem_path                          ""
% 3.19/0.98  --include_path                          ""
% 3.19/0.98  --clausifier                            res/vclausify_rel
% 3.19/0.98  --clausifier_options                    ""
% 3.19/0.98  --stdin                                 false
% 3.19/0.98  --stats_out                             all
% 3.19/0.98  
% 3.19/0.98  ------ General Options
% 3.19/0.98  
% 3.19/0.98  --fof                                   false
% 3.19/0.98  --time_out_real                         305.
% 3.19/0.98  --time_out_virtual                      -1.
% 3.19/0.98  --symbol_type_check                     false
% 3.19/0.98  --clausify_out                          false
% 3.19/0.98  --sig_cnt_out                           false
% 3.19/0.98  --trig_cnt_out                          false
% 3.19/0.98  --trig_cnt_out_tolerance                1.
% 3.19/0.98  --trig_cnt_out_sk_spl                   false
% 3.19/0.98  --abstr_cl_out                          false
% 3.19/0.98  
% 3.19/0.98  ------ Global Options
% 3.19/0.98  
% 3.19/0.98  --schedule                              default
% 3.19/0.98  --add_important_lit                     false
% 3.19/0.98  --prop_solver_per_cl                    1000
% 3.19/0.98  --min_unsat_core                        false
% 3.19/0.98  --soft_assumptions                      false
% 3.19/0.98  --soft_lemma_size                       3
% 3.19/0.98  --prop_impl_unit_size                   0
% 3.19/0.98  --prop_impl_unit                        []
% 3.19/0.98  --share_sel_clauses                     true
% 3.19/0.98  --reset_solvers                         false
% 3.19/0.98  --bc_imp_inh                            [conj_cone]
% 3.19/0.98  --conj_cone_tolerance                   3.
% 3.19/0.98  --extra_neg_conj                        none
% 3.19/0.98  --large_theory_mode                     true
% 3.19/0.98  --prolific_symb_bound                   200
% 3.19/0.98  --lt_threshold                          2000
% 3.19/0.98  --clause_weak_htbl                      true
% 3.19/0.98  --gc_record_bc_elim                     false
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing Options
% 3.19/0.98  
% 3.19/0.98  --preprocessing_flag                    true
% 3.19/0.98  --time_out_prep_mult                    0.1
% 3.19/0.98  --splitting_mode                        input
% 3.19/0.98  --splitting_grd                         true
% 3.19/0.98  --splitting_cvd                         false
% 3.19/0.98  --splitting_cvd_svl                     false
% 3.19/0.98  --splitting_nvd                         32
% 3.19/0.98  --sub_typing                            true
% 3.19/0.98  --prep_gs_sim                           true
% 3.19/0.98  --prep_unflatten                        true
% 3.19/0.98  --prep_res_sim                          true
% 3.19/0.98  --prep_upred                            true
% 3.19/0.98  --prep_sem_filter                       exhaustive
% 3.19/0.98  --prep_sem_filter_out                   false
% 3.19/0.98  --pred_elim                             true
% 3.19/0.98  --res_sim_input                         true
% 3.19/0.98  --eq_ax_congr_red                       true
% 3.19/0.98  --pure_diseq_elim                       true
% 3.19/0.98  --brand_transform                       false
% 3.19/0.98  --non_eq_to_eq                          false
% 3.19/0.98  --prep_def_merge                        true
% 3.19/0.98  --prep_def_merge_prop_impl              false
% 3.19/0.98  --prep_def_merge_mbd                    true
% 3.19/0.98  --prep_def_merge_tr_red                 false
% 3.19/0.98  --prep_def_merge_tr_cl                  false
% 3.19/0.98  --smt_preprocessing                     true
% 3.19/0.98  --smt_ac_axioms                         fast
% 3.19/0.98  --preprocessed_out                      false
% 3.19/0.98  --preprocessed_stats                    false
% 3.19/0.98  
% 3.19/0.98  ------ Abstraction refinement Options
% 3.19/0.98  
% 3.19/0.98  --abstr_ref                             []
% 3.19/0.98  --abstr_ref_prep                        false
% 3.19/0.98  --abstr_ref_until_sat                   false
% 3.19/0.98  --abstr_ref_sig_restrict                funpre
% 3.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.98  --abstr_ref_under                       []
% 3.19/0.98  
% 3.19/0.98  ------ SAT Options
% 3.19/0.98  
% 3.19/0.98  --sat_mode                              false
% 3.19/0.98  --sat_fm_restart_options                ""
% 3.19/0.98  --sat_gr_def                            false
% 3.19/0.98  --sat_epr_types                         true
% 3.19/0.98  --sat_non_cyclic_types                  false
% 3.19/0.98  --sat_finite_models                     false
% 3.19/0.98  --sat_fm_lemmas                         false
% 3.19/0.98  --sat_fm_prep                           false
% 3.19/0.98  --sat_fm_uc_incr                        true
% 3.19/0.98  --sat_out_model                         small
% 3.19/0.98  --sat_out_clauses                       false
% 3.19/0.98  
% 3.19/0.98  ------ QBF Options
% 3.19/0.98  
% 3.19/0.98  --qbf_mode                              false
% 3.19/0.98  --qbf_elim_univ                         false
% 3.19/0.98  --qbf_dom_inst                          none
% 3.19/0.98  --qbf_dom_pre_inst                      false
% 3.19/0.98  --qbf_sk_in                             false
% 3.19/0.98  --qbf_pred_elim                         true
% 3.19/0.98  --qbf_split                             512
% 3.19/0.98  
% 3.19/0.98  ------ BMC1 Options
% 3.19/0.98  
% 3.19/0.98  --bmc1_incremental                      false
% 3.19/0.98  --bmc1_axioms                           reachable_all
% 3.19/0.98  --bmc1_min_bound                        0
% 3.19/0.98  --bmc1_max_bound                        -1
% 3.19/0.98  --bmc1_max_bound_default                -1
% 3.19/0.98  --bmc1_symbol_reachability              true
% 3.19/0.98  --bmc1_property_lemmas                  false
% 3.19/0.98  --bmc1_k_induction                      false
% 3.19/0.98  --bmc1_non_equiv_states                 false
% 3.19/0.98  --bmc1_deadlock                         false
% 3.19/0.98  --bmc1_ucm                              false
% 3.19/0.98  --bmc1_add_unsat_core                   none
% 3.19/0.98  --bmc1_unsat_core_children              false
% 3.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.98  --bmc1_out_stat                         full
% 3.19/0.98  --bmc1_ground_init                      false
% 3.19/0.98  --bmc1_pre_inst_next_state              false
% 3.19/0.98  --bmc1_pre_inst_state                   false
% 3.19/0.98  --bmc1_pre_inst_reach_state             false
% 3.19/0.98  --bmc1_out_unsat_core                   false
% 3.19/0.98  --bmc1_aig_witness_out                  false
% 3.19/0.98  --bmc1_verbose                          false
% 3.19/0.98  --bmc1_dump_clauses_tptp                false
% 3.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.98  --bmc1_dump_file                        -
% 3.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.98  --bmc1_ucm_extend_mode                  1
% 3.19/0.98  --bmc1_ucm_init_mode                    2
% 3.19/0.98  --bmc1_ucm_cone_mode                    none
% 3.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.98  --bmc1_ucm_relax_model                  4
% 3.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.98  --bmc1_ucm_layered_model                none
% 3.19/0.98  --bmc1_ucm_max_lemma_size               10
% 3.19/0.98  
% 3.19/0.98  ------ AIG Options
% 3.19/0.98  
% 3.19/0.98  --aig_mode                              false
% 3.19/0.98  
% 3.19/0.98  ------ Instantiation Options
% 3.19/0.98  
% 3.19/0.98  --instantiation_flag                    true
% 3.19/0.98  --inst_sos_flag                         true
% 3.19/0.98  --inst_sos_phase                        true
% 3.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel_side                     none
% 3.19/0.98  --inst_solver_per_active                1400
% 3.19/0.98  --inst_solver_calls_frac                1.
% 3.19/0.98  --inst_passive_queue_type               priority_queues
% 3.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.98  --inst_passive_queues_freq              [25;2]
% 3.19/0.98  --inst_dismatching                      true
% 3.19/0.98  --inst_eager_unprocessed_to_passive     true
% 3.19/0.98  --inst_prop_sim_given                   true
% 3.19/0.98  --inst_prop_sim_new                     false
% 3.19/0.98  --inst_subs_new                         false
% 3.19/0.98  --inst_eq_res_simp                      false
% 3.19/0.98  --inst_subs_given                       false
% 3.19/0.98  --inst_orphan_elimination               true
% 3.19/0.98  --inst_learning_loop_flag               true
% 3.19/0.98  --inst_learning_start                   3000
% 3.19/0.98  --inst_learning_factor                  2
% 3.19/0.98  --inst_start_prop_sim_after_learn       3
% 3.19/0.98  --inst_sel_renew                        solver
% 3.19/0.98  --inst_lit_activity_flag                true
% 3.19/0.98  --inst_restr_to_given                   false
% 3.19/0.98  --inst_activity_threshold               500
% 3.19/0.98  --inst_out_proof                        true
% 3.19/0.98  
% 3.19/0.98  ------ Resolution Options
% 3.19/0.98  
% 3.19/0.98  --resolution_flag                       false
% 3.19/0.98  --res_lit_sel                           adaptive
% 3.19/0.98  --res_lit_sel_side                      none
% 3.19/0.98  --res_ordering                          kbo
% 3.19/0.98  --res_to_prop_solver                    active
% 3.19/0.98  --res_prop_simpl_new                    false
% 3.19/0.98  --res_prop_simpl_given                  true
% 3.19/0.98  --res_passive_queue_type                priority_queues
% 3.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.98  --res_passive_queues_freq               [15;5]
% 3.19/0.98  --res_forward_subs                      full
% 3.19/0.98  --res_backward_subs                     full
% 3.19/0.98  --res_forward_subs_resolution           true
% 3.19/0.98  --res_backward_subs_resolution          true
% 3.19/0.98  --res_orphan_elimination                true
% 3.19/0.98  --res_time_limit                        2.
% 3.19/0.98  --res_out_proof                         true
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Options
% 3.19/0.98  
% 3.19/0.98  --superposition_flag                    true
% 3.19/0.98  --sup_passive_queue_type                priority_queues
% 3.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.98  --demod_completeness_check              fast
% 3.19/0.98  --demod_use_ground                      true
% 3.19/0.98  --sup_to_prop_solver                    passive
% 3.19/0.98  --sup_prop_simpl_new                    true
% 3.19/0.98  --sup_prop_simpl_given                  true
% 3.19/0.98  --sup_fun_splitting                     true
% 3.19/0.98  --sup_smt_interval                      50000
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Simplification Setup
% 3.19/0.98  
% 3.19/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.19/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.19/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.19/0.98  --sup_immed_triv                        [TrivRules]
% 3.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_bw_main                     []
% 3.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_input_bw                          []
% 3.19/0.98  
% 3.19/0.98  ------ Combination Options
% 3.19/0.98  
% 3.19/0.98  --comb_res_mult                         3
% 3.19/0.98  --comb_sup_mult                         2
% 3.19/0.98  --comb_inst_mult                        10
% 3.19/0.98  
% 3.19/0.98  ------ Debug Options
% 3.19/0.98  
% 3.19/0.98  --dbg_backtrace                         false
% 3.19/0.98  --dbg_dump_prop_clauses                 false
% 3.19/0.98  --dbg_dump_prop_clauses_file            -
% 3.19/0.98  --dbg_out_stat                          false
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  ------ Proving...
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  % SZS status Theorem for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  fof(f9,axiom,(
% 3.19/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f55,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f9])).
% 3.19/0.98  
% 3.19/0.98  fof(f10,axiom,(
% 3.19/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f56,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f10])).
% 3.19/0.98  
% 3.19/0.98  fof(f11,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f57,plain,(
% 3.19/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f11])).
% 3.19/0.98  
% 3.19/0.98  fof(f12,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f58,plain,(
% 3.19/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f12])).
% 3.19/0.98  
% 3.19/0.98  fof(f13,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f59,plain,(
% 3.19/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f13])).
% 3.19/0.98  
% 3.19/0.98  fof(f65,plain,(
% 3.19/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f58,f59])).
% 3.19/0.98  
% 3.19/0.98  fof(f66,plain,(
% 3.19/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f57,f65])).
% 3.19/0.98  
% 3.19/0.98  fof(f67,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f56,f66])).
% 3.19/0.98  
% 3.19/0.98  fof(f69,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f55,f67])).
% 3.19/0.98  
% 3.19/0.98  fof(f4,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f24,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.19/0.98    inference(ennf_transformation,[],[f4])).
% 3.19/0.98  
% 3.19/0.98  fof(f31,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.19/0.98    inference(nnf_transformation,[],[f24])).
% 3.19/0.98  
% 3.19/0.98  fof(f32,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.19/0.98    inference(flattening,[],[f31])).
% 3.19/0.98  
% 3.19/0.98  fof(f33,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.19/0.98    inference(rectify,[],[f32])).
% 3.19/0.98  
% 3.19/0.98  fof(f34,plain,(
% 3.19/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f35,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.19/0.98  
% 3.19/0.98  fof(f44,plain,(
% 3.19/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.19/0.98    inference(cnf_transformation,[],[f35])).
% 3.19/0.98  
% 3.19/0.98  fof(f77,plain,(
% 3.19/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.19/0.98    inference(definition_unfolding,[],[f44,f67])).
% 3.19/0.98  
% 3.19/0.98  fof(f86,plain,(
% 3.19/0.98    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.19/0.98    inference(equality_resolution,[],[f77])).
% 3.19/0.98  
% 3.19/0.98  fof(f87,plain,(
% 3.19/0.98    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 3.19/0.98    inference(equality_resolution,[],[f86])).
% 3.19/0.98  
% 3.19/0.98  fof(f46,plain,(
% 3.19/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.19/0.98    inference(cnf_transformation,[],[f35])).
% 3.19/0.98  
% 3.19/0.98  fof(f75,plain,(
% 3.19/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.19/0.98    inference(definition_unfolding,[],[f46,f67])).
% 3.19/0.98  
% 3.19/0.98  fof(f82,plain,(
% 3.19/0.98    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 3.19/0.98    inference(equality_resolution,[],[f75])).
% 3.19/0.98  
% 3.19/0.98  fof(f83,plain,(
% 3.19/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 3.19/0.98    inference(equality_resolution,[],[f82])).
% 3.19/0.98  
% 3.19/0.98  fof(f15,axiom,(
% 3.19/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f25,plain,(
% 3.19/0.98    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 3.19/0.98    inference(ennf_transformation,[],[f15])).
% 3.19/0.98  
% 3.19/0.98  fof(f61,plain,(
% 3.19/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f25])).
% 3.19/0.98  
% 3.19/0.98  fof(f17,conjecture,(
% 3.19/0.98    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f18,negated_conjecture,(
% 3.19/0.98    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.19/0.98    inference(negated_conjecture,[],[f17])).
% 3.19/0.98  
% 3.19/0.98  fof(f26,plain,(
% 3.19/0.98    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 3.19/0.98    inference(ennf_transformation,[],[f18])).
% 3.19/0.98  
% 3.19/0.98  fof(f36,plain,(
% 3.19/0.98    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3))),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f37,plain,(
% 3.19/0.98    ~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 3.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f36])).
% 3.19/0.98  
% 3.19/0.98  fof(f63,plain,(
% 3.19/0.98    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 3.19/0.98    inference(cnf_transformation,[],[f37])).
% 3.19/0.98  
% 3.19/0.98  fof(f16,axiom,(
% 3.19/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f62,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f16])).
% 3.19/0.98  
% 3.19/0.98  fof(f8,axiom,(
% 3.19/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f54,plain,(
% 3.19/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f8])).
% 3.19/0.98  
% 3.19/0.98  fof(f81,plain,(
% 3.19/0.98    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3)),
% 3.19/0.98    inference(definition_unfolding,[],[f63,f62,f54])).
% 3.19/0.98  
% 3.19/0.98  fof(f2,axiom,(
% 3.19/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f19,plain,(
% 3.19/0.98    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 3.19/0.98    inference(unused_predicate_definition_removal,[],[f2])).
% 3.19/0.98  
% 3.19/0.98  fof(f21,plain,(
% 3.19/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 3.19/0.98    inference(ennf_transformation,[],[f19])).
% 3.19/0.98  
% 3.19/0.98  fof(f22,plain,(
% 3.19/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.19/0.98    inference(flattening,[],[f21])).
% 3.19/0.98  
% 3.19/0.98  fof(f41,plain,(
% 3.19/0.98    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f22])).
% 3.19/0.98  
% 3.19/0.98  fof(f3,axiom,(
% 3.19/0.98    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f23,plain,(
% 3.19/0.98    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 3.19/0.98    inference(ennf_transformation,[],[f3])).
% 3.19/0.98  
% 3.19/0.98  fof(f42,plain,(
% 3.19/0.98    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f23])).
% 3.19/0.98  
% 3.19/0.98  fof(f1,axiom,(
% 3.19/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f20,plain,(
% 3.19/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f1])).
% 3.19/0.98  
% 3.19/0.98  fof(f27,plain,(
% 3.19/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.19/0.98    inference(nnf_transformation,[],[f20])).
% 3.19/0.98  
% 3.19/0.98  fof(f28,plain,(
% 3.19/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.19/0.98    inference(rectify,[],[f27])).
% 3.19/0.98  
% 3.19/0.98  fof(f29,plain,(
% 3.19/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f30,plain,(
% 3.19/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.19/0.98  
% 3.19/0.98  fof(f38,plain,(
% 3.19/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f30])).
% 3.19/0.98  
% 3.19/0.98  fof(f64,plain,(
% 3.19/0.98    ~r2_hidden(sK2,sK3)),
% 3.19/0.98    inference(cnf_transformation,[],[f37])).
% 3.19/0.98  
% 3.19/0.98  cnf(c_303,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.19/0.98      theory(equality) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_726,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1)
% 3.19/0.98      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,X3),X4)
% 3.19/0.98      | X4 != X1
% 3.19/0.98      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,X3) != X0 ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_303]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_966,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1)
% 3.19/0.98      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,X3),k3_tarski(X4))
% 3.19/0.98      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,X3) != X0
% 3.19/0.98      | k3_tarski(X4) != X1 ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_726]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2024,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1)
% 3.19/0.98      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
% 3.19/0.98      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,X2,sK2) != X0
% 3.19/0.98      | k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) != X1 ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_966]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3468,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,sK3)
% 3.19/0.98      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X1,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
% 3.19/0.98      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,X1,sK2) != X0
% 3.19/0.98      | k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) != sK3 ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_2024]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4212,plain,
% 3.19/0.98      ( r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
% 3.19/0.98      | ~ r1_tarski(k2_tarski(sK2,sK2),sK3)
% 3.19/0.98      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k2_tarski(sK2,sK2)
% 3.19/0.98      | k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) != sK3 ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_3468]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_0,plain,
% 3.19/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_13,plain,
% 3.19/0.98      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_543,plain,
% 3.19/0.98      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_769,plain,
% 3.19/0.98      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_0,c_543]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_11,plain,
% 3.19/0.98      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_545,plain,
% 3.19/0.98      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_946,plain,
% 3.19/0.98      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_0,c_545]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_17,plain,
% 3.19/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_541,plain,
% 3.19/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.19/0.98      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_19,negated_conjecture,
% 3.19/0.98      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) ),
% 3.19/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_539,plain,
% 3.19/0.98      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_5,plain,
% 3.19/0.98      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_6,plain,
% 3.19/0.98      ( ~ r2_xboole_0(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_180,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_5,c_6]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_538,plain,
% 3.19/0.98      ( X0 = X1
% 3.19/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.19/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1632,plain,
% 3.19/0.98      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3
% 3.19/0.98      | r1_tarski(sK3,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3))) != iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_539,c_538]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1690,plain,
% 3.19/0.98      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3
% 3.19/0.98      | r2_hidden(sK3,k2_tarski(k2_tarski(sK2,sK2),sK3)) != iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_541,c_1632]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1693,plain,
% 3.19/0.98      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)) = sK3 ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_946,c_1690]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1720,plain,
% 3.19/0.98      ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK2),sK3)) != iProver_top
% 3.19/0.98      | r1_tarski(X0,sK3) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_1693,c_541]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2076,plain,
% 3.19/0.98      ( r1_tarski(k2_tarski(sK2,sK2),sK3) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_769,c_1720]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2081,plain,
% 3.19/0.98      ( r1_tarski(k2_tarski(sK2,sK2),sK3) ),
% 3.19/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2076]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4,plain,
% 3.19/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.19/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_580,plain,
% 3.19/0.98      ( ~ r2_hidden(sK2,X0) | r2_hidden(sK2,X1) | ~ r1_tarski(X0,X1) ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_625,plain,
% 3.19/0.98      ( r2_hidden(sK2,X0)
% 3.19/0.98      | ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,X1,X2))
% 3.19/0.98      | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X1,X2),X0) ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_580]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_721,plain,
% 3.19/0.98      ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,X1))
% 3.19/0.98      | r2_hidden(sK2,k3_tarski(X2))
% 3.19/0.98      | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,X1),k3_tarski(X2)) ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_625]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1009,plain,
% 3.19/0.99      ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK2))
% 3.19/0.99      | r2_hidden(sK2,k3_tarski(X1))
% 3.19/0.99      | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK2),k3_tarski(X1)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_721]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1672,plain,
% 3.19/0.99      ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK2))
% 3.19/0.99      | r2_hidden(sK2,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
% 3.19/0.99      | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3))) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1009]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1674,plain,
% 3.19/0.99      ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.19/0.99      | r2_hidden(sK2,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
% 3.19/0.99      | ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3))) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1672]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_570,plain,
% 3.19/0.99      ( ~ r2_hidden(sK2,X0) | r2_hidden(sK2,sK3) | ~ r1_tarski(X0,sK3) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_875,plain,
% 3.19/0.99      ( ~ r2_hidden(sK2,k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)))
% 3.19/0.99      | r2_hidden(sK2,sK3)
% 3.19/0.99      | ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK3)),sK3) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_570]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_56,plain,
% 3.19/0.99      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k2_tarski(sK2,sK2) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_31,plain,
% 3.19/0.99      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_18,negated_conjecture,
% 3.19/0.99      ( ~ r2_hidden(sK2,sK3) ),
% 3.19/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(contradiction,plain,
% 3.19/0.99      ( $false ),
% 3.19/0.99      inference(minisat,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_4212,c_2081,c_1693,c_1674,c_875,c_56,c_31,c_18,c_19]) ).
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  ------                               Statistics
% 3.19/0.99  
% 3.19/0.99  ------ General
% 3.19/0.99  
% 3.19/0.99  abstr_ref_over_cycles:                  0
% 3.19/0.99  abstr_ref_under_cycles:                 0
% 3.19/0.99  gc_basic_clause_elim:                   0
% 3.19/0.99  forced_gc_time:                         0
% 3.19/0.99  parsing_time:                           0.008
% 3.19/0.99  unif_index_cands_time:                  0.
% 3.19/0.99  unif_index_add_time:                    0.
% 3.19/0.99  orderings_time:                         0.
% 3.19/0.99  out_proof_time:                         0.007
% 3.19/0.99  total_time:                             0.171
% 3.19/0.99  num_of_symbols:                         41
% 3.19/0.99  num_of_terms:                           4664
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing
% 3.19/0.99  
% 3.19/0.99  num_of_splits:                          0
% 3.19/0.99  num_of_split_atoms:                     0
% 3.19/0.99  num_of_reused_defs:                     0
% 3.19/0.99  num_eq_ax_congr_red:                    41
% 3.19/0.99  num_of_sem_filtered_clauses:            1
% 3.19/0.99  num_of_subtypes:                        0
% 3.19/0.99  monotx_restored_types:                  0
% 3.19/0.99  sat_num_of_epr_types:                   0
% 3.19/0.99  sat_num_of_non_cyclic_types:            0
% 3.19/0.99  sat_guarded_non_collapsed_types:        0
% 3.19/0.99  num_pure_diseq_elim:                    0
% 3.19/0.99  simp_replaced_by:                       0
% 3.19/0.99  res_preprocessed:                       90
% 3.19/0.99  prep_upred:                             0
% 3.19/0.99  prep_unflattend:                        0
% 3.19/0.99  smt_new_axioms:                         0
% 3.19/0.99  pred_elim_cands:                        2
% 3.19/0.99  pred_elim:                              1
% 3.19/0.99  pred_elim_cl:                           1
% 3.19/0.99  pred_elim_cycles:                       3
% 3.19/0.99  merged_defs:                            0
% 3.19/0.99  merged_defs_ncl:                        0
% 3.19/0.99  bin_hyper_res:                          0
% 3.19/0.99  prep_cycles:                            4
% 3.19/0.99  pred_elim_time:                         0.001
% 3.19/0.99  splitting_time:                         0.
% 3.19/0.99  sem_filter_time:                        0.
% 3.19/0.99  monotx_time:                            0.001
% 3.19/0.99  subtype_inf_time:                       0.
% 3.19/0.99  
% 3.19/0.99  ------ Problem properties
% 3.19/0.99  
% 3.19/0.99  clauses:                                19
% 3.19/0.99  conjectures:                            2
% 3.19/0.99  epr:                                    3
% 3.19/0.99  horn:                                   16
% 3.19/0.99  ground:                                 2
% 3.19/0.99  unary:                                  9
% 3.19/0.99  binary:                                 3
% 3.19/0.99  lits:                                   39
% 3.19/0.99  lits_eq:                                18
% 3.19/0.99  fd_pure:                                0
% 3.19/0.99  fd_pseudo:                              0
% 3.19/0.99  fd_cond:                                0
% 3.19/0.99  fd_pseudo_cond:                         5
% 3.19/0.99  ac_symbols:                             0
% 3.19/0.99  
% 3.19/0.99  ------ Propositional Solver
% 3.19/0.99  
% 3.19/0.99  prop_solver_calls:                      29
% 3.19/0.99  prop_fast_solver_calls:                 496
% 3.19/0.99  smt_solver_calls:                       0
% 3.19/0.99  smt_fast_solver_calls:                  0
% 3.19/0.99  prop_num_of_clauses:                    1514
% 3.19/0.99  prop_preprocess_simplified:             6136
% 3.19/0.99  prop_fo_subsumed:                       0
% 3.19/0.99  prop_solver_time:                       0.
% 3.19/0.99  smt_solver_time:                        0.
% 3.19/0.99  smt_fast_solver_time:                   0.
% 3.19/0.99  prop_fast_solver_time:                  0.
% 3.19/0.99  prop_unsat_core_time:                   0.
% 3.19/0.99  
% 3.19/0.99  ------ QBF
% 3.19/0.99  
% 3.19/0.99  qbf_q_res:                              0
% 3.19/0.99  qbf_num_tautologies:                    0
% 3.19/0.99  qbf_prep_cycles:                        0
% 3.19/0.99  
% 3.19/0.99  ------ BMC1
% 3.19/0.99  
% 3.19/0.99  bmc1_current_bound:                     -1
% 3.19/0.99  bmc1_last_solved_bound:                 -1
% 3.19/0.99  bmc1_unsat_core_size:                   -1
% 3.19/0.99  bmc1_unsat_core_parents_size:           -1
% 3.19/0.99  bmc1_merge_next_fun:                    0
% 3.19/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.19/0.99  
% 3.19/0.99  ------ Instantiation
% 3.19/0.99  
% 3.19/0.99  inst_num_of_clauses:                    492
% 3.19/0.99  inst_num_in_passive:                    289
% 3.19/0.99  inst_num_in_active:                     176
% 3.19/0.99  inst_num_in_unprocessed:                26
% 3.19/0.99  inst_num_of_loops:                      248
% 3.19/0.99  inst_num_of_learning_restarts:          0
% 3.19/0.99  inst_num_moves_active_passive:          69
% 3.19/0.99  inst_lit_activity:                      0
% 3.19/0.99  inst_lit_activity_moves:                0
% 3.19/0.99  inst_num_tautologies:                   0
% 3.19/0.99  inst_num_prop_implied:                  0
% 3.19/0.99  inst_num_existing_simplified:           0
% 3.19/0.99  inst_num_eq_res_simplified:             0
% 3.19/0.99  inst_num_child_elim:                    0
% 3.19/0.99  inst_num_of_dismatching_blockings:      338
% 3.19/0.99  inst_num_of_non_proper_insts:           613
% 3.19/0.99  inst_num_of_duplicates:                 0
% 3.19/0.99  inst_inst_num_from_inst_to_res:         0
% 3.19/0.99  inst_dismatching_checking_time:         0.
% 3.19/0.99  
% 3.19/0.99  ------ Resolution
% 3.19/0.99  
% 3.19/0.99  res_num_of_clauses:                     0
% 3.19/0.99  res_num_in_passive:                     0
% 3.19/0.99  res_num_in_active:                      0
% 3.19/0.99  res_num_of_loops:                       94
% 3.19/0.99  res_forward_subset_subsumed:            59
% 3.19/0.99  res_backward_subset_subsumed:           0
% 3.19/0.99  res_forward_subsumed:                   0
% 3.19/0.99  res_backward_subsumed:                  0
% 3.19/0.99  res_forward_subsumption_resolution:     0
% 3.19/0.99  res_backward_subsumption_resolution:    0
% 3.19/0.99  res_clause_to_clause_subsumption:       445
% 3.19/0.99  res_orphan_elimination:                 0
% 3.19/0.99  res_tautology_del:                      8
% 3.19/0.99  res_num_eq_res_simplified:              0
% 3.19/0.99  res_num_sel_changes:                    0
% 3.19/0.99  res_moves_from_active_to_pass:          0
% 3.19/0.99  
% 3.19/0.99  ------ Superposition
% 3.19/0.99  
% 3.19/0.99  sup_time_total:                         0.
% 3.19/0.99  sup_time_generating:                    0.
% 3.19/0.99  sup_time_sim_full:                      0.
% 3.19/0.99  sup_time_sim_immed:                     0.
% 3.19/0.99  
% 3.19/0.99  sup_num_of_clauses:                     100
% 3.19/0.99  sup_num_in_active:                      36
% 3.19/0.99  sup_num_in_passive:                     64
% 3.19/0.99  sup_num_of_loops:                       48
% 3.19/0.99  sup_fw_superposition:                   56
% 3.19/0.99  sup_bw_superposition:                   126
% 3.19/0.99  sup_immediate_simplified:               14
% 3.19/0.99  sup_given_eliminated:                   0
% 3.19/0.99  comparisons_done:                       0
% 3.19/0.99  comparisons_avoided:                    45
% 3.19/0.99  
% 3.19/0.99  ------ Simplifications
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  sim_fw_subset_subsumed:                 0
% 3.19/0.99  sim_bw_subset_subsumed:                 3
% 3.19/0.99  sim_fw_subsumed:                        2
% 3.19/0.99  sim_bw_subsumed:                        4
% 3.19/0.99  sim_fw_subsumption_res:                 0
% 3.19/0.99  sim_bw_subsumption_res:                 0
% 3.19/0.99  sim_tautology_del:                      0
% 3.19/0.99  sim_eq_tautology_del:                   4
% 3.19/0.99  sim_eq_res_simp:                        0
% 3.19/0.99  sim_fw_demodulated:                     10
% 3.19/0.99  sim_bw_demodulated:                     10
% 3.19/0.99  sim_light_normalised:                   3
% 3.19/0.99  sim_joinable_taut:                      0
% 3.19/0.99  sim_joinable_simp:                      0
% 3.19/0.99  sim_ac_normalised:                      0
% 3.19/0.99  sim_smt_subsumption:                    0
% 3.19/0.99  
%------------------------------------------------------------------------------
