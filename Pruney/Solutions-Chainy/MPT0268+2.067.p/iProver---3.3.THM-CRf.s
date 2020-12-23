%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:43 EST 2020

% Result     : Theorem 23.23s
% Output     : CNFRefutation 23.23s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 210 expanded)
%              Number of clauses        :   59 (  67 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  329 ( 693 expanded)
%              Number of equality atoms :  109 ( 217 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f32,plain,
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

fof(f33,plain,
    ( ( r2_hidden(sK4,sK3)
      | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3 )
    & ( ~ r2_hidden(sK4,sK3)
      | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f32])).

fof(f53,plain,
    ( ~ r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f62,plain,
    ( ~ r2_hidden(sK4,sK3)
    | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3 ),
    inference(definition_unfolding,[],[f53,f45,f56])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f27])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,
    ( r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,
    ( r2_hidden(sK4,sK3)
    | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != sK3 ),
    inference(definition_unfolding,[],[f54,f45,f56])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK4,sK3)
    | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_196,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1054,plain,
    ( X0 != X1
    | k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X0 ),
    inference(resolution,[status(thm)],[c_196,c_11])).

cnf(c_199,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_7225,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)),X1)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_1054,c_199])).

cnf(c_88040,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))),X0)
    | r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),X0)
    | ~ r2_hidden(sK4,sK3) ),
    inference(resolution,[status(thm)],[c_16,c_7225])).

cnf(c_12,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_89601,plain,
    ( r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK4,sK3) ),
    inference(resolution,[status(thm)],[c_88040,c_12])).

cnf(c_8172,plain,
    ( ~ r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
    | r1_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))
    | X2 != X0 ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_65417,plain,
    ( ~ r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
    | r1_xboole_0(sK3,k2_enumset1(X1,X1,X1,X1))
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_8172])).

cnf(c_83542,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(X0,X0,X0,X0))
    | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0))
    | sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_65417])).

cnf(c_83544,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r1_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_83542])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6763,plain,
    ( ~ r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_41749,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_6763])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1489,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7671,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)
    | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),X0)
    | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_18827,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) ),
    inference(instantiation,[status(thm)],[c_7671])).

cnf(c_18828,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) != iProver_top
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18827])).

cnf(c_7651,plain,
    ( ~ r1_xboole_0(sK3,X0)
    | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),X0)
    | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_18810,plain,
    ( ~ r1_xboole_0(sK3,k1_xboole_0)
    | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3)
    | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7651])).

cnf(c_18811,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) != iProver_top
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) != iProver_top
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18810])).

cnf(c_2322,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1)
    | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_13603,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0)
    | r1_xboole_0(sK3,k1_xboole_0)
    | sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_13604,plain,
    ( sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))
    | r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
    | r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13603])).

cnf(c_10507,plain,
    ( r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10508,plain,
    ( r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10507])).

cnf(c_14,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5918,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_5919,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5918])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2826,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1469,plain,
    ( ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0))
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1470,plain,
    ( r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1469])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1466,plain,
    ( ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0))
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1467,plain,
    ( r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_920,plain,
    ( r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0))
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3)
    | k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_924,plain,
    ( k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k1_xboole_0)
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0)) = iProver_top
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_921,plain,
    ( r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0))
    | k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_922,plain,
    ( k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k1_xboole_0)
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_200,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_916,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))
    | k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != k3_xboole_0(sK3,k1_xboole_0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_733,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != X0
    | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_836,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))
    | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3
    | sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_827,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) = sK3 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_758,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_759,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_826,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) != sK3
    | sK3 = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_195,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_760,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_89601,c_83544,c_41749,c_18828,c_18811,c_13604,c_10508,c_5919,c_2826,c_1470,c_1467,c_924,c_922,c_916,c_836,c_827,c_826,c_760,c_15,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:42:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.23/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.23/3.49  
% 23.23/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.23/3.49  
% 23.23/3.49  ------  iProver source info
% 23.23/3.49  
% 23.23/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.23/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.23/3.49  git: non_committed_changes: false
% 23.23/3.49  git: last_make_outside_of_git: false
% 23.23/3.49  
% 23.23/3.49  ------ 
% 23.23/3.49  
% 23.23/3.49  ------ Input Options
% 23.23/3.49  
% 23.23/3.49  --out_options                           all
% 23.23/3.49  --tptp_safe_out                         true
% 23.23/3.49  --problem_path                          ""
% 23.23/3.49  --include_path                          ""
% 23.23/3.49  --clausifier                            res/vclausify_rel
% 23.23/3.49  --clausifier_options                    --mode clausify
% 23.23/3.49  --stdin                                 false
% 23.23/3.49  --stats_out                             sel
% 23.23/3.49  
% 23.23/3.49  ------ General Options
% 23.23/3.49  
% 23.23/3.49  --fof                                   false
% 23.23/3.49  --time_out_real                         604.99
% 23.23/3.49  --time_out_virtual                      -1.
% 23.23/3.49  --symbol_type_check                     false
% 23.23/3.49  --clausify_out                          false
% 23.23/3.49  --sig_cnt_out                           false
% 23.23/3.49  --trig_cnt_out                          false
% 23.23/3.49  --trig_cnt_out_tolerance                1.
% 23.23/3.49  --trig_cnt_out_sk_spl                   false
% 23.23/3.49  --abstr_cl_out                          false
% 23.23/3.49  
% 23.23/3.49  ------ Global Options
% 23.23/3.49  
% 23.23/3.49  --schedule                              none
% 23.23/3.49  --add_important_lit                     false
% 23.23/3.49  --prop_solver_per_cl                    1000
% 23.23/3.49  --min_unsat_core                        false
% 23.23/3.49  --soft_assumptions                      false
% 23.23/3.49  --soft_lemma_size                       3
% 23.23/3.49  --prop_impl_unit_size                   0
% 23.23/3.49  --prop_impl_unit                        []
% 23.23/3.49  --share_sel_clauses                     true
% 23.23/3.49  --reset_solvers                         false
% 23.23/3.49  --bc_imp_inh                            [conj_cone]
% 23.23/3.49  --conj_cone_tolerance                   3.
% 23.23/3.49  --extra_neg_conj                        none
% 23.23/3.49  --large_theory_mode                     true
% 23.23/3.49  --prolific_symb_bound                   200
% 23.23/3.49  --lt_threshold                          2000
% 23.23/3.49  --clause_weak_htbl                      true
% 23.23/3.49  --gc_record_bc_elim                     false
% 23.23/3.49  
% 23.23/3.49  ------ Preprocessing Options
% 23.23/3.49  
% 23.23/3.49  --preprocessing_flag                    true
% 23.23/3.49  --time_out_prep_mult                    0.1
% 23.23/3.49  --splitting_mode                        input
% 23.23/3.49  --splitting_grd                         true
% 23.23/3.49  --splitting_cvd                         false
% 23.23/3.49  --splitting_cvd_svl                     false
% 23.23/3.49  --splitting_nvd                         32
% 23.23/3.49  --sub_typing                            true
% 23.23/3.49  --prep_gs_sim                           false
% 23.23/3.49  --prep_unflatten                        true
% 23.23/3.49  --prep_res_sim                          true
% 23.23/3.49  --prep_upred                            true
% 23.23/3.49  --prep_sem_filter                       exhaustive
% 23.23/3.49  --prep_sem_filter_out                   false
% 23.23/3.49  --pred_elim                             false
% 23.23/3.49  --res_sim_input                         true
% 23.23/3.49  --eq_ax_congr_red                       true
% 23.23/3.49  --pure_diseq_elim                       true
% 23.23/3.49  --brand_transform                       false
% 23.23/3.49  --non_eq_to_eq                          false
% 23.23/3.49  --prep_def_merge                        true
% 23.23/3.49  --prep_def_merge_prop_impl              false
% 23.23/3.49  --prep_def_merge_mbd                    true
% 23.23/3.49  --prep_def_merge_tr_red                 false
% 23.23/3.49  --prep_def_merge_tr_cl                  false
% 23.23/3.49  --smt_preprocessing                     true
% 23.23/3.49  --smt_ac_axioms                         fast
% 23.23/3.49  --preprocessed_out                      false
% 23.23/3.49  --preprocessed_stats                    false
% 23.23/3.49  
% 23.23/3.49  ------ Abstraction refinement Options
% 23.23/3.49  
% 23.23/3.49  --abstr_ref                             []
% 23.23/3.49  --abstr_ref_prep                        false
% 23.23/3.49  --abstr_ref_until_sat                   false
% 23.23/3.49  --abstr_ref_sig_restrict                funpre
% 23.23/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.23/3.49  --abstr_ref_under                       []
% 23.23/3.49  
% 23.23/3.49  ------ SAT Options
% 23.23/3.49  
% 23.23/3.49  --sat_mode                              false
% 23.23/3.49  --sat_fm_restart_options                ""
% 23.23/3.49  --sat_gr_def                            false
% 23.23/3.49  --sat_epr_types                         true
% 23.23/3.49  --sat_non_cyclic_types                  false
% 23.23/3.49  --sat_finite_models                     false
% 23.23/3.49  --sat_fm_lemmas                         false
% 23.23/3.49  --sat_fm_prep                           false
% 23.23/3.49  --sat_fm_uc_incr                        true
% 23.23/3.49  --sat_out_model                         small
% 23.23/3.49  --sat_out_clauses                       false
% 23.23/3.49  
% 23.23/3.49  ------ QBF Options
% 23.23/3.49  
% 23.23/3.49  --qbf_mode                              false
% 23.23/3.49  --qbf_elim_univ                         false
% 23.23/3.49  --qbf_dom_inst                          none
% 23.23/3.49  --qbf_dom_pre_inst                      false
% 23.23/3.49  --qbf_sk_in                             false
% 23.23/3.49  --qbf_pred_elim                         true
% 23.23/3.49  --qbf_split                             512
% 23.23/3.49  
% 23.23/3.49  ------ BMC1 Options
% 23.23/3.49  
% 23.23/3.49  --bmc1_incremental                      false
% 23.23/3.49  --bmc1_axioms                           reachable_all
% 23.23/3.49  --bmc1_min_bound                        0
% 23.23/3.49  --bmc1_max_bound                        -1
% 23.23/3.49  --bmc1_max_bound_default                -1
% 23.23/3.49  --bmc1_symbol_reachability              true
% 23.23/3.49  --bmc1_property_lemmas                  false
% 23.23/3.49  --bmc1_k_induction                      false
% 23.23/3.49  --bmc1_non_equiv_states                 false
% 23.23/3.49  --bmc1_deadlock                         false
% 23.23/3.49  --bmc1_ucm                              false
% 23.23/3.49  --bmc1_add_unsat_core                   none
% 23.23/3.49  --bmc1_unsat_core_children              false
% 23.23/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.23/3.49  --bmc1_out_stat                         full
% 23.23/3.49  --bmc1_ground_init                      false
% 23.23/3.49  --bmc1_pre_inst_next_state              false
% 23.23/3.49  --bmc1_pre_inst_state                   false
% 23.23/3.49  --bmc1_pre_inst_reach_state             false
% 23.23/3.49  --bmc1_out_unsat_core                   false
% 23.23/3.49  --bmc1_aig_witness_out                  false
% 23.23/3.49  --bmc1_verbose                          false
% 23.23/3.49  --bmc1_dump_clauses_tptp                false
% 23.23/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.23/3.49  --bmc1_dump_file                        -
% 23.23/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.23/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.23/3.49  --bmc1_ucm_extend_mode                  1
% 23.23/3.49  --bmc1_ucm_init_mode                    2
% 23.23/3.49  --bmc1_ucm_cone_mode                    none
% 23.23/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.23/3.49  --bmc1_ucm_relax_model                  4
% 23.23/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.23/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.23/3.49  --bmc1_ucm_layered_model                none
% 23.23/3.49  --bmc1_ucm_max_lemma_size               10
% 23.23/3.49  
% 23.23/3.49  ------ AIG Options
% 23.23/3.49  
% 23.23/3.49  --aig_mode                              false
% 23.23/3.49  
% 23.23/3.49  ------ Instantiation Options
% 23.23/3.49  
% 23.23/3.49  --instantiation_flag                    true
% 23.23/3.49  --inst_sos_flag                         false
% 23.23/3.49  --inst_sos_phase                        true
% 23.23/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.23/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.23/3.49  --inst_lit_sel_side                     num_symb
% 23.23/3.49  --inst_solver_per_active                1400
% 23.23/3.49  --inst_solver_calls_frac                1.
% 23.23/3.49  --inst_passive_queue_type               priority_queues
% 23.23/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.23/3.49  --inst_passive_queues_freq              [25;2]
% 23.23/3.49  --inst_dismatching                      true
% 23.23/3.49  --inst_eager_unprocessed_to_passive     true
% 23.23/3.49  --inst_prop_sim_given                   true
% 23.23/3.49  --inst_prop_sim_new                     false
% 23.23/3.49  --inst_subs_new                         false
% 23.23/3.49  --inst_eq_res_simp                      false
% 23.23/3.49  --inst_subs_given                       false
% 23.23/3.49  --inst_orphan_elimination               true
% 23.23/3.49  --inst_learning_loop_flag               true
% 23.23/3.49  --inst_learning_start                   3000
% 23.23/3.49  --inst_learning_factor                  2
% 23.23/3.49  --inst_start_prop_sim_after_learn       3
% 23.23/3.49  --inst_sel_renew                        solver
% 23.23/3.49  --inst_lit_activity_flag                true
% 23.23/3.49  --inst_restr_to_given                   false
% 23.23/3.49  --inst_activity_threshold               500
% 23.23/3.49  --inst_out_proof                        true
% 23.23/3.49  
% 23.23/3.49  ------ Resolution Options
% 23.23/3.49  
% 23.23/3.49  --resolution_flag                       true
% 23.23/3.49  --res_lit_sel                           adaptive
% 23.23/3.49  --res_lit_sel_side                      none
% 23.23/3.49  --res_ordering                          kbo
% 23.23/3.49  --res_to_prop_solver                    active
% 23.23/3.49  --res_prop_simpl_new                    false
% 23.23/3.49  --res_prop_simpl_given                  true
% 23.23/3.49  --res_passive_queue_type                priority_queues
% 23.23/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.23/3.49  --res_passive_queues_freq               [15;5]
% 23.23/3.49  --res_forward_subs                      full
% 23.23/3.49  --res_backward_subs                     full
% 23.23/3.49  --res_forward_subs_resolution           true
% 23.23/3.49  --res_backward_subs_resolution          true
% 23.23/3.49  --res_orphan_elimination                true
% 23.23/3.49  --res_time_limit                        2.
% 23.23/3.49  --res_out_proof                         true
% 23.23/3.49  
% 23.23/3.49  ------ Superposition Options
% 23.23/3.49  
% 23.23/3.49  --superposition_flag                    true
% 23.23/3.49  --sup_passive_queue_type                priority_queues
% 23.23/3.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.23/3.49  --sup_passive_queues_freq               [1;4]
% 23.23/3.49  --demod_completeness_check              fast
% 23.23/3.49  --demod_use_ground                      true
% 23.23/3.49  --sup_to_prop_solver                    passive
% 23.23/3.49  --sup_prop_simpl_new                    true
% 23.23/3.49  --sup_prop_simpl_given                  true
% 23.23/3.49  --sup_fun_splitting                     false
% 23.23/3.49  --sup_smt_interval                      50000
% 23.23/3.49  
% 23.23/3.49  ------ Superposition Simplification Setup
% 23.23/3.49  
% 23.23/3.49  --sup_indices_passive                   []
% 23.23/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.23/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.23/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.23/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.23/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.23/3.49  --sup_full_bw                           [BwDemod]
% 23.23/3.49  --sup_immed_triv                        [TrivRules]
% 23.23/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.23/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.23/3.49  --sup_immed_bw_main                     []
% 23.23/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.23/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.23/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.23/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.23/3.49  
% 23.23/3.49  ------ Combination Options
% 23.23/3.49  
% 23.23/3.49  --comb_res_mult                         3
% 23.23/3.49  --comb_sup_mult                         2
% 23.23/3.49  --comb_inst_mult                        10
% 23.23/3.49  
% 23.23/3.49  ------ Debug Options
% 23.23/3.49  
% 23.23/3.49  --dbg_backtrace                         false
% 23.23/3.49  --dbg_dump_prop_clauses                 false
% 23.23/3.49  --dbg_dump_prop_clauses_file            -
% 23.23/3.49  --dbg_out_stat                          false
% 23.23/3.49  ------ Parsing...
% 23.23/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.23/3.49  
% 23.23/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 23.23/3.49  
% 23.23/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.23/3.49  
% 23.23/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.23/3.49  ------ Proving...
% 23.23/3.49  ------ Problem Properties 
% 23.23/3.49  
% 23.23/3.49  
% 23.23/3.49  clauses                                 17
% 23.23/3.49  conjectures                             2
% 23.23/3.49  EPR                                     2
% 23.23/3.49  Horn                                    11
% 23.23/3.49  unary                                   2
% 23.23/3.49  binary                                  10
% 23.23/3.49  lits                                    38
% 23.23/3.49  lits eq                                 7
% 23.23/3.49  fd_pure                                 0
% 23.23/3.49  fd_pseudo                               0
% 23.23/3.49  fd_cond                                 1
% 23.23/3.49  fd_pseudo_cond                          3
% 23.23/3.49  AC symbols                              0
% 23.23/3.49  
% 23.23/3.49  ------ Input Options Time Limit: Unbounded
% 23.23/3.49  
% 23.23/3.49  
% 23.23/3.49  ------ 
% 23.23/3.49  Current options:
% 23.23/3.49  ------ 
% 23.23/3.49  
% 23.23/3.49  ------ Input Options
% 23.23/3.49  
% 23.23/3.49  --out_options                           all
% 23.23/3.49  --tptp_safe_out                         true
% 23.23/3.49  --problem_path                          ""
% 23.23/3.49  --include_path                          ""
% 23.23/3.49  --clausifier                            res/vclausify_rel
% 23.23/3.49  --clausifier_options                    --mode clausify
% 23.23/3.49  --stdin                                 false
% 23.23/3.49  --stats_out                             sel
% 23.23/3.49  
% 23.23/3.49  ------ General Options
% 23.23/3.49  
% 23.23/3.49  --fof                                   false
% 23.23/3.49  --time_out_real                         604.99
% 23.23/3.49  --time_out_virtual                      -1.
% 23.23/3.49  --symbol_type_check                     false
% 23.23/3.49  --clausify_out                          false
% 23.23/3.49  --sig_cnt_out                           false
% 23.23/3.49  --trig_cnt_out                          false
% 23.23/3.49  --trig_cnt_out_tolerance                1.
% 23.23/3.49  --trig_cnt_out_sk_spl                   false
% 23.23/3.49  --abstr_cl_out                          false
% 23.23/3.49  
% 23.23/3.49  ------ Global Options
% 23.23/3.49  
% 23.23/3.49  --schedule                              none
% 23.23/3.49  --add_important_lit                     false
% 23.23/3.49  --prop_solver_per_cl                    1000
% 23.23/3.49  --min_unsat_core                        false
% 23.23/3.49  --soft_assumptions                      false
% 23.23/3.49  --soft_lemma_size                       3
% 23.23/3.49  --prop_impl_unit_size                   0
% 23.23/3.49  --prop_impl_unit                        []
% 23.23/3.49  --share_sel_clauses                     true
% 23.23/3.49  --reset_solvers                         false
% 23.23/3.49  --bc_imp_inh                            [conj_cone]
% 23.23/3.49  --conj_cone_tolerance                   3.
% 23.23/3.49  --extra_neg_conj                        none
% 23.23/3.49  --large_theory_mode                     true
% 23.23/3.49  --prolific_symb_bound                   200
% 23.23/3.49  --lt_threshold                          2000
% 23.23/3.49  --clause_weak_htbl                      true
% 23.23/3.49  --gc_record_bc_elim                     false
% 23.23/3.49  
% 23.23/3.49  ------ Preprocessing Options
% 23.23/3.49  
% 23.23/3.49  --preprocessing_flag                    true
% 23.23/3.49  --time_out_prep_mult                    0.1
% 23.23/3.49  --splitting_mode                        input
% 23.23/3.49  --splitting_grd                         true
% 23.23/3.49  --splitting_cvd                         false
% 23.23/3.49  --splitting_cvd_svl                     false
% 23.23/3.49  --splitting_nvd                         32
% 23.23/3.49  --sub_typing                            true
% 23.23/3.49  --prep_gs_sim                           false
% 23.23/3.49  --prep_unflatten                        true
% 23.23/3.49  --prep_res_sim                          true
% 23.23/3.49  --prep_upred                            true
% 23.23/3.49  --prep_sem_filter                       exhaustive
% 23.23/3.49  --prep_sem_filter_out                   false
% 23.23/3.49  --pred_elim                             false
% 23.23/3.49  --res_sim_input                         true
% 23.23/3.49  --eq_ax_congr_red                       true
% 23.23/3.49  --pure_diseq_elim                       true
% 23.23/3.49  --brand_transform                       false
% 23.23/3.49  --non_eq_to_eq                          false
% 23.23/3.49  --prep_def_merge                        true
% 23.23/3.49  --prep_def_merge_prop_impl              false
% 23.23/3.49  --prep_def_merge_mbd                    true
% 23.23/3.49  --prep_def_merge_tr_red                 false
% 23.23/3.49  --prep_def_merge_tr_cl                  false
% 23.23/3.49  --smt_preprocessing                     true
% 23.23/3.49  --smt_ac_axioms                         fast
% 23.23/3.49  --preprocessed_out                      false
% 23.23/3.49  --preprocessed_stats                    false
% 23.23/3.49  
% 23.23/3.49  ------ Abstraction refinement Options
% 23.23/3.49  
% 23.23/3.49  --abstr_ref                             []
% 23.23/3.49  --abstr_ref_prep                        false
% 23.23/3.49  --abstr_ref_until_sat                   false
% 23.23/3.49  --abstr_ref_sig_restrict                funpre
% 23.23/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.23/3.49  --abstr_ref_under                       []
% 23.23/3.49  
% 23.23/3.49  ------ SAT Options
% 23.23/3.49  
% 23.23/3.49  --sat_mode                              false
% 23.23/3.49  --sat_fm_restart_options                ""
% 23.23/3.49  --sat_gr_def                            false
% 23.23/3.49  --sat_epr_types                         true
% 23.23/3.49  --sat_non_cyclic_types                  false
% 23.23/3.49  --sat_finite_models                     false
% 23.23/3.49  --sat_fm_lemmas                         false
% 23.23/3.49  --sat_fm_prep                           false
% 23.23/3.49  --sat_fm_uc_incr                        true
% 23.23/3.49  --sat_out_model                         small
% 23.23/3.49  --sat_out_clauses                       false
% 23.23/3.49  
% 23.23/3.49  ------ QBF Options
% 23.23/3.49  
% 23.23/3.49  --qbf_mode                              false
% 23.23/3.49  --qbf_elim_univ                         false
% 23.23/3.49  --qbf_dom_inst                          none
% 23.23/3.49  --qbf_dom_pre_inst                      false
% 23.23/3.49  --qbf_sk_in                             false
% 23.23/3.49  --qbf_pred_elim                         true
% 23.23/3.49  --qbf_split                             512
% 23.23/3.49  
% 23.23/3.49  ------ BMC1 Options
% 23.23/3.49  
% 23.23/3.49  --bmc1_incremental                      false
% 23.23/3.49  --bmc1_axioms                           reachable_all
% 23.23/3.49  --bmc1_min_bound                        0
% 23.23/3.49  --bmc1_max_bound                        -1
% 23.23/3.49  --bmc1_max_bound_default                -1
% 23.23/3.49  --bmc1_symbol_reachability              true
% 23.23/3.49  --bmc1_property_lemmas                  false
% 23.23/3.49  --bmc1_k_induction                      false
% 23.23/3.49  --bmc1_non_equiv_states                 false
% 23.23/3.49  --bmc1_deadlock                         false
% 23.23/3.49  --bmc1_ucm                              false
% 23.23/3.49  --bmc1_add_unsat_core                   none
% 23.23/3.49  --bmc1_unsat_core_children              false
% 23.23/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.23/3.49  --bmc1_out_stat                         full
% 23.23/3.49  --bmc1_ground_init                      false
% 23.23/3.49  --bmc1_pre_inst_next_state              false
% 23.23/3.49  --bmc1_pre_inst_state                   false
% 23.23/3.49  --bmc1_pre_inst_reach_state             false
% 23.23/3.49  --bmc1_out_unsat_core                   false
% 23.23/3.49  --bmc1_aig_witness_out                  false
% 23.23/3.49  --bmc1_verbose                          false
% 23.23/3.49  --bmc1_dump_clauses_tptp                false
% 23.23/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.23/3.49  --bmc1_dump_file                        -
% 23.23/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.23/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.23/3.49  --bmc1_ucm_extend_mode                  1
% 23.23/3.49  --bmc1_ucm_init_mode                    2
% 23.23/3.49  --bmc1_ucm_cone_mode                    none
% 23.23/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.23/3.49  --bmc1_ucm_relax_model                  4
% 23.23/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.23/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.23/3.49  --bmc1_ucm_layered_model                none
% 23.23/3.49  --bmc1_ucm_max_lemma_size               10
% 23.23/3.49  
% 23.23/3.49  ------ AIG Options
% 23.23/3.49  
% 23.23/3.49  --aig_mode                              false
% 23.23/3.49  
% 23.23/3.49  ------ Instantiation Options
% 23.23/3.49  
% 23.23/3.49  --instantiation_flag                    true
% 23.23/3.49  --inst_sos_flag                         false
% 23.23/3.49  --inst_sos_phase                        true
% 23.23/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.23/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.23/3.49  --inst_lit_sel_side                     num_symb
% 23.23/3.49  --inst_solver_per_active                1400
% 23.23/3.49  --inst_solver_calls_frac                1.
% 23.23/3.49  --inst_passive_queue_type               priority_queues
% 23.23/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.23/3.49  --inst_passive_queues_freq              [25;2]
% 23.23/3.49  --inst_dismatching                      true
% 23.23/3.49  --inst_eager_unprocessed_to_passive     true
% 23.23/3.49  --inst_prop_sim_given                   true
% 23.23/3.49  --inst_prop_sim_new                     false
% 23.23/3.49  --inst_subs_new                         false
% 23.23/3.49  --inst_eq_res_simp                      false
% 23.23/3.49  --inst_subs_given                       false
% 23.23/3.49  --inst_orphan_elimination               true
% 23.23/3.49  --inst_learning_loop_flag               true
% 23.23/3.49  --inst_learning_start                   3000
% 23.23/3.49  --inst_learning_factor                  2
% 23.23/3.49  --inst_start_prop_sim_after_learn       3
% 23.23/3.49  --inst_sel_renew                        solver
% 23.23/3.49  --inst_lit_activity_flag                true
% 23.23/3.49  --inst_restr_to_given                   false
% 23.23/3.49  --inst_activity_threshold               500
% 23.23/3.49  --inst_out_proof                        true
% 23.23/3.49  
% 23.23/3.49  ------ Resolution Options
% 23.23/3.49  
% 23.23/3.49  --resolution_flag                       true
% 23.23/3.49  --res_lit_sel                           adaptive
% 23.23/3.49  --res_lit_sel_side                      none
% 23.23/3.49  --res_ordering                          kbo
% 23.23/3.49  --res_to_prop_solver                    active
% 23.23/3.49  --res_prop_simpl_new                    false
% 23.23/3.49  --res_prop_simpl_given                  true
% 23.23/3.49  --res_passive_queue_type                priority_queues
% 23.23/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.23/3.49  --res_passive_queues_freq               [15;5]
% 23.23/3.49  --res_forward_subs                      full
% 23.23/3.49  --res_backward_subs                     full
% 23.23/3.49  --res_forward_subs_resolution           true
% 23.23/3.49  --res_backward_subs_resolution          true
% 23.23/3.49  --res_orphan_elimination                true
% 23.23/3.49  --res_time_limit                        2.
% 23.23/3.49  --res_out_proof                         true
% 23.23/3.49  
% 23.23/3.49  ------ Superposition Options
% 23.23/3.49  
% 23.23/3.49  --superposition_flag                    true
% 23.23/3.49  --sup_passive_queue_type                priority_queues
% 23.23/3.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.23/3.49  --sup_passive_queues_freq               [1;4]
% 23.23/3.49  --demod_completeness_check              fast
% 23.23/3.49  --demod_use_ground                      true
% 23.23/3.49  --sup_to_prop_solver                    passive
% 23.23/3.49  --sup_prop_simpl_new                    true
% 23.23/3.49  --sup_prop_simpl_given                  true
% 23.23/3.49  --sup_fun_splitting                     false
% 23.23/3.49  --sup_smt_interval                      50000
% 23.23/3.49  
% 23.23/3.49  ------ Superposition Simplification Setup
% 23.23/3.49  
% 23.23/3.49  --sup_indices_passive                   []
% 23.23/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.23/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.23/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.23/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.23/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.23/3.49  --sup_full_bw                           [BwDemod]
% 23.23/3.49  --sup_immed_triv                        [TrivRules]
% 23.23/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.23/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.23/3.49  --sup_immed_bw_main                     []
% 23.23/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.23/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.23/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.23/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.23/3.49  
% 23.23/3.49  ------ Combination Options
% 23.23/3.49  
% 23.23/3.49  --comb_res_mult                         3
% 23.23/3.49  --comb_sup_mult                         2
% 23.23/3.49  --comb_inst_mult                        10
% 23.23/3.49  
% 23.23/3.49  ------ Debug Options
% 23.23/3.49  
% 23.23/3.49  --dbg_backtrace                         false
% 23.23/3.49  --dbg_dump_prop_clauses                 false
% 23.23/3.49  --dbg_dump_prop_clauses_file            -
% 23.23/3.49  --dbg_out_stat                          false
% 23.23/3.49  
% 23.23/3.49  
% 23.23/3.49  
% 23.23/3.49  
% 23.23/3.49  ------ Proving...
% 23.23/3.49  
% 23.23/3.49  
% 23.23/3.49  % SZS status Theorem for theBenchmark.p
% 23.23/3.49  
% 23.23/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.23/3.49  
% 23.23/3.49  fof(f13,conjecture,(
% 23.23/3.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f14,negated_conjecture,(
% 23.23/3.49    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 23.23/3.49    inference(negated_conjecture,[],[f13])).
% 23.23/3.49  
% 23.23/3.49  fof(f21,plain,(
% 23.23/3.49    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 23.23/3.49    inference(ennf_transformation,[],[f14])).
% 23.23/3.49  
% 23.23/3.49  fof(f31,plain,(
% 23.23/3.49    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 23.23/3.49    inference(nnf_transformation,[],[f21])).
% 23.23/3.49  
% 23.23/3.49  fof(f32,plain,(
% 23.23/3.49    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3) & (~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3))),
% 23.23/3.49    introduced(choice_axiom,[])).
% 23.23/3.49  
% 23.23/3.49  fof(f33,plain,(
% 23.23/3.49    (r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3) & (~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3)),
% 23.23/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f32])).
% 23.23/3.49  
% 23.23/3.49  fof(f53,plain,(
% 23.23/3.49    ~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3),
% 23.23/3.49    inference(cnf_transformation,[],[f33])).
% 23.23/3.49  
% 23.23/3.49  fof(f5,axiom,(
% 23.23/3.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f45,plain,(
% 23.23/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.23/3.49    inference(cnf_transformation,[],[f5])).
% 23.23/3.49  
% 23.23/3.49  fof(f8,axiom,(
% 23.23/3.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f48,plain,(
% 23.23/3.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f8])).
% 23.23/3.49  
% 23.23/3.49  fof(f9,axiom,(
% 23.23/3.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f49,plain,(
% 23.23/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f9])).
% 23.23/3.49  
% 23.23/3.49  fof(f10,axiom,(
% 23.23/3.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f50,plain,(
% 23.23/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f10])).
% 23.23/3.49  
% 23.23/3.49  fof(f55,plain,(
% 23.23/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.23/3.49    inference(definition_unfolding,[],[f49,f50])).
% 23.23/3.49  
% 23.23/3.49  fof(f56,plain,(
% 23.23/3.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 23.23/3.49    inference(definition_unfolding,[],[f48,f55])).
% 23.23/3.49  
% 23.23/3.49  fof(f62,plain,(
% 23.23/3.49    ~r2_hidden(sK4,sK3) | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3),
% 23.23/3.49    inference(definition_unfolding,[],[f53,f45,f56])).
% 23.23/3.49  
% 23.23/3.49  fof(f6,axiom,(
% 23.23/3.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f46,plain,(
% 23.23/3.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.23/3.49    inference(cnf_transformation,[],[f6])).
% 23.23/3.49  
% 23.23/3.49  fof(f57,plain,(
% 23.23/3.49    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 23.23/3.49    inference(definition_unfolding,[],[f46,f45])).
% 23.23/3.49  
% 23.23/3.49  fof(f7,axiom,(
% 23.23/3.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f47,plain,(
% 23.23/3.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f7])).
% 23.23/3.49  
% 23.23/3.49  fof(f58,plain,(
% 23.23/3.49    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 23.23/3.49    inference(definition_unfolding,[],[f47,f45])).
% 23.23/3.49  
% 23.23/3.49  fof(f2,axiom,(
% 23.23/3.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f16,plain,(
% 23.23/3.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 23.23/3.49    inference(ennf_transformation,[],[f2])).
% 23.23/3.49  
% 23.23/3.49  fof(f40,plain,(
% 23.23/3.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f16])).
% 23.23/3.49  
% 23.23/3.49  fof(f3,axiom,(
% 23.23/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f15,plain,(
% 23.23/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.23/3.49    inference(rectify,[],[f3])).
% 23.23/3.49  
% 23.23/3.49  fof(f17,plain,(
% 23.23/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 23.23/3.49    inference(ennf_transformation,[],[f15])).
% 23.23/3.49  
% 23.23/3.49  fof(f27,plain,(
% 23.23/3.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 23.23/3.49    introduced(choice_axiom,[])).
% 23.23/3.49  
% 23.23/3.49  fof(f28,plain,(
% 23.23/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 23.23/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f27])).
% 23.23/3.49  
% 23.23/3.49  fof(f43,plain,(
% 23.23/3.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f28])).
% 23.23/3.49  
% 23.23/3.49  fof(f12,axiom,(
% 23.23/3.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f20,plain,(
% 23.23/3.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 23.23/3.49    inference(ennf_transformation,[],[f12])).
% 23.23/3.49  
% 23.23/3.49  fof(f52,plain,(
% 23.23/3.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f20])).
% 23.23/3.49  
% 23.23/3.49  fof(f60,plain,(
% 23.23/3.49    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 23.23/3.49    inference(definition_unfolding,[],[f52,f56])).
% 23.23/3.49  
% 23.23/3.49  fof(f11,axiom,(
% 23.23/3.49    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f19,plain,(
% 23.23/3.49    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 23.23/3.49    inference(ennf_transformation,[],[f11])).
% 23.23/3.49  
% 23.23/3.49  fof(f51,plain,(
% 23.23/3.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f19])).
% 23.23/3.49  
% 23.23/3.49  fof(f59,plain,(
% 23.23/3.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 23.23/3.49    inference(definition_unfolding,[],[f51,f56])).
% 23.23/3.49  
% 23.23/3.49  fof(f1,axiom,(
% 23.23/3.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.23/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.49  
% 23.23/3.49  fof(f22,plain,(
% 23.23/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.23/3.49    inference(nnf_transformation,[],[f1])).
% 23.23/3.49  
% 23.23/3.49  fof(f23,plain,(
% 23.23/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.23/3.49    inference(flattening,[],[f22])).
% 23.23/3.49  
% 23.23/3.49  fof(f24,plain,(
% 23.23/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.23/3.49    inference(rectify,[],[f23])).
% 23.23/3.49  
% 23.23/3.49  fof(f25,plain,(
% 23.23/3.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.23/3.49    introduced(choice_axiom,[])).
% 23.23/3.49  
% 23.23/3.49  fof(f26,plain,(
% 23.23/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.23/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 23.23/3.49  
% 23.23/3.49  fof(f34,plain,(
% 23.23/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 23.23/3.49    inference(cnf_transformation,[],[f26])).
% 23.23/3.49  
% 23.23/3.49  fof(f65,plain,(
% 23.23/3.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 23.23/3.49    inference(equality_resolution,[],[f34])).
% 23.23/3.49  
% 23.23/3.49  fof(f35,plain,(
% 23.23/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 23.23/3.49    inference(cnf_transformation,[],[f26])).
% 23.23/3.49  
% 23.23/3.49  fof(f64,plain,(
% 23.23/3.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 23.23/3.49    inference(equality_resolution,[],[f35])).
% 23.23/3.49  
% 23.23/3.49  fof(f37,plain,(
% 23.23/3.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f26])).
% 23.23/3.49  
% 23.23/3.49  fof(f38,plain,(
% 23.23/3.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.23/3.49    inference(cnf_transformation,[],[f26])).
% 23.23/3.49  
% 23.23/3.49  fof(f54,plain,(
% 23.23/3.49    r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3),
% 23.23/3.49    inference(cnf_transformation,[],[f33])).
% 23.23/3.49  
% 23.23/3.49  fof(f61,plain,(
% 23.23/3.49    r2_hidden(sK4,sK3) | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != sK3),
% 23.23/3.49    inference(definition_unfolding,[],[f54,f45,f56])).
% 23.23/3.49  
% 23.23/3.49  cnf(c_16,negated_conjecture,
% 23.23/3.49      ( ~ r2_hidden(sK4,sK3)
% 23.23/3.49      | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3 ),
% 23.23/3.49      inference(cnf_transformation,[],[f62]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_196,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_11,plain,
% 23.23/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 23.23/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_1054,plain,
% 23.23/3.49      ( X0 != X1 | k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X0 ),
% 23.23/3.49      inference(resolution,[status(thm)],[c_196,c_11]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_199,plain,
% 23.23/3.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 23.23/3.49      theory(equality) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_7225,plain,
% 23.23/3.49      ( ~ r1_xboole_0(X0,X1)
% 23.23/3.49      | r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)),X1)
% 23.23/3.49      | X0 != X2 ),
% 23.23/3.49      inference(resolution,[status(thm)],[c_1054,c_199]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_88040,plain,
% 23.23/3.49      ( ~ r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))),X0)
% 23.23/3.49      | r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),X0)
% 23.23/3.49      | ~ r2_hidden(sK4,sK3) ),
% 23.23/3.49      inference(resolution,[status(thm)],[c_16,c_7225]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_12,plain,
% 23.23/3.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 23.23/3.49      inference(cnf_transformation,[],[f58]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_89601,plain,
% 23.23/3.49      ( r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4))
% 23.23/3.49      | ~ r2_hidden(sK4,sK3) ),
% 23.23/3.49      inference(resolution,[status(thm)],[c_88040,c_12]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_8172,plain,
% 23.23/3.49      ( ~ r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
% 23.23/3.49      | r1_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))
% 23.23/3.49      | X2 != X0 ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_199]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_65417,plain,
% 23.23/3.49      ( ~ r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
% 23.23/3.49      | r1_xboole_0(sK3,k2_enumset1(X1,X1,X1,X1))
% 23.23/3.49      | sK3 != X0 ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_8172]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_83542,plain,
% 23.23/3.49      ( ~ r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(X0,X0,X0,X0))
% 23.23/3.49      | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0))
% 23.23/3.49      | sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_65417]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_83544,plain,
% 23.23/3.49      ( ~ r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4))
% 23.23/3.49      | r1_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 23.23/3.49      | sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_83542]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_6,plain,
% 23.23/3.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 23.23/3.49      inference(cnf_transformation,[],[f40]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_6763,plain,
% 23.23/3.49      ( ~ r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
% 23.23/3.49      | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X0) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_6]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_41749,plain,
% 23.23/3.49      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 23.23/3.49      | ~ r1_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_6763]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_7,plain,
% 23.23/3.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 23.23/3.49      inference(cnf_transformation,[],[f43]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_1489,plain,
% 23.23/3.49      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
% 23.23/3.49      | ~ r2_hidden(X2,X1)
% 23.23/3.49      | ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_7]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_7671,plain,
% 23.23/3.49      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)
% 23.23/3.49      | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),X0)
% 23.23/3.49      | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_1489]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_18827,plain,
% 23.23/3.49      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 23.23/3.49      | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4))
% 23.23/3.49      | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_7671]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_18828,plain,
% 23.23/3.49      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) != iProver_top
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) != iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_18827]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_7651,plain,
% 23.23/3.49      ( ~ r1_xboole_0(sK3,X0)
% 23.23/3.49      | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),X0)
% 23.23/3.49      | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_7]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_18810,plain,
% 23.23/3.49      ( ~ r1_xboole_0(sK3,k1_xboole_0)
% 23.23/3.49      | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3)
% 23.23/3.49      | ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_7651]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_18811,plain,
% 23.23/3.49      ( r1_xboole_0(sK3,k1_xboole_0) != iProver_top
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) != iProver_top
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_18810]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_2322,plain,
% 23.23/3.49      ( r1_xboole_0(X0,X1)
% 23.23/3.49      | ~ r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1)
% 23.23/3.49      | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X1)) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_199]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_13603,plain,
% 23.23/3.49      ( ~ r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0)
% 23.23/3.49      | r1_xboole_0(sK3,k1_xboole_0)
% 23.23/3.49      | sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_2322]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_13604,plain,
% 23.23/3.49      ( sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))
% 23.23/3.49      | r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
% 23.23/3.49      | r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_13603]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_10507,plain,
% 23.23/3.49      ( r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_12]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_10508,plain,
% 23.23/3.49      ( r1_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_10507]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_14,plain,
% 23.23/3.49      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 23.23/3.49      inference(cnf_transformation,[],[f60]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_5918,plain,
% 23.23/3.49      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 23.23/3.49      | r2_hidden(sK4,sK3) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_14]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_5919,plain,
% 23.23/3.49      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = iProver_top
% 23.23/3.49      | r2_hidden(sK4,sK3) = iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_5918]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_13,plain,
% 23.23/3.49      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 23.23/3.49      inference(cnf_transformation,[],[f59]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_2826,plain,
% 23.23/3.49      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 23.23/3.49      | ~ r2_hidden(sK4,sK3) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_13]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_5,plain,
% 23.23/3.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 23.23/3.49      inference(cnf_transformation,[],[f65]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_1469,plain,
% 23.23/3.49      ( ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0))
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_5]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_1470,plain,
% 23.23/3.49      ( r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0)) != iProver_top
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) = iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_1469]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_4,plain,
% 23.23/3.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 23.23/3.49      inference(cnf_transformation,[],[f64]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_1466,plain,
% 23.23/3.49      ( ~ r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0))
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_4]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_1467,plain,
% 23.23/3.49      ( r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0)) != iProver_top
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_2,plain,
% 23.23/3.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 23.23/3.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.23/3.49      | k3_xboole_0(X0,X1) = X2 ),
% 23.23/3.49      inference(cnf_transformation,[],[f37]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_920,plain,
% 23.23/3.49      ( r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0))
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3)
% 23.23/3.49      | k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k1_xboole_0) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_924,plain,
% 23.23/3.49      ( k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k1_xboole_0)
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0)) = iProver_top
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),sK3) = iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_920]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_1,plain,
% 23.23/3.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 23.23/3.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.23/3.49      | k3_xboole_0(X0,X1) = X2 ),
% 23.23/3.49      inference(cnf_transformation,[],[f38]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_921,plain,
% 23.23/3.49      ( r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4))
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0))
% 23.23/3.49      | k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k1_xboole_0) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_1]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_922,plain,
% 23.23/3.49      ( k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k1_xboole_0)
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 23.23/3.49      | r2_hidden(sK0(sK3,k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(sK3,k1_xboole_0)),k3_xboole_0(sK3,k1_xboole_0)) = iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_200,plain,
% 23.23/3.49      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 23.23/3.49      theory(equality) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_916,plain,
% 23.23/3.49      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))
% 23.23/3.49      | k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != k3_xboole_0(sK3,k1_xboole_0)
% 23.23/3.49      | sK3 != sK3 ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_200]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_733,plain,
% 23.23/3.49      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != X0
% 23.23/3.49      | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3
% 23.23/3.49      | sK3 != X0 ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_196]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_836,plain,
% 23.23/3.49      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))
% 23.23/3.49      | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3
% 23.23/3.49      | sK3 != k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_733]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_827,plain,
% 23.23/3.49      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) = sK3 ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_11]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_758,plain,
% 23.23/3.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_196]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_759,plain,
% 23.23/3.49      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_758]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_826,plain,
% 23.23/3.49      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) != sK3
% 23.23/3.49      | sK3 = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))
% 23.23/3.49      | sK3 != sK3 ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_759]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_195,plain,( X0 = X0 ),theory(equality) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_760,plain,
% 23.23/3.49      ( sK3 = sK3 ),
% 23.23/3.49      inference(instantiation,[status(thm)],[c_195]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_15,negated_conjecture,
% 23.23/3.49      ( r2_hidden(sK4,sK3)
% 23.23/3.49      | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != sK3 ),
% 23.23/3.49      inference(cnf_transformation,[],[f61]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(c_17,plain,
% 23.23/3.49      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3
% 23.23/3.49      | r2_hidden(sK4,sK3) != iProver_top ),
% 23.23/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.23/3.49  
% 23.23/3.49  cnf(contradiction,plain,
% 23.23/3.49      ( $false ),
% 23.23/3.49      inference(minisat,
% 23.23/3.49                [status(thm)],
% 23.23/3.49                [c_89601,c_83544,c_41749,c_18828,c_18811,c_13604,c_10508,
% 23.23/3.49                 c_5919,c_2826,c_1470,c_1467,c_924,c_922,c_916,c_836,
% 23.23/3.49                 c_827,c_826,c_760,c_15,c_17]) ).
% 23.23/3.49  
% 23.23/3.49  
% 23.23/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.23/3.49  
% 23.23/3.49  ------                               Statistics
% 23.23/3.49  
% 23.23/3.49  ------ Selected
% 23.23/3.49  
% 23.23/3.49  total_time:                             2.788
% 23.23/3.49  
%------------------------------------------------------------------------------
