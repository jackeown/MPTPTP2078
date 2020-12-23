%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:47 EST 2020

% Result     : Theorem 35.26s
% Output     : CNFRefutation 35.26s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 879 expanded)
%              Number of clauses        :   57 ( 129 expanded)
%              Number of leaves         :   23 ( 292 expanded)
%              Depth                    :   16
%              Number of atoms          :  403 (1481 expanded)
%              Number of equality atoms :  223 (1182 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f69])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f22,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK3 != sK4
      & k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( sK3 != sK4
    & k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f36])).

fof(f67,plain,(
    k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f67,f71,f71,f71])).

fof(f9,axiom,(
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
    inference(nnf_transformation,[],[f9])).

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

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f95,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f93,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f82])).

fof(f94,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f93])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f86,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f76])).

fof(f87,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f86])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f25])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_361,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2788,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(X2,X1)
    | r1_xboole_0(X3,k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1))
    | X3 != X2 ),
    inference(resolution,[status(thm)],[c_361,c_24])).

cnf(c_26,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_26945,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)
    | r1_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) ),
    inference(resolution,[status(thm)],[c_2788,c_26])).

cnf(c_363,plain,
    ( X0 != X1
    | k2_xboole_0(X0,X2) = k2_xboole_0(X1,X2) ),
    theory(equality)).

cnf(c_2798,plain,
    ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
    | r1_xboole_0(X3,k2_xboole_0(X4,X2))
    | X3 != X0
    | X4 != X1 ),
    inference(resolution,[status(thm)],[c_361,c_363])).

cnf(c_28222,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_xboole_0(X2,k2_xboole_0(X3,X1))
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)
    | X3 != k3_enumset1(X0,X0,X0,X0,X0)
    | X2 != k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_26945,c_2798])).

cnf(c_359,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_358,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1464,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_359,c_358])).

cnf(c_7985,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_1464,c_26])).

cnf(c_50468,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X2,X1))
    | X2 != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(resolution,[status(thm)],[c_28222,c_7985])).

cnf(c_55680,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X0)) ),
    inference(resolution,[status(thm)],[c_50468,c_26])).

cnf(c_2796,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_361,c_358])).

cnf(c_10104,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
    | r1_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X0) ),
    inference(resolution,[status(thm)],[c_2796,c_26])).

cnf(c_23396,plain,
    ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X3,X2))
    | X1 != X3
    | X0 != k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_2798,c_10104])).

cnf(c_31817,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X0,X1))
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X2,X1))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_23396,c_7985])).

cnf(c_55747,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X1,X0))
    | X1 != k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_55680,c_31817])).

cnf(c_364,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
    theory(equality)).

cnf(c_7427,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != k3_enumset1(X1,X3,X5,X7,X9)
    | k3_enumset1(X0,X2,X4,X6,X8) = X10 ),
    inference(resolution,[status(thm)],[c_364,c_359])).

cnf(c_54249,plain,
    ( X0 != sK3
    | X1 != sK3
    | X2 != sK3
    | X3 != sK3
    | X4 != sK3
    | k3_enumset1(X1,X4,X0,X2,X3) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_7427,c_26])).

cnf(c_57125,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X0))
    | X2 != sK3
    | X3 != sK3
    | X4 != sK3
    | X5 != sK3
    | X1 != sK3 ),
    inference(resolution,[status(thm)],[c_55747,c_54249])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_31,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_34,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_362,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2844,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | r2_hidden(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_362,c_26])).

cnf(c_16,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3064,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_2844,c_16])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3076,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_3064,c_7])).

cnf(c_3078,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3076])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7604,plain,
    ( r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_57107,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(resolution,[status(thm)],[c_55747,c_7985])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7961,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_1464,c_2])).

cnf(c_1462,plain,
    ( X0 != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = X0 ),
    inference(resolution,[status(thm)],[c_359,c_26])).

cnf(c_1473,plain,
    ( X0 != X1
    | X1 != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = X0 ),
    inference(resolution,[status(thm)],[c_1462,c_359])).

cnf(c_11,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1688,plain,
    ( X0 != k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))
    | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = X0 ),
    inference(resolution,[status(thm)],[c_1473,c_11])).

cnf(c_107961,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0))
    | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7961,c_1688])).

cnf(c_132682,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_57125,c_31,c_34,c_3078,c_7604,c_57107,c_107961])).

cnf(c_10143,plain,
    ( r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
    | ~ r1_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X0) ),
    inference(resolution,[status(thm)],[c_2796,c_7985])).

cnf(c_9,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11443,plain,
    ( r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    inference(resolution,[status(thm)],[c_10143,c_9])).

cnf(c_132700,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    inference(resolution,[status(thm)],[c_132682,c_11443])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1073,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_enumset1(X0,X0,X0,X2,X3))
    | r2_hidden(X0,k5_xboole_0(k3_enumset1(X0,X0,X0,X2,X3),X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1435,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,X1,X2))
    | r2_hidden(sK3,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,X1,X2),X0)) ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_1778,plain,
    ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,X0,X1))
    | r2_hidden(sK3,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,X0,X1),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_1780,plain,
    ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | r2_hidden(sK3,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_983,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_25,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_132700,c_1780,c_983,c_34,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.26/4.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.26/4.98  
% 35.26/4.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.26/4.98  
% 35.26/4.98  ------  iProver source info
% 35.26/4.98  
% 35.26/4.98  git: date: 2020-06-30 10:37:57 +0100
% 35.26/4.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.26/4.98  git: non_committed_changes: false
% 35.26/4.98  git: last_make_outside_of_git: false
% 35.26/4.98  
% 35.26/4.98  ------ 
% 35.26/4.98  ------ Parsing...
% 35.26/4.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.26/4.98  
% 35.26/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.26/4.98  
% 35.26/4.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.26/4.98  
% 35.26/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.26/4.98  ------ Proving...
% 35.26/4.98  ------ Problem Properties 
% 35.26/4.98  
% 35.26/4.98  
% 35.26/4.98  clauses                                 27
% 35.26/4.98  conjectures                             2
% 35.26/4.98  EPR                                     1
% 35.26/4.98  Horn                                    20
% 35.26/4.98  unary                                   10
% 35.26/4.98  binary                                  6
% 35.26/4.98  lits                                    58
% 35.26/4.98  lits eq                                 26
% 35.26/4.98  fd_pure                                 0
% 35.26/4.98  fd_pseudo                               0
% 35.26/4.98  fd_cond                                 0
% 35.26/4.98  fd_pseudo_cond                          6
% 35.26/4.98  AC symbols                              1
% 35.26/4.98  
% 35.26/4.98  ------ Input Options Time Limit: Unbounded
% 35.26/4.98  
% 35.26/4.98  
% 35.26/4.98  ------ 
% 35.26/4.98  Current options:
% 35.26/4.98  ------ 
% 35.26/4.98  
% 35.26/4.98  
% 35.26/4.98  
% 35.26/4.98  
% 35.26/4.98  ------ Proving...
% 35.26/4.98  
% 35.26/4.98  
% 35.26/4.98  % SZS status Theorem for theBenchmark.p
% 35.26/4.98  
% 35.26/4.98  % SZS output start CNFRefutation for theBenchmark.p
% 35.26/4.98  
% 35.26/4.98  fof(f14,axiom,(
% 35.26/4.98    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f21,plain,(
% 35.26/4.98    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 35.26/4.98    inference(ennf_transformation,[],[f14])).
% 35.26/4.98  
% 35.26/4.98  fof(f66,plain,(
% 35.26/4.98    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 35.26/4.98    inference(cnf_transformation,[],[f21])).
% 35.26/4.98  
% 35.26/4.98  fof(f10,axiom,(
% 35.26/4.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f62,plain,(
% 35.26/4.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 35.26/4.98    inference(cnf_transformation,[],[f10])).
% 35.26/4.98  
% 35.26/4.98  fof(f11,axiom,(
% 35.26/4.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f63,plain,(
% 35.26/4.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 35.26/4.98    inference(cnf_transformation,[],[f11])).
% 35.26/4.98  
% 35.26/4.98  fof(f12,axiom,(
% 35.26/4.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f64,plain,(
% 35.26/4.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.26/4.98    inference(cnf_transformation,[],[f12])).
% 35.26/4.98  
% 35.26/4.98  fof(f13,axiom,(
% 35.26/4.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f65,plain,(
% 35.26/4.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.26/4.98    inference(cnf_transformation,[],[f13])).
% 35.26/4.98  
% 35.26/4.98  fof(f69,plain,(
% 35.26/4.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 35.26/4.98    inference(definition_unfolding,[],[f64,f65])).
% 35.26/4.98  
% 35.26/4.98  fof(f70,plain,(
% 35.26/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 35.26/4.98    inference(definition_unfolding,[],[f63,f69])).
% 35.26/4.98  
% 35.26/4.98  fof(f71,plain,(
% 35.26/4.98    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 35.26/4.98    inference(definition_unfolding,[],[f62,f70])).
% 35.26/4.98  
% 35.26/4.98  fof(f84,plain,(
% 35.26/4.98    ( ! [X0,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 35.26/4.98    inference(definition_unfolding,[],[f66,f71])).
% 35.26/4.98  
% 35.26/4.98  fof(f15,conjecture,(
% 35.26/4.98    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f16,negated_conjecture,(
% 35.26/4.98    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 35.26/4.98    inference(negated_conjecture,[],[f15])).
% 35.26/4.98  
% 35.26/4.98  fof(f22,plain,(
% 35.26/4.98    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 35.26/4.98    inference(ennf_transformation,[],[f16])).
% 35.26/4.98  
% 35.26/4.98  fof(f36,plain,(
% 35.26/4.98    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK3 != sK4 & k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3))),
% 35.26/4.98    introduced(choice_axiom,[])).
% 35.26/4.98  
% 35.26/4.98  fof(f37,plain,(
% 35.26/4.98    sK3 != sK4 & k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3)),
% 35.26/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f36])).
% 35.26/4.98  
% 35.26/4.98  fof(f67,plain,(
% 35.26/4.98    k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3)),
% 35.26/4.98    inference(cnf_transformation,[],[f37])).
% 35.26/4.98  
% 35.26/4.98  fof(f85,plain,(
% 35.26/4.98    k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 35.26/4.98    inference(definition_unfolding,[],[f67,f71,f71,f71])).
% 35.26/4.98  
% 35.26/4.98  fof(f9,axiom,(
% 35.26/4.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f32,plain,(
% 35.26/4.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 35.26/4.98    inference(nnf_transformation,[],[f9])).
% 35.26/4.98  
% 35.26/4.98  fof(f33,plain,(
% 35.26/4.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 35.26/4.98    inference(rectify,[],[f32])).
% 35.26/4.98  
% 35.26/4.98  fof(f34,plain,(
% 35.26/4.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 35.26/4.98    introduced(choice_axiom,[])).
% 35.26/4.98  
% 35.26/4.98  fof(f35,plain,(
% 35.26/4.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 35.26/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 35.26/4.98  
% 35.26/4.98  fof(f58,plain,(
% 35.26/4.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 35.26/4.98    inference(cnf_transformation,[],[f35])).
% 35.26/4.98  
% 35.26/4.98  fof(f83,plain,(
% 35.26/4.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 35.26/4.98    inference(definition_unfolding,[],[f58,f71])).
% 35.26/4.98  
% 35.26/4.98  fof(f95,plain,(
% 35.26/4.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 35.26/4.98    inference(equality_resolution,[],[f83])).
% 35.26/4.98  
% 35.26/4.98  fof(f59,plain,(
% 35.26/4.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 35.26/4.98    inference(cnf_transformation,[],[f35])).
% 35.26/4.98  
% 35.26/4.98  fof(f82,plain,(
% 35.26/4.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 35.26/4.98    inference(definition_unfolding,[],[f59,f71])).
% 35.26/4.98  
% 35.26/4.98  fof(f93,plain,(
% 35.26/4.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 35.26/4.98    inference(equality_resolution,[],[f82])).
% 35.26/4.98  
% 35.26/4.98  fof(f94,plain,(
% 35.26/4.98    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 35.26/4.98    inference(equality_resolution,[],[f93])).
% 35.26/4.98  
% 35.26/4.98  fof(f8,axiom,(
% 35.26/4.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f20,plain,(
% 35.26/4.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 35.26/4.98    inference(ennf_transformation,[],[f8])).
% 35.26/4.98  
% 35.26/4.98  fof(f27,plain,(
% 35.26/4.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.26/4.98    inference(nnf_transformation,[],[f20])).
% 35.26/4.98  
% 35.26/4.98  fof(f28,plain,(
% 35.26/4.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.26/4.98    inference(flattening,[],[f27])).
% 35.26/4.98  
% 35.26/4.98  fof(f29,plain,(
% 35.26/4.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.26/4.98    inference(rectify,[],[f28])).
% 35.26/4.98  
% 35.26/4.98  fof(f30,plain,(
% 35.26/4.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 35.26/4.98    introduced(choice_axiom,[])).
% 35.26/4.98  
% 35.26/4.98  fof(f31,plain,(
% 35.26/4.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.26/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 35.26/4.98  
% 35.26/4.98  fof(f53,plain,(
% 35.26/4.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 35.26/4.98    inference(cnf_transformation,[],[f31])).
% 35.26/4.98  
% 35.26/4.98  fof(f76,plain,(
% 35.26/4.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 35.26/4.98    inference(definition_unfolding,[],[f53,f69])).
% 35.26/4.98  
% 35.26/4.98  fof(f86,plain,(
% 35.26/4.98    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 35.26/4.98    inference(equality_resolution,[],[f76])).
% 35.26/4.98  
% 35.26/4.98  fof(f87,plain,(
% 35.26/4.98    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 35.26/4.98    inference(equality_resolution,[],[f86])).
% 35.26/4.98  
% 35.26/4.98  fof(f4,axiom,(
% 35.26/4.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f17,plain,(
% 35.26/4.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.26/4.98    inference(rectify,[],[f4])).
% 35.26/4.98  
% 35.26/4.98  fof(f19,plain,(
% 35.26/4.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.26/4.98    inference(ennf_transformation,[],[f17])).
% 35.26/4.98  
% 35.26/4.98  fof(f25,plain,(
% 35.26/4.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 35.26/4.98    introduced(choice_axiom,[])).
% 35.26/4.98  
% 35.26/4.98  fof(f26,plain,(
% 35.26/4.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.26/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f25])).
% 35.26/4.98  
% 35.26/4.98  fof(f46,plain,(
% 35.26/4.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 35.26/4.98    inference(cnf_transformation,[],[f26])).
% 35.26/4.98  
% 35.26/4.98  fof(f2,axiom,(
% 35.26/4.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f23,plain,(
% 35.26/4.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.26/4.98    inference(nnf_transformation,[],[f2])).
% 35.26/4.98  
% 35.26/4.98  fof(f40,plain,(
% 35.26/4.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.26/4.98    inference(cnf_transformation,[],[f23])).
% 35.26/4.98  
% 35.26/4.98  fof(f39,plain,(
% 35.26/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.26/4.98    inference(cnf_transformation,[],[f23])).
% 35.26/4.98  
% 35.26/4.98  fof(f7,axiom,(
% 35.26/4.98    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f49,plain,(
% 35.26/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 35.26/4.98    inference(cnf_transformation,[],[f7])).
% 35.26/4.98  
% 35.26/4.98  fof(f5,axiom,(
% 35.26/4.98    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f47,plain,(
% 35.26/4.98    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 35.26/4.98    inference(cnf_transformation,[],[f5])).
% 35.26/4.98  
% 35.26/4.98  fof(f3,axiom,(
% 35.26/4.98    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 35.26/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.26/4.98  
% 35.26/4.98  fof(f18,plain,(
% 35.26/4.98    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 35.26/4.98    inference(ennf_transformation,[],[f3])).
% 35.26/4.98  
% 35.26/4.98  fof(f24,plain,(
% 35.26/4.98    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 35.26/4.98    inference(nnf_transformation,[],[f18])).
% 35.26/4.98  
% 35.26/4.98  fof(f43,plain,(
% 35.26/4.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 35.26/4.98    inference(cnf_transformation,[],[f24])).
% 35.26/4.98  
% 35.26/4.98  fof(f68,plain,(
% 35.26/4.98    sK3 != sK4),
% 35.26/4.98    inference(cnf_transformation,[],[f37])).
% 35.26/4.98  
% 35.26/4.98  cnf(c_361,plain,
% 35.26/4.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.26/4.98      theory(equality) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_24,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,X1)
% 35.26/4.98      | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 ),
% 35.26/4.98      inference(cnf_transformation,[],[f84]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_2788,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,X1)
% 35.26/4.98      | ~ r1_xboole_0(X2,X1)
% 35.26/4.98      | r1_xboole_0(X3,k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1))
% 35.26/4.98      | X3 != X2 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_361,c_24]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_26,negated_conjecture,
% 35.26/4.98      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 35.26/4.98      inference(cnf_transformation,[],[f85]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_26945,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,X1)
% 35.26/4.98      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)
% 35.26/4.98      | r1_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_2788,c_26]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_363,plain,
% 35.26/4.98      ( X0 != X1 | k2_xboole_0(X0,X2) = k2_xboole_0(X1,X2) ),
% 35.26/4.98      theory(equality) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_2798,plain,
% 35.26/4.98      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
% 35.26/4.98      | r1_xboole_0(X3,k2_xboole_0(X4,X2))
% 35.26/4.98      | X3 != X0
% 35.26/4.98      | X4 != X1 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_361,c_363]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_28222,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,X1)
% 35.26/4.98      | r1_xboole_0(X2,k2_xboole_0(X3,X1))
% 35.26/4.98      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)
% 35.26/4.98      | X3 != k3_enumset1(X0,X0,X0,X0,X0)
% 35.26/4.98      | X2 != k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_26945,c_2798]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_359,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_358,plain,( X0 = X0 ),theory(equality) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_1464,plain,
% 35.26/4.98      ( X0 != X1 | X1 = X0 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_359,c_358]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_7985,plain,
% 35.26/4.98      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_1464,c_26]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_50468,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,X1)
% 35.26/4.98      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)
% 35.26/4.98      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X2,X1))
% 35.26/4.98      | X2 != k3_enumset1(X0,X0,X0,X0,X0) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_28222,c_7985]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_55680,plain,
% 35.26/4.98      ( ~ r2_hidden(sK3,X0)
% 35.26/4.98      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
% 35.26/4.98      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X0)) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_50468,c_26]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_2796,plain,
% 35.26/4.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_361,c_358]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_10104,plain,
% 35.26/4.98      ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
% 35.26/4.98      | r1_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X0) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_2796,c_26]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_23396,plain,
% 35.26/4.98      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
% 35.26/4.98      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X3,X2))
% 35.26/4.98      | X1 != X3
% 35.26/4.98      | X0 != k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_2798,c_10104]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_31817,plain,
% 35.26/4.98      ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X0,X1))
% 35.26/4.98      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X2,X1))
% 35.26/4.98      | X2 != X0 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_23396,c_7985]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_55747,plain,
% 35.26/4.98      ( ~ r2_hidden(sK3,X0)
% 35.26/4.98      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
% 35.26/4.98      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(X1,X0))
% 35.26/4.98      | X1 != k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_55680,c_31817]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_364,plain,
% 35.26/4.98      ( X0 != X1
% 35.26/4.98      | X2 != X3
% 35.26/4.98      | X4 != X5
% 35.26/4.98      | X6 != X7
% 35.26/4.98      | X8 != X9
% 35.26/4.98      | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
% 35.26/4.98      theory(equality) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_7427,plain,
% 35.26/4.98      ( X0 != X1
% 35.26/4.98      | X2 != X3
% 35.26/4.98      | X4 != X5
% 35.26/4.98      | X6 != X7
% 35.26/4.98      | X8 != X9
% 35.26/4.98      | X10 != k3_enumset1(X1,X3,X5,X7,X9)
% 35.26/4.98      | k3_enumset1(X0,X2,X4,X6,X8) = X10 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_364,c_359]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_54249,plain,
% 35.26/4.98      ( X0 != sK3
% 35.26/4.98      | X1 != sK3
% 35.26/4.98      | X2 != sK3
% 35.26/4.98      | X3 != sK3
% 35.26/4.98      | X4 != sK3
% 35.26/4.98      | k3_enumset1(X1,X4,X0,X2,X3) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_7427,c_26]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_57125,plain,
% 35.26/4.98      ( ~ r2_hidden(sK3,X0)
% 35.26/4.98      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
% 35.26/4.98      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X0))
% 35.26/4.98      | X2 != sK3
% 35.26/4.98      | X3 != sK3
% 35.26/4.98      | X4 != sK3
% 35.26/4.98      | X5 != sK3
% 35.26/4.98      | X1 != sK3 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_55747,c_54249]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_23,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 35.26/4.98      inference(cnf_transformation,[],[f95]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_31,plain,
% 35.26/4.98      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 35.26/4.98      inference(instantiation,[status(thm)],[c_23]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_22,plain,
% 35.26/4.98      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 35.26/4.98      inference(cnf_transformation,[],[f94]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_34,plain,
% 35.26/4.98      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 35.26/4.98      inference(instantiation,[status(thm)],[c_22]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_362,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.26/4.98      theory(equality) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_2844,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 35.26/4.98      | r2_hidden(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
% 35.26/4.98      | X1 != X0 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_362,c_26]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_16,plain,
% 35.26/4.98      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
% 35.26/4.98      inference(cnf_transformation,[],[f87]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_3064,plain,
% 35.26/4.98      ( r2_hidden(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
% 35.26/4.98      | X0 != sK3 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_2844,c_16]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_7,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 35.26/4.98      inference(cnf_transformation,[],[f46]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_3076,plain,
% 35.26/4.98      ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 35.26/4.98      | X0 != sK3 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_3064,c_7]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_3078,plain,
% 35.26/4.98      ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 35.26/4.98      | sK3 != sK3 ),
% 35.26/4.98      inference(instantiation,[status(thm)],[c_3076]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_1,plain,
% 35.26/4.98      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 35.26/4.98      inference(cnf_transformation,[],[f40]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_7604,plain,
% 35.26/4.98      ( r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 35.26/4.98      | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != k1_xboole_0 ),
% 35.26/4.98      inference(instantiation,[status(thm)],[c_1]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_57107,plain,
% 35.26/4.98      ( ~ r2_hidden(sK3,X0)
% 35.26/4.98      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
% 35.26/4.98      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_55747,c_7985]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_2,plain,
% 35.26/4.98      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 35.26/4.98      inference(cnf_transformation,[],[f39]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_7961,plain,
% 35.26/4.98      ( ~ r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_1464,c_2]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_1462,plain,
% 35.26/4.98      ( X0 != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 35.26/4.98      | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = X0 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_359,c_26]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_1473,plain,
% 35.26/4.98      ( X0 != X1
% 35.26/4.98      | X1 != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 35.26/4.98      | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = X0 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_1462,c_359]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_11,plain,
% 35.26/4.98      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 35.26/4.98      inference(cnf_transformation,[],[f49]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_1688,plain,
% 35.26/4.98      ( X0 != k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))
% 35.26/4.98      | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = X0 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_1473,c_11]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_107961,plain,
% 35.26/4.98      ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0))
% 35.26/4.98      | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_7961,c_1688]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_132682,plain,
% 35.26/4.98      ( ~ r2_hidden(sK3,X0)
% 35.26/4.98      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0) ),
% 35.26/4.98      inference(global_propositional_subsumption,
% 35.26/4.98                [status(thm)],
% 35.26/4.98                [c_57125,c_31,c_34,c_3078,c_7604,c_57107,c_107961]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_10143,plain,
% 35.26/4.98      ( r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
% 35.26/4.98      | ~ r1_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X0) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_2796,c_7985]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_9,plain,
% 35.26/4.98      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 35.26/4.98      inference(cnf_transformation,[],[f47]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_11443,plain,
% 35.26/4.98      ( r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_10143,c_9]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_132700,plain,
% 35.26/4.98      ( ~ r2_hidden(sK3,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
% 35.26/4.98      inference(resolution,[status(thm)],[c_132682,c_11443]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_4,plain,
% 35.26/4.98      ( ~ r2_hidden(X0,X1)
% 35.26/4.98      | r2_hidden(X0,X2)
% 35.26/4.98      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 35.26/4.98      inference(cnf_transformation,[],[f43]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_1073,plain,
% 35.26/4.98      ( r2_hidden(X0,X1)
% 35.26/4.98      | ~ r2_hidden(X0,k3_enumset1(X0,X0,X0,X2,X3))
% 35.26/4.98      | r2_hidden(X0,k5_xboole_0(k3_enumset1(X0,X0,X0,X2,X3),X1)) ),
% 35.26/4.98      inference(instantiation,[status(thm)],[c_4]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_1435,plain,
% 35.26/4.98      ( r2_hidden(sK3,X0)
% 35.26/4.98      | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,X1,X2))
% 35.26/4.98      | r2_hidden(sK3,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,X1,X2),X0)) ),
% 35.26/4.98      inference(instantiation,[status(thm)],[c_1073]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_1778,plain,
% 35.26/4.98      ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 35.26/4.98      | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,X0,X1))
% 35.26/4.98      | r2_hidden(sK3,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,X0,X1),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
% 35.26/4.98      inference(instantiation,[status(thm)],[c_1435]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_1780,plain,
% 35.26/4.98      ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 35.26/4.98      | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 35.26/4.98      | r2_hidden(sK3,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
% 35.26/4.98      inference(instantiation,[status(thm)],[c_1778]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_983,plain,
% 35.26/4.98      ( ~ r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | sK3 = sK4 ),
% 35.26/4.98      inference(instantiation,[status(thm)],[c_23]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(c_25,negated_conjecture,
% 35.26/4.98      ( sK3 != sK4 ),
% 35.26/4.98      inference(cnf_transformation,[],[f68]) ).
% 35.26/4.98  
% 35.26/4.98  cnf(contradiction,plain,
% 35.26/4.98      ( $false ),
% 35.26/4.98      inference(minisat,[status(thm)],[c_132700,c_1780,c_983,c_34,c_25]) ).
% 35.26/4.98  
% 35.26/4.98  
% 35.26/4.98  % SZS output end CNFRefutation for theBenchmark.p
% 35.26/4.98  
% 35.26/4.98  ------                               Statistics
% 35.26/4.98  
% 35.26/4.98  ------ Selected
% 35.26/4.98  
% 35.26/4.98  total_time:                             4.304
% 35.26/4.98  
%------------------------------------------------------------------------------
