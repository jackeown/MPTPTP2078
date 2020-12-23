%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:01 EST 2020

% Result     : Theorem 11.90s
% Output     : CNFRefutation 11.90s
% Verified   : 
% Statistics : Number of formulae       :  141 (2438 expanded)
%              Number of clauses        :   68 ( 636 expanded)
%              Number of leaves         :   19 ( 640 expanded)
%              Depth                    :   23
%              Number of atoms          :  313 (4978 expanded)
%              Number of equality atoms :  140 (2308 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f60,f60])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f31])).

fof(f59,plain,(
    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f80,plain,(
    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))))) != sK3 ),
    inference(definition_unfolding,[],[f59,f60,f45,f63,f63])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f58,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f60,f62])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_805,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_806,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_809,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3220,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_809])).

cnf(c_4515,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_3220])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_800,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4755,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_4515,c_800])).

cnf(c_4767,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4755,c_4755])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))))) != sK3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1415,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(demodulation,[status(thm)],[c_0,c_19])).

cnf(c_39306,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(demodulation,[status(thm)],[c_4767,c_1415])).

cnf(c_13,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_802,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_804,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1264,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_802,c_804])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1416,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_1748,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1264,c_1416])).

cnf(c_1747,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_802])).

cnf(c_1815,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1747])).

cnf(c_1819,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1815,c_804])).

cnf(c_1863,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1819,c_12])).

cnf(c_2766,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1748,c_1748,c_1863])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_801,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2779,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_801])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_807,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3100,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2779,c_807])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_52,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_808,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3108,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_808])).

cnf(c_3358,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3100,c_52,c_3108])).

cnf(c_3366,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_3358])).

cnf(c_3499,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_3366,c_800])).

cnf(c_3501,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_3499,c_1416])).

cnf(c_3620,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3501,c_2766])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_797,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_810,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_799,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2018,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_799,c_804])).

cnf(c_5233,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_810,c_2018])).

cnf(c_9023,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,X0)))) = k1_xboole_0
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_797,c_5233])).

cnf(c_9332,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) = k1_xboole_0
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9023,c_808])).

cnf(c_9611,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)))))) = k1_xboole_0
    | r2_hidden(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9332,c_809])).

cnf(c_12211,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_797,c_9611])).

cnf(c_12259,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12211,c_0])).

cnf(c_18,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1742,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1264,c_18])).

cnf(c_2373,plain,
    ( k3_tarski(k3_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1264,c_1742])).

cnf(c_1531,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_18,c_12])).

cnf(c_2376,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_2373,c_1531])).

cnf(c_12279,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))) ),
    inference(demodulation,[status(thm)],[c_12259,c_2376])).

cnf(c_17598,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK3)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK3)),X0)))) ),
    inference(superposition,[status(thm)],[c_3620,c_12279])).

cnf(c_17600,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK3),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK3),X0)))) ),
    inference(demodulation,[status(thm)],[c_17598,c_3499,c_3501,c_3620])).

cnf(c_17601,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
    inference(demodulation,[status(thm)],[c_17600,c_3499,c_3501,c_3620])).

cnf(c_39307,plain,
    ( sK3 != sK3 ),
    inference(light_normalisation,[status(thm)],[c_39306,c_17601])).

cnf(c_39308,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_39307])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:32:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.90/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.90/2.00  
% 11.90/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.90/2.00  
% 11.90/2.00  ------  iProver source info
% 11.90/2.00  
% 11.90/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.90/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.90/2.00  git: non_committed_changes: false
% 11.90/2.00  git: last_make_outside_of_git: false
% 11.90/2.00  
% 11.90/2.00  ------ 
% 11.90/2.00  
% 11.90/2.00  ------ Input Options
% 11.90/2.00  
% 11.90/2.00  --out_options                           all
% 11.90/2.00  --tptp_safe_out                         true
% 11.90/2.00  --problem_path                          ""
% 11.90/2.00  --include_path                          ""
% 11.90/2.00  --clausifier                            res/vclausify_rel
% 11.90/2.00  --clausifier_options                    ""
% 11.90/2.00  --stdin                                 false
% 11.90/2.00  --stats_out                             all
% 11.90/2.00  
% 11.90/2.00  ------ General Options
% 11.90/2.00  
% 11.90/2.00  --fof                                   false
% 11.90/2.00  --time_out_real                         305.
% 11.90/2.00  --time_out_virtual                      -1.
% 11.90/2.00  --symbol_type_check                     false
% 11.90/2.00  --clausify_out                          false
% 11.90/2.00  --sig_cnt_out                           false
% 11.90/2.00  --trig_cnt_out                          false
% 11.90/2.00  --trig_cnt_out_tolerance                1.
% 11.90/2.00  --trig_cnt_out_sk_spl                   false
% 11.90/2.00  --abstr_cl_out                          false
% 11.90/2.00  
% 11.90/2.00  ------ Global Options
% 11.90/2.00  
% 11.90/2.00  --schedule                              default
% 11.90/2.00  --add_important_lit                     false
% 11.90/2.00  --prop_solver_per_cl                    1000
% 11.90/2.00  --min_unsat_core                        false
% 11.90/2.00  --soft_assumptions                      false
% 11.90/2.00  --soft_lemma_size                       3
% 11.90/2.00  --prop_impl_unit_size                   0
% 11.90/2.00  --prop_impl_unit                        []
% 11.90/2.00  --share_sel_clauses                     true
% 11.90/2.00  --reset_solvers                         false
% 11.90/2.00  --bc_imp_inh                            [conj_cone]
% 11.90/2.00  --conj_cone_tolerance                   3.
% 11.90/2.00  --extra_neg_conj                        none
% 11.90/2.00  --large_theory_mode                     true
% 11.90/2.00  --prolific_symb_bound                   200
% 11.90/2.00  --lt_threshold                          2000
% 11.90/2.00  --clause_weak_htbl                      true
% 11.90/2.00  --gc_record_bc_elim                     false
% 11.90/2.00  
% 11.90/2.00  ------ Preprocessing Options
% 11.90/2.00  
% 11.90/2.00  --preprocessing_flag                    true
% 11.90/2.00  --time_out_prep_mult                    0.1
% 11.90/2.00  --splitting_mode                        input
% 11.90/2.00  --splitting_grd                         true
% 11.90/2.00  --splitting_cvd                         false
% 11.90/2.00  --splitting_cvd_svl                     false
% 11.90/2.00  --splitting_nvd                         32
% 11.90/2.00  --sub_typing                            true
% 11.90/2.00  --prep_gs_sim                           true
% 11.90/2.00  --prep_unflatten                        true
% 11.90/2.00  --prep_res_sim                          true
% 11.90/2.00  --prep_upred                            true
% 11.90/2.00  --prep_sem_filter                       exhaustive
% 11.90/2.00  --prep_sem_filter_out                   false
% 11.90/2.00  --pred_elim                             true
% 11.90/2.00  --res_sim_input                         true
% 11.90/2.00  --eq_ax_congr_red                       true
% 11.90/2.00  --pure_diseq_elim                       true
% 11.90/2.00  --brand_transform                       false
% 11.90/2.00  --non_eq_to_eq                          false
% 11.90/2.00  --prep_def_merge                        true
% 11.90/2.00  --prep_def_merge_prop_impl              false
% 11.90/2.00  --prep_def_merge_mbd                    true
% 11.90/2.00  --prep_def_merge_tr_red                 false
% 11.90/2.00  --prep_def_merge_tr_cl                  false
% 11.90/2.00  --smt_preprocessing                     true
% 11.90/2.00  --smt_ac_axioms                         fast
% 11.90/2.00  --preprocessed_out                      false
% 11.90/2.00  --preprocessed_stats                    false
% 11.90/2.00  
% 11.90/2.00  ------ Abstraction refinement Options
% 11.90/2.00  
% 11.90/2.00  --abstr_ref                             []
% 11.90/2.00  --abstr_ref_prep                        false
% 11.90/2.00  --abstr_ref_until_sat                   false
% 11.90/2.00  --abstr_ref_sig_restrict                funpre
% 11.90/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.90/2.00  --abstr_ref_under                       []
% 11.90/2.00  
% 11.90/2.00  ------ SAT Options
% 11.90/2.00  
% 11.90/2.00  --sat_mode                              false
% 11.90/2.00  --sat_fm_restart_options                ""
% 11.90/2.00  --sat_gr_def                            false
% 11.90/2.00  --sat_epr_types                         true
% 11.90/2.00  --sat_non_cyclic_types                  false
% 11.90/2.00  --sat_finite_models                     false
% 11.90/2.00  --sat_fm_lemmas                         false
% 11.90/2.00  --sat_fm_prep                           false
% 11.90/2.00  --sat_fm_uc_incr                        true
% 11.90/2.00  --sat_out_model                         small
% 11.90/2.00  --sat_out_clauses                       false
% 11.90/2.00  
% 11.90/2.00  ------ QBF Options
% 11.90/2.00  
% 11.90/2.00  --qbf_mode                              false
% 11.90/2.00  --qbf_elim_univ                         false
% 11.90/2.00  --qbf_dom_inst                          none
% 11.90/2.00  --qbf_dom_pre_inst                      false
% 11.90/2.00  --qbf_sk_in                             false
% 11.90/2.00  --qbf_pred_elim                         true
% 11.90/2.00  --qbf_split                             512
% 11.90/2.00  
% 11.90/2.00  ------ BMC1 Options
% 11.90/2.00  
% 11.90/2.00  --bmc1_incremental                      false
% 11.90/2.00  --bmc1_axioms                           reachable_all
% 11.90/2.00  --bmc1_min_bound                        0
% 11.90/2.00  --bmc1_max_bound                        -1
% 11.90/2.00  --bmc1_max_bound_default                -1
% 11.90/2.00  --bmc1_symbol_reachability              true
% 11.90/2.00  --bmc1_property_lemmas                  false
% 11.90/2.00  --bmc1_k_induction                      false
% 11.90/2.00  --bmc1_non_equiv_states                 false
% 11.90/2.00  --bmc1_deadlock                         false
% 11.90/2.00  --bmc1_ucm                              false
% 11.90/2.00  --bmc1_add_unsat_core                   none
% 11.90/2.00  --bmc1_unsat_core_children              false
% 11.90/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.90/2.00  --bmc1_out_stat                         full
% 11.90/2.00  --bmc1_ground_init                      false
% 11.90/2.00  --bmc1_pre_inst_next_state              false
% 11.90/2.00  --bmc1_pre_inst_state                   false
% 11.90/2.00  --bmc1_pre_inst_reach_state             false
% 11.90/2.00  --bmc1_out_unsat_core                   false
% 11.90/2.00  --bmc1_aig_witness_out                  false
% 11.90/2.00  --bmc1_verbose                          false
% 11.90/2.00  --bmc1_dump_clauses_tptp                false
% 11.90/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.90/2.00  --bmc1_dump_file                        -
% 11.90/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.90/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.90/2.00  --bmc1_ucm_extend_mode                  1
% 11.90/2.00  --bmc1_ucm_init_mode                    2
% 11.90/2.00  --bmc1_ucm_cone_mode                    none
% 11.90/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.90/2.00  --bmc1_ucm_relax_model                  4
% 11.90/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.90/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.90/2.00  --bmc1_ucm_layered_model                none
% 11.90/2.00  --bmc1_ucm_max_lemma_size               10
% 11.90/2.00  
% 11.90/2.00  ------ AIG Options
% 11.90/2.00  
% 11.90/2.00  --aig_mode                              false
% 11.90/2.00  
% 11.90/2.00  ------ Instantiation Options
% 11.90/2.00  
% 11.90/2.00  --instantiation_flag                    true
% 11.90/2.00  --inst_sos_flag                         true
% 11.90/2.00  --inst_sos_phase                        true
% 11.90/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.90/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.90/2.00  --inst_lit_sel_side                     num_symb
% 11.90/2.00  --inst_solver_per_active                1400
% 11.90/2.00  --inst_solver_calls_frac                1.
% 11.90/2.00  --inst_passive_queue_type               priority_queues
% 11.90/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.90/2.00  --inst_passive_queues_freq              [25;2]
% 11.90/2.00  --inst_dismatching                      true
% 11.90/2.00  --inst_eager_unprocessed_to_passive     true
% 11.90/2.00  --inst_prop_sim_given                   true
% 11.90/2.00  --inst_prop_sim_new                     false
% 11.90/2.00  --inst_subs_new                         false
% 11.90/2.00  --inst_eq_res_simp                      false
% 11.90/2.00  --inst_subs_given                       false
% 11.90/2.00  --inst_orphan_elimination               true
% 11.90/2.00  --inst_learning_loop_flag               true
% 11.90/2.00  --inst_learning_start                   3000
% 11.90/2.00  --inst_learning_factor                  2
% 11.90/2.00  --inst_start_prop_sim_after_learn       3
% 11.90/2.00  --inst_sel_renew                        solver
% 11.90/2.00  --inst_lit_activity_flag                true
% 11.90/2.00  --inst_restr_to_given                   false
% 11.90/2.00  --inst_activity_threshold               500
% 11.90/2.00  --inst_out_proof                        true
% 11.90/2.00  
% 11.90/2.00  ------ Resolution Options
% 11.90/2.00  
% 11.90/2.00  --resolution_flag                       true
% 11.90/2.00  --res_lit_sel                           adaptive
% 11.90/2.00  --res_lit_sel_side                      none
% 11.90/2.00  --res_ordering                          kbo
% 11.90/2.00  --res_to_prop_solver                    active
% 11.90/2.00  --res_prop_simpl_new                    false
% 11.90/2.00  --res_prop_simpl_given                  true
% 11.90/2.00  --res_passive_queue_type                priority_queues
% 11.90/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.90/2.00  --res_passive_queues_freq               [15;5]
% 11.90/2.00  --res_forward_subs                      full
% 11.90/2.00  --res_backward_subs                     full
% 11.90/2.00  --res_forward_subs_resolution           true
% 11.90/2.00  --res_backward_subs_resolution          true
% 11.90/2.00  --res_orphan_elimination                true
% 11.90/2.00  --res_time_limit                        2.
% 11.90/2.00  --res_out_proof                         true
% 11.90/2.00  
% 11.90/2.00  ------ Superposition Options
% 11.90/2.00  
% 11.90/2.00  --superposition_flag                    true
% 11.90/2.00  --sup_passive_queue_type                priority_queues
% 11.90/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.90/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.90/2.00  --demod_completeness_check              fast
% 11.90/2.00  --demod_use_ground                      true
% 11.90/2.00  --sup_to_prop_solver                    passive
% 11.90/2.00  --sup_prop_simpl_new                    true
% 11.90/2.00  --sup_prop_simpl_given                  true
% 11.90/2.00  --sup_fun_splitting                     true
% 11.90/2.00  --sup_smt_interval                      50000
% 11.90/2.00  
% 11.90/2.00  ------ Superposition Simplification Setup
% 11.90/2.00  
% 11.90/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.90/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.90/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.90/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.90/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.90/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.90/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.90/2.00  --sup_immed_triv                        [TrivRules]
% 11.90/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.90/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.90/2.00  --sup_immed_bw_main                     []
% 11.90/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.90/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.90/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.90/2.00  --sup_input_bw                          []
% 11.90/2.00  
% 11.90/2.00  ------ Combination Options
% 11.90/2.00  
% 11.90/2.00  --comb_res_mult                         3
% 11.90/2.00  --comb_sup_mult                         2
% 11.90/2.00  --comb_inst_mult                        10
% 11.90/2.00  
% 11.90/2.00  ------ Debug Options
% 11.90/2.00  
% 11.90/2.00  --dbg_backtrace                         false
% 11.90/2.00  --dbg_dump_prop_clauses                 false
% 11.90/2.00  --dbg_dump_prop_clauses_file            -
% 11.90/2.00  --dbg_out_stat                          false
% 11.90/2.00  ------ Parsing...
% 11.90/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.90/2.00  
% 11.90/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.90/2.00  
% 11.90/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.90/2.00  
% 11.90/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.90/2.00  ------ Proving...
% 11.90/2.00  ------ Problem Properties 
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  clauses                                 21
% 11.90/2.00  conjectures                             2
% 11.90/2.00  EPR                                     2
% 11.90/2.00  Horn                                    15
% 11.90/2.00  unary                                   6
% 11.90/2.00  binary                                  10
% 11.90/2.00  lits                                    42
% 11.90/2.00  lits eq                                 11
% 11.90/2.00  fd_pure                                 0
% 11.90/2.00  fd_pseudo                               0
% 11.90/2.00  fd_cond                                 0
% 11.90/2.00  fd_pseudo_cond                          3
% 11.90/2.00  AC symbols                              0
% 11.90/2.00  
% 11.90/2.00  ------ Schedule dynamic 5 is on 
% 11.90/2.00  
% 11.90/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  ------ 
% 11.90/2.00  Current options:
% 11.90/2.00  ------ 
% 11.90/2.00  
% 11.90/2.00  ------ Input Options
% 11.90/2.00  
% 11.90/2.00  --out_options                           all
% 11.90/2.00  --tptp_safe_out                         true
% 11.90/2.00  --problem_path                          ""
% 11.90/2.00  --include_path                          ""
% 11.90/2.00  --clausifier                            res/vclausify_rel
% 11.90/2.00  --clausifier_options                    ""
% 11.90/2.00  --stdin                                 false
% 11.90/2.00  --stats_out                             all
% 11.90/2.00  
% 11.90/2.00  ------ General Options
% 11.90/2.00  
% 11.90/2.00  --fof                                   false
% 11.90/2.00  --time_out_real                         305.
% 11.90/2.00  --time_out_virtual                      -1.
% 11.90/2.00  --symbol_type_check                     false
% 11.90/2.00  --clausify_out                          false
% 11.90/2.00  --sig_cnt_out                           false
% 11.90/2.00  --trig_cnt_out                          false
% 11.90/2.00  --trig_cnt_out_tolerance                1.
% 11.90/2.00  --trig_cnt_out_sk_spl                   false
% 11.90/2.00  --abstr_cl_out                          false
% 11.90/2.00  
% 11.90/2.00  ------ Global Options
% 11.90/2.00  
% 11.90/2.00  --schedule                              default
% 11.90/2.00  --add_important_lit                     false
% 11.90/2.00  --prop_solver_per_cl                    1000
% 11.90/2.00  --min_unsat_core                        false
% 11.90/2.00  --soft_assumptions                      false
% 11.90/2.00  --soft_lemma_size                       3
% 11.90/2.00  --prop_impl_unit_size                   0
% 11.90/2.00  --prop_impl_unit                        []
% 11.90/2.00  --share_sel_clauses                     true
% 11.90/2.00  --reset_solvers                         false
% 11.90/2.00  --bc_imp_inh                            [conj_cone]
% 11.90/2.00  --conj_cone_tolerance                   3.
% 11.90/2.00  --extra_neg_conj                        none
% 11.90/2.00  --large_theory_mode                     true
% 11.90/2.00  --prolific_symb_bound                   200
% 11.90/2.00  --lt_threshold                          2000
% 11.90/2.00  --clause_weak_htbl                      true
% 11.90/2.00  --gc_record_bc_elim                     false
% 11.90/2.00  
% 11.90/2.00  ------ Preprocessing Options
% 11.90/2.00  
% 11.90/2.00  --preprocessing_flag                    true
% 11.90/2.00  --time_out_prep_mult                    0.1
% 11.90/2.00  --splitting_mode                        input
% 11.90/2.00  --splitting_grd                         true
% 11.90/2.00  --splitting_cvd                         false
% 11.90/2.00  --splitting_cvd_svl                     false
% 11.90/2.00  --splitting_nvd                         32
% 11.90/2.00  --sub_typing                            true
% 11.90/2.00  --prep_gs_sim                           true
% 11.90/2.00  --prep_unflatten                        true
% 11.90/2.00  --prep_res_sim                          true
% 11.90/2.00  --prep_upred                            true
% 11.90/2.00  --prep_sem_filter                       exhaustive
% 11.90/2.00  --prep_sem_filter_out                   false
% 11.90/2.00  --pred_elim                             true
% 11.90/2.00  --res_sim_input                         true
% 11.90/2.00  --eq_ax_congr_red                       true
% 11.90/2.00  --pure_diseq_elim                       true
% 11.90/2.00  --brand_transform                       false
% 11.90/2.00  --non_eq_to_eq                          false
% 11.90/2.00  --prep_def_merge                        true
% 11.90/2.00  --prep_def_merge_prop_impl              false
% 11.90/2.00  --prep_def_merge_mbd                    true
% 11.90/2.00  --prep_def_merge_tr_red                 false
% 11.90/2.00  --prep_def_merge_tr_cl                  false
% 11.90/2.00  --smt_preprocessing                     true
% 11.90/2.00  --smt_ac_axioms                         fast
% 11.90/2.00  --preprocessed_out                      false
% 11.90/2.00  --preprocessed_stats                    false
% 11.90/2.00  
% 11.90/2.00  ------ Abstraction refinement Options
% 11.90/2.00  
% 11.90/2.00  --abstr_ref                             []
% 11.90/2.00  --abstr_ref_prep                        false
% 11.90/2.00  --abstr_ref_until_sat                   false
% 11.90/2.00  --abstr_ref_sig_restrict                funpre
% 11.90/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.90/2.00  --abstr_ref_under                       []
% 11.90/2.00  
% 11.90/2.00  ------ SAT Options
% 11.90/2.00  
% 11.90/2.00  --sat_mode                              false
% 11.90/2.00  --sat_fm_restart_options                ""
% 11.90/2.00  --sat_gr_def                            false
% 11.90/2.00  --sat_epr_types                         true
% 11.90/2.00  --sat_non_cyclic_types                  false
% 11.90/2.00  --sat_finite_models                     false
% 11.90/2.00  --sat_fm_lemmas                         false
% 11.90/2.00  --sat_fm_prep                           false
% 11.90/2.00  --sat_fm_uc_incr                        true
% 11.90/2.00  --sat_out_model                         small
% 11.90/2.00  --sat_out_clauses                       false
% 11.90/2.00  
% 11.90/2.00  ------ QBF Options
% 11.90/2.00  
% 11.90/2.00  --qbf_mode                              false
% 11.90/2.00  --qbf_elim_univ                         false
% 11.90/2.00  --qbf_dom_inst                          none
% 11.90/2.00  --qbf_dom_pre_inst                      false
% 11.90/2.00  --qbf_sk_in                             false
% 11.90/2.00  --qbf_pred_elim                         true
% 11.90/2.00  --qbf_split                             512
% 11.90/2.00  
% 11.90/2.00  ------ BMC1 Options
% 11.90/2.00  
% 11.90/2.00  --bmc1_incremental                      false
% 11.90/2.00  --bmc1_axioms                           reachable_all
% 11.90/2.00  --bmc1_min_bound                        0
% 11.90/2.00  --bmc1_max_bound                        -1
% 11.90/2.00  --bmc1_max_bound_default                -1
% 11.90/2.00  --bmc1_symbol_reachability              true
% 11.90/2.00  --bmc1_property_lemmas                  false
% 11.90/2.00  --bmc1_k_induction                      false
% 11.90/2.00  --bmc1_non_equiv_states                 false
% 11.90/2.00  --bmc1_deadlock                         false
% 11.90/2.00  --bmc1_ucm                              false
% 11.90/2.00  --bmc1_add_unsat_core                   none
% 11.90/2.00  --bmc1_unsat_core_children              false
% 11.90/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.90/2.00  --bmc1_out_stat                         full
% 11.90/2.00  --bmc1_ground_init                      false
% 11.90/2.00  --bmc1_pre_inst_next_state              false
% 11.90/2.00  --bmc1_pre_inst_state                   false
% 11.90/2.00  --bmc1_pre_inst_reach_state             false
% 11.90/2.00  --bmc1_out_unsat_core                   false
% 11.90/2.00  --bmc1_aig_witness_out                  false
% 11.90/2.00  --bmc1_verbose                          false
% 11.90/2.00  --bmc1_dump_clauses_tptp                false
% 11.90/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.90/2.00  --bmc1_dump_file                        -
% 11.90/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.90/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.90/2.00  --bmc1_ucm_extend_mode                  1
% 11.90/2.00  --bmc1_ucm_init_mode                    2
% 11.90/2.00  --bmc1_ucm_cone_mode                    none
% 11.90/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.90/2.00  --bmc1_ucm_relax_model                  4
% 11.90/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.90/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.90/2.00  --bmc1_ucm_layered_model                none
% 11.90/2.00  --bmc1_ucm_max_lemma_size               10
% 11.90/2.00  
% 11.90/2.00  ------ AIG Options
% 11.90/2.00  
% 11.90/2.00  --aig_mode                              false
% 11.90/2.00  
% 11.90/2.00  ------ Instantiation Options
% 11.90/2.00  
% 11.90/2.00  --instantiation_flag                    true
% 11.90/2.00  --inst_sos_flag                         true
% 11.90/2.00  --inst_sos_phase                        true
% 11.90/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.90/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.90/2.00  --inst_lit_sel_side                     none
% 11.90/2.00  --inst_solver_per_active                1400
% 11.90/2.00  --inst_solver_calls_frac                1.
% 11.90/2.00  --inst_passive_queue_type               priority_queues
% 11.90/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.90/2.00  --inst_passive_queues_freq              [25;2]
% 11.90/2.00  --inst_dismatching                      true
% 11.90/2.00  --inst_eager_unprocessed_to_passive     true
% 11.90/2.00  --inst_prop_sim_given                   true
% 11.90/2.00  --inst_prop_sim_new                     false
% 11.90/2.00  --inst_subs_new                         false
% 11.90/2.00  --inst_eq_res_simp                      false
% 11.90/2.00  --inst_subs_given                       false
% 11.90/2.00  --inst_orphan_elimination               true
% 11.90/2.00  --inst_learning_loop_flag               true
% 11.90/2.00  --inst_learning_start                   3000
% 11.90/2.00  --inst_learning_factor                  2
% 11.90/2.00  --inst_start_prop_sim_after_learn       3
% 11.90/2.00  --inst_sel_renew                        solver
% 11.90/2.00  --inst_lit_activity_flag                true
% 11.90/2.00  --inst_restr_to_given                   false
% 11.90/2.00  --inst_activity_threshold               500
% 11.90/2.00  --inst_out_proof                        true
% 11.90/2.00  
% 11.90/2.00  ------ Resolution Options
% 11.90/2.00  
% 11.90/2.00  --resolution_flag                       false
% 11.90/2.00  --res_lit_sel                           adaptive
% 11.90/2.00  --res_lit_sel_side                      none
% 11.90/2.00  --res_ordering                          kbo
% 11.90/2.00  --res_to_prop_solver                    active
% 11.90/2.00  --res_prop_simpl_new                    false
% 11.90/2.00  --res_prop_simpl_given                  true
% 11.90/2.00  --res_passive_queue_type                priority_queues
% 11.90/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.90/2.00  --res_passive_queues_freq               [15;5]
% 11.90/2.00  --res_forward_subs                      full
% 11.90/2.00  --res_backward_subs                     full
% 11.90/2.00  --res_forward_subs_resolution           true
% 11.90/2.00  --res_backward_subs_resolution          true
% 11.90/2.00  --res_orphan_elimination                true
% 11.90/2.00  --res_time_limit                        2.
% 11.90/2.00  --res_out_proof                         true
% 11.90/2.00  
% 11.90/2.00  ------ Superposition Options
% 11.90/2.00  
% 11.90/2.00  --superposition_flag                    true
% 11.90/2.00  --sup_passive_queue_type                priority_queues
% 11.90/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.90/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.90/2.00  --demod_completeness_check              fast
% 11.90/2.00  --demod_use_ground                      true
% 11.90/2.00  --sup_to_prop_solver                    passive
% 11.90/2.00  --sup_prop_simpl_new                    true
% 11.90/2.00  --sup_prop_simpl_given                  true
% 11.90/2.00  --sup_fun_splitting                     true
% 11.90/2.00  --sup_smt_interval                      50000
% 11.90/2.00  
% 11.90/2.00  ------ Superposition Simplification Setup
% 11.90/2.00  
% 11.90/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.90/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.90/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.90/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.90/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.90/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.90/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.90/2.00  --sup_immed_triv                        [TrivRules]
% 11.90/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.90/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.90/2.00  --sup_immed_bw_main                     []
% 11.90/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.90/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.90/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.90/2.00  --sup_input_bw                          []
% 11.90/2.00  
% 11.90/2.00  ------ Combination Options
% 11.90/2.00  
% 11.90/2.00  --comb_res_mult                         3
% 11.90/2.00  --comb_sup_mult                         2
% 11.90/2.00  --comb_inst_mult                        10
% 11.90/2.00  
% 11.90/2.00  ------ Debug Options
% 11.90/2.00  
% 11.90/2.00  --dbg_backtrace                         false
% 11.90/2.00  --dbg_dump_prop_clauses                 false
% 11.90/2.00  --dbg_dump_prop_clauses_file            -
% 11.90/2.00  --dbg_out_stat                          false
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  ------ Proving...
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  % SZS status Theorem for theBenchmark.p
% 11.90/2.00  
% 11.90/2.00   Resolution empty clause
% 11.90/2.00  
% 11.90/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.90/2.00  
% 11.90/2.00  fof(f3,axiom,(
% 11.90/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f18,plain,(
% 11.90/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.90/2.00    inference(rectify,[],[f3])).
% 11.90/2.00  
% 11.90/2.00  fof(f19,plain,(
% 11.90/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.90/2.00    inference(ennf_transformation,[],[f18])).
% 11.90/2.00  
% 11.90/2.00  fof(f26,plain,(
% 11.90/2.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.90/2.00    introduced(choice_axiom,[])).
% 11.90/2.00  
% 11.90/2.00  fof(f27,plain,(
% 11.90/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.90/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).
% 11.90/2.00  
% 11.90/2.00  fof(f40,plain,(
% 11.90/2.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f27])).
% 11.90/2.00  
% 11.90/2.00  fof(f41,plain,(
% 11.90/2.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f27])).
% 11.90/2.00  
% 11.90/2.00  fof(f2,axiom,(
% 11.90/2.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f21,plain,(
% 11.90/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.90/2.00    inference(nnf_transformation,[],[f2])).
% 11.90/2.00  
% 11.90/2.00  fof(f22,plain,(
% 11.90/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.90/2.00    inference(flattening,[],[f21])).
% 11.90/2.00  
% 11.90/2.00  fof(f23,plain,(
% 11.90/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.90/2.00    inference(rectify,[],[f22])).
% 11.90/2.00  
% 11.90/2.00  fof(f24,plain,(
% 11.90/2.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.90/2.00    introduced(choice_axiom,[])).
% 11.90/2.00  
% 11.90/2.00  fof(f25,plain,(
% 11.90/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.90/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 11.90/2.00  
% 11.90/2.00  fof(f35,plain,(
% 11.90/2.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.90/2.00    inference(cnf_transformation,[],[f25])).
% 11.90/2.00  
% 11.90/2.00  fof(f5,axiom,(
% 11.90/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f45,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.90/2.00    inference(cnf_transformation,[],[f5])).
% 11.90/2.00  
% 11.90/2.00  fof(f69,plain,(
% 11.90/2.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.90/2.00    inference(definition_unfolding,[],[f35,f45])).
% 11.90/2.00  
% 11.90/2.00  fof(f82,plain,(
% 11.90/2.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.90/2.00    inference(equality_resolution,[],[f69])).
% 11.90/2.00  
% 11.90/2.00  fof(f8,axiom,(
% 11.90/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f29,plain,(
% 11.90/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 11.90/2.00    inference(nnf_transformation,[],[f8])).
% 11.90/2.00  
% 11.90/2.00  fof(f48,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f29])).
% 11.90/2.00  
% 11.90/2.00  fof(f76,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.90/2.00    inference(definition_unfolding,[],[f48,f45])).
% 11.90/2.00  
% 11.90/2.00  fof(f1,axiom,(
% 11.90/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f33,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f1])).
% 11.90/2.00  
% 11.90/2.00  fof(f9,axiom,(
% 11.90/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f50,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.90/2.00    inference(cnf_transformation,[],[f9])).
% 11.90/2.00  
% 11.90/2.00  fof(f60,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 11.90/2.00    inference(definition_unfolding,[],[f50,f45])).
% 11.90/2.00  
% 11.90/2.00  fof(f64,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.90/2.00    inference(definition_unfolding,[],[f33,f60,f60])).
% 11.90/2.00  
% 11.90/2.00  fof(f16,conjecture,(
% 11.90/2.00    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f17,negated_conjecture,(
% 11.90/2.00    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 11.90/2.00    inference(negated_conjecture,[],[f16])).
% 11.90/2.00  
% 11.90/2.00  fof(f20,plain,(
% 11.90/2.00    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 11.90/2.00    inference(ennf_transformation,[],[f17])).
% 11.90/2.00  
% 11.90/2.00  fof(f31,plain,(
% 11.90/2.00    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 & r2_hidden(sK2,sK3))),
% 11.90/2.00    introduced(choice_axiom,[])).
% 11.90/2.00  
% 11.90/2.00  fof(f32,plain,(
% 11.90/2.00    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 & r2_hidden(sK2,sK3)),
% 11.90/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f31])).
% 11.90/2.00  
% 11.90/2.00  fof(f59,plain,(
% 11.90/2.00    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3),
% 11.90/2.00    inference(cnf_transformation,[],[f32])).
% 11.90/2.00  
% 11.90/2.00  fof(f10,axiom,(
% 11.90/2.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f51,plain,(
% 11.90/2.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f10])).
% 11.90/2.00  
% 11.90/2.00  fof(f11,axiom,(
% 11.90/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f52,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f11])).
% 11.90/2.00  
% 11.90/2.00  fof(f12,axiom,(
% 11.90/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f53,plain,(
% 11.90/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f12])).
% 11.90/2.00  
% 11.90/2.00  fof(f13,axiom,(
% 11.90/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f54,plain,(
% 11.90/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f13])).
% 11.90/2.00  
% 11.90/2.00  fof(f61,plain,(
% 11.90/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 11.90/2.00    inference(definition_unfolding,[],[f53,f54])).
% 11.90/2.00  
% 11.90/2.00  fof(f62,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 11.90/2.00    inference(definition_unfolding,[],[f52,f61])).
% 11.90/2.00  
% 11.90/2.00  fof(f63,plain,(
% 11.90/2.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 11.90/2.00    inference(definition_unfolding,[],[f51,f62])).
% 11.90/2.00  
% 11.90/2.00  fof(f80,plain,(
% 11.90/2.00    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))))) != sK3),
% 11.90/2.00    inference(definition_unfolding,[],[f59,f60,f45,f63,f63])).
% 11.90/2.00  
% 11.90/2.00  fof(f7,axiom,(
% 11.90/2.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f47,plain,(
% 11.90/2.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f7])).
% 11.90/2.00  
% 11.90/2.00  fof(f74,plain,(
% 11.90/2.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 11.90/2.00    inference(definition_unfolding,[],[f47,f45])).
% 11.90/2.00  
% 11.90/2.00  fof(f4,axiom,(
% 11.90/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f28,plain,(
% 11.90/2.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.90/2.00    inference(nnf_transformation,[],[f4])).
% 11.90/2.00  
% 11.90/2.00  fof(f44,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f28])).
% 11.90/2.00  
% 11.90/2.00  fof(f71,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 11.90/2.00    inference(definition_unfolding,[],[f44,f45])).
% 11.90/2.00  
% 11.90/2.00  fof(f6,axiom,(
% 11.90/2.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f46,plain,(
% 11.90/2.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.90/2.00    inference(cnf_transformation,[],[f6])).
% 11.90/2.00  
% 11.90/2.00  fof(f73,plain,(
% 11.90/2.00    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 11.90/2.00    inference(definition_unfolding,[],[f46,f60])).
% 11.90/2.00  
% 11.90/2.00  fof(f49,plain,(
% 11.90/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 11.90/2.00    inference(cnf_transformation,[],[f29])).
% 11.90/2.00  
% 11.90/2.00  fof(f75,plain,(
% 11.90/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 11.90/2.00    inference(definition_unfolding,[],[f49,f45])).
% 11.90/2.00  
% 11.90/2.00  fof(f42,plain,(
% 11.90/2.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f27])).
% 11.90/2.00  
% 11.90/2.00  fof(f34,plain,(
% 11.90/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.90/2.00    inference(cnf_transformation,[],[f25])).
% 11.90/2.00  
% 11.90/2.00  fof(f70,plain,(
% 11.90/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.90/2.00    inference(definition_unfolding,[],[f34,f45])).
% 11.90/2.00  
% 11.90/2.00  fof(f83,plain,(
% 11.90/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.90/2.00    inference(equality_resolution,[],[f70])).
% 11.90/2.00  
% 11.90/2.00  fof(f58,plain,(
% 11.90/2.00    r2_hidden(sK2,sK3)),
% 11.90/2.00    inference(cnf_transformation,[],[f32])).
% 11.90/2.00  
% 11.90/2.00  fof(f36,plain,(
% 11.90/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 11.90/2.00    inference(cnf_transformation,[],[f25])).
% 11.90/2.00  
% 11.90/2.00  fof(f68,plain,(
% 11.90/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.90/2.00    inference(definition_unfolding,[],[f36,f45])).
% 11.90/2.00  
% 11.90/2.00  fof(f81,plain,(
% 11.90/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 11.90/2.00    inference(equality_resolution,[],[f68])).
% 11.90/2.00  
% 11.90/2.00  fof(f14,axiom,(
% 11.90/2.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f30,plain,(
% 11.90/2.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.90/2.00    inference(nnf_transformation,[],[f14])).
% 11.90/2.00  
% 11.90/2.00  fof(f56,plain,(
% 11.90/2.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.90/2.00    inference(cnf_transformation,[],[f30])).
% 11.90/2.00  
% 11.90/2.00  fof(f77,plain,(
% 11.90/2.00    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.90/2.00    inference(definition_unfolding,[],[f56,f63])).
% 11.90/2.00  
% 11.90/2.00  fof(f15,axiom,(
% 11.90/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.90/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/2.00  
% 11.90/2.00  fof(f57,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.90/2.00    inference(cnf_transformation,[],[f15])).
% 11.90/2.00  
% 11.90/2.00  fof(f79,plain,(
% 11.90/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 11.90/2.00    inference(definition_unfolding,[],[f57,f60,f62])).
% 11.90/2.00  
% 11.90/2.00  cnf(c_9,plain,
% 11.90/2.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 11.90/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_805,plain,
% 11.90/2.00      ( r1_xboole_0(X0,X1) = iProver_top
% 11.90/2.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_8,plain,
% 11.90/2.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 11.90/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_806,plain,
% 11.90/2.00      ( r1_xboole_0(X0,X1) = iProver_top
% 11.90/2.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_5,plain,
% 11.90/2.00      ( ~ r2_hidden(X0,X1)
% 11.90/2.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 11.90/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_809,plain,
% 11.90/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.90/2.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_3220,plain,
% 11.90/2.00      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 11.90/2.00      | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) != iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_806,c_809]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_4515,plain,
% 11.90/2.00      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_805,c_3220]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_15,plain,
% 11.90/2.00      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 11.90/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_800,plain,
% 11.90/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 11.90/2.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_4755,plain,
% 11.90/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_4515,c_800]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_4767,plain,
% 11.90/2.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_4755,c_4755]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_0,plain,
% 11.90/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 11.90/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_19,negated_conjecture,
% 11.90/2.00      ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))))) != sK3 ),
% 11.90/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1415,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_0,c_19]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_39306,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_4767,c_1415]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_13,plain,
% 11.90/2.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.90/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_802,plain,
% 11.90/2.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_10,plain,
% 11.90/2.00      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.90/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_804,plain,
% 11.90/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 11.90/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1264,plain,
% 11.90/2.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = k1_xboole_0 ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_802,c_804]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_12,plain,
% 11.90/2.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 11.90/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1416,plain,
% 11.90/2.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1748,plain,
% 11.90/2.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_1264,c_1416]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1747,plain,
% 11.90/2.00      ( r1_tarski(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_1264,c_802]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1815,plain,
% 11.90/2.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_1264,c_1747]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1819,plain,
% 11.90/2.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_1815,c_804]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1863,plain,
% 11.90/2.00      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_1819,c_12]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_2766,plain,
% 11.90/2.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.90/2.00      inference(light_normalisation,[status(thm)],[c_1748,c_1748,c_1863]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_14,plain,
% 11.90/2.00      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 11.90/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_801,plain,
% 11.90/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
% 11.90/2.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_2779,plain,
% 11.90/2.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_2766,c_801]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_7,plain,
% 11.90/2.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 11.90/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_807,plain,
% 11.90/2.00      ( r1_xboole_0(X0,X1) != iProver_top
% 11.90/2.00      | r2_hidden(X2,X1) != iProver_top
% 11.90/2.00      | r2_hidden(X2,X0) != iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_3100,plain,
% 11.90/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.90/2.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_2779,c_807]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_6,plain,
% 11.90/2.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.90/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_52,plain,
% 11.90/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.90/2.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_808,plain,
% 11.90/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.90/2.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_3108,plain,
% 11.90/2.00      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 11.90/2.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_1264,c_808]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_3358,plain,
% 11.90/2.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.90/2.00      inference(global_propositional_subsumption,
% 11.90/2.00                [status(thm)],
% 11.90/2.00                [c_3100,c_52,c_3108]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_3366,plain,
% 11.90/2.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_806,c_3358]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_3499,plain,
% 11.90/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_3366,c_800]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_3501,plain,
% 11.90/2.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_3499,c_1416]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_3620,plain,
% 11.90/2.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_3501,c_2766]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_20,negated_conjecture,
% 11.90/2.00      ( r2_hidden(sK2,sK3) ),
% 11.90/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_797,plain,
% 11.90/2.00      ( r2_hidden(sK2,sK3) = iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_4,plain,
% 11.90/2.00      ( ~ r2_hidden(X0,X1)
% 11.90/2.00      | r2_hidden(X0,X2)
% 11.90/2.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.90/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_810,plain,
% 11.90/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.90/2.00      | r2_hidden(X0,X2) = iProver_top
% 11.90/2.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_16,plain,
% 11.90/2.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 11.90/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_799,plain,
% 11.90/2.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
% 11.90/2.00      | r2_hidden(X0,X1) != iProver_top ),
% 11.90/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_2018,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k1_xboole_0
% 11.90/2.00      | r2_hidden(X0,X1) != iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_799,c_804]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_5233,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k1_xboole_0
% 11.90/2.00      | r2_hidden(X0,X1) != iProver_top
% 11.90/2.00      | r2_hidden(X0,X2) = iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_810,c_2018]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_9023,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,X0)))) = k1_xboole_0
% 11.90/2.00      | r2_hidden(sK2,X0) = iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_797,c_5233]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_9332,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) = k1_xboole_0
% 11.90/2.00      | r2_hidden(sK2,X0) = iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_9023,c_808]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_9611,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)))))) = k1_xboole_0
% 11.90/2.00      | r2_hidden(sK2,X1) != iProver_top ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_9332,c_809]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_12211,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))))) = k1_xboole_0 ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_797,c_9611]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_12259,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k1_xboole_0) ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_12211,c_0]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_18,plain,
% 11.90/2.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 11.90/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1742,plain,
% 11.90/2.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k1_xboole_0) ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_1264,c_18]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_2373,plain,
% 11.90/2.00      ( k3_tarski(k3_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_1264,c_1742]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_1531,plain,
% 11.90/2.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_18,c_12]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_2376,plain,
% 11.90/2.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_2373,c_1531]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_12279,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1)))) ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_12259,c_2376]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_17598,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK3)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK3)),X0)))) ),
% 11.90/2.00      inference(superposition,[status(thm)],[c_3620,c_12279]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_17600,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK3),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK3),X0)))) ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_17598,c_3499,c_3501,c_3620]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_17601,plain,
% 11.90/2.00      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_17600,c_3499,c_3501,c_3620]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_39307,plain,
% 11.90/2.00      ( sK3 != sK3 ),
% 11.90/2.00      inference(light_normalisation,[status(thm)],[c_39306,c_17601]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_39308,plain,
% 11.90/2.00      ( $false ),
% 11.90/2.00      inference(equality_resolution_simp,[status(thm)],[c_39307]) ).
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.90/2.00  
% 11.90/2.00  ------                               Statistics
% 11.90/2.00  
% 11.90/2.00  ------ General
% 11.90/2.00  
% 11.90/2.00  abstr_ref_over_cycles:                  0
% 11.90/2.00  abstr_ref_under_cycles:                 0
% 11.90/2.00  gc_basic_clause_elim:                   0
% 11.90/2.00  forced_gc_time:                         0
% 11.90/2.00  parsing_time:                           0.008
% 11.90/2.00  unif_index_cands_time:                  0.
% 11.90/2.00  unif_index_add_time:                    0.
% 11.90/2.00  orderings_time:                         0.
% 11.90/2.00  out_proof_time:                         0.01
% 11.90/2.00  total_time:                             1.385
% 11.90/2.00  num_of_symbols:                         43
% 11.90/2.00  num_of_terms:                           54381
% 11.90/2.00  
% 11.90/2.00  ------ Preprocessing
% 11.90/2.00  
% 11.90/2.00  num_of_splits:                          0
% 11.90/2.00  num_of_split_atoms:                     0
% 11.90/2.00  num_of_reused_defs:                     0
% 11.90/2.00  num_eq_ax_congr_red:                    16
% 11.90/2.00  num_of_sem_filtered_clauses:            1
% 11.90/2.00  num_of_subtypes:                        0
% 11.90/2.00  monotx_restored_types:                  0
% 11.90/2.00  sat_num_of_epr_types:                   0
% 11.90/2.00  sat_num_of_non_cyclic_types:            0
% 11.90/2.00  sat_guarded_non_collapsed_types:        0
% 11.90/2.00  num_pure_diseq_elim:                    0
% 11.90/2.00  simp_replaced_by:                       0
% 11.90/2.00  res_preprocessed:                       80
% 11.90/2.00  prep_upred:                             0
% 11.90/2.00  prep_unflattend:                        7
% 11.90/2.00  smt_new_axioms:                         0
% 11.90/2.00  pred_elim_cands:                        3
% 11.90/2.00  pred_elim:                              0
% 11.90/2.00  pred_elim_cl:                           0
% 11.90/2.00  pred_elim_cycles:                       2
% 11.90/2.00  merged_defs:                            18
% 11.90/2.00  merged_defs_ncl:                        0
% 11.90/2.00  bin_hyper_res:                          18
% 11.90/2.00  prep_cycles:                            3
% 11.90/2.00  pred_elim_time:                         0.001
% 11.90/2.00  splitting_time:                         0.
% 11.90/2.00  sem_filter_time:                        0.
% 11.90/2.00  monotx_time:                            0.018
% 11.90/2.00  subtype_inf_time:                       0.
% 11.90/2.00  
% 11.90/2.00  ------ Problem properties
% 11.90/2.00  
% 11.90/2.00  clauses:                                21
% 11.90/2.00  conjectures:                            2
% 11.90/2.00  epr:                                    2
% 11.90/2.00  horn:                                   15
% 11.90/2.00  ground:                                 2
% 11.90/2.00  unary:                                  6
% 11.90/2.00  binary:                                 10
% 11.90/2.00  lits:                                   42
% 11.90/2.00  lits_eq:                                11
% 11.90/2.00  fd_pure:                                0
% 11.90/2.00  fd_pseudo:                              0
% 11.90/2.00  fd_cond:                                0
% 11.90/2.00  fd_pseudo_cond:                         3
% 11.90/2.00  ac_symbols:                             0
% 11.90/2.00  
% 11.90/2.00  ------ Propositional Solver
% 11.90/2.00  
% 11.90/2.00  prop_solver_calls:                      27
% 11.90/2.00  prop_fast_solver_calls:                 777
% 11.90/2.00  smt_solver_calls:                       0
% 11.90/2.00  smt_fast_solver_calls:                  0
% 11.90/2.00  prop_num_of_clauses:                    13229
% 11.90/2.00  prop_preprocess_simplified:             22550
% 11.90/2.00  prop_fo_subsumed:                       6
% 11.90/2.00  prop_solver_time:                       0.
% 11.90/2.00  smt_solver_time:                        0.
% 11.90/2.00  smt_fast_solver_time:                   0.
% 11.90/2.00  prop_fast_solver_time:                  0.
% 11.90/2.00  prop_unsat_core_time:                   0.
% 11.90/2.00  
% 11.90/2.00  ------ QBF
% 11.90/2.00  
% 11.90/2.00  qbf_q_res:                              0
% 11.90/2.00  qbf_num_tautologies:                    0
% 11.90/2.00  qbf_prep_cycles:                        0
% 11.90/2.00  
% 11.90/2.00  ------ BMC1
% 11.90/2.00  
% 11.90/2.00  bmc1_current_bound:                     -1
% 11.90/2.00  bmc1_last_solved_bound:                 -1
% 11.90/2.00  bmc1_unsat_core_size:                   -1
% 11.90/2.00  bmc1_unsat_core_parents_size:           -1
% 11.90/2.00  bmc1_merge_next_fun:                    0
% 11.90/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.90/2.00  
% 11.90/2.00  ------ Instantiation
% 11.90/2.00  
% 11.90/2.00  inst_num_of_clauses:                    2618
% 11.90/2.00  inst_num_in_passive:                    1556
% 11.90/2.00  inst_num_in_active:                     833
% 11.90/2.00  inst_num_in_unprocessed:                229
% 11.90/2.00  inst_num_of_loops:                      1050
% 11.90/2.00  inst_num_of_learning_restarts:          0
% 11.90/2.00  inst_num_moves_active_passive:          217
% 11.90/2.00  inst_lit_activity:                      0
% 11.90/2.00  inst_lit_activity_moves:                0
% 11.90/2.00  inst_num_tautologies:                   0
% 11.90/2.00  inst_num_prop_implied:                  0
% 11.90/2.00  inst_num_existing_simplified:           0
% 11.90/2.00  inst_num_eq_res_simplified:             0
% 11.90/2.00  inst_num_child_elim:                    0
% 11.90/2.00  inst_num_of_dismatching_blockings:      4702
% 11.90/2.00  inst_num_of_non_proper_insts:           4777
% 11.90/2.00  inst_num_of_duplicates:                 0
% 11.90/2.00  inst_inst_num_from_inst_to_res:         0
% 11.90/2.00  inst_dismatching_checking_time:         0.
% 11.90/2.00  
% 11.90/2.00  ------ Resolution
% 11.90/2.00  
% 11.90/2.00  res_num_of_clauses:                     0
% 11.90/2.00  res_num_in_passive:                     0
% 11.90/2.00  res_num_in_active:                      0
% 11.90/2.00  res_num_of_loops:                       83
% 11.90/2.00  res_forward_subset_subsumed:            198
% 11.90/2.00  res_backward_subset_subsumed:           0
% 11.90/2.00  res_forward_subsumed:                   0
% 11.90/2.00  res_backward_subsumed:                  0
% 11.90/2.00  res_forward_subsumption_resolution:     0
% 11.90/2.00  res_backward_subsumption_resolution:    0
% 11.90/2.00  res_clause_to_clause_subsumption:       17818
% 11.90/2.00  res_orphan_elimination:                 0
% 11.90/2.00  res_tautology_del:                      387
% 11.90/2.00  res_num_eq_res_simplified:              0
% 11.90/2.00  res_num_sel_changes:                    0
% 11.90/2.00  res_moves_from_active_to_pass:          0
% 11.90/2.00  
% 11.90/2.00  ------ Superposition
% 11.90/2.00  
% 11.90/2.00  sup_time_total:                         0.
% 11.90/2.00  sup_time_generating:                    0.
% 11.90/2.00  sup_time_sim_full:                      0.
% 11.90/2.00  sup_time_sim_immed:                     0.
% 11.90/2.00  
% 11.90/2.00  sup_num_of_clauses:                     1408
% 11.90/2.00  sup_num_in_active:                      198
% 11.90/2.00  sup_num_in_passive:                     1210
% 11.90/2.00  sup_num_of_loops:                       209
% 11.90/2.00  sup_fw_superposition:                   3937
% 11.90/2.00  sup_bw_superposition:                   2519
% 11.90/2.00  sup_immediate_simplified:               3378
% 11.90/2.00  sup_given_eliminated:                   0
% 11.90/2.00  comparisons_done:                       0
% 11.90/2.00  comparisons_avoided:                    0
% 11.90/2.00  
% 11.90/2.00  ------ Simplifications
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  sim_fw_subset_subsumed:                 334
% 11.90/2.00  sim_bw_subset_subsumed:                 11
% 11.90/2.00  sim_fw_subsumed:                        931
% 11.90/2.00  sim_bw_subsumed:                        27
% 11.90/2.00  sim_fw_subsumption_res:                 0
% 11.90/2.00  sim_bw_subsumption_res:                 0
% 11.90/2.00  sim_tautology_del:                      23
% 11.90/2.00  sim_eq_tautology_del:                   1054
% 11.90/2.00  sim_eq_res_simp:                        10
% 11.90/2.00  sim_fw_demodulated:                     2699
% 11.90/2.00  sim_bw_demodulated:                     8
% 11.90/2.00  sim_light_normalised:                   536
% 11.90/2.00  sim_joinable_taut:                      0
% 11.90/2.00  sim_joinable_simp:                      0
% 11.90/2.00  sim_ac_normalised:                      0
% 11.90/2.00  sim_smt_subsumption:                    0
% 11.90/2.00  
%------------------------------------------------------------------------------
