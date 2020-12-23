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
% DateTime   : Thu Dec  3 11:29:15 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 429 expanded)
%              Number of clauses        :   30 (  45 expanded)
%              Number of leaves         :   20 ( 134 expanded)
%              Depth                    :   21
%              Number of atoms          :  255 ( 688 expanded)
%              Number of equality atoms :  198 ( 593 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f74])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f76])).

fof(f78,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f78])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f63,f73,f70,f79])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f37])).

fof(f71,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f71,f73,f79,f79,f79])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f77])).

fof(f99,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f100,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f99])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f108,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f59,f79])).

fof(f106,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f94])).

fof(f107,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f106])).

fof(f72,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2087,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_1,c_23])).

cnf(c_2198,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
    inference(superposition,[status(thm)],[c_2087,c_9])).

cnf(c_2439,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0),X1) ),
    inference(superposition,[status(thm)],[c_2198,c_9])).

cnf(c_2519,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0),X1) ),
    inference(superposition,[status(thm)],[c_9,c_2439])).

cnf(c_2530,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_2519,c_2198])).

cnf(c_2599,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X1)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_0,c_2530])).

cnf(c_2768,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_1,c_2599])).

cnf(c_3531,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
    inference(superposition,[status(thm)],[c_2768,c_2198])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3676,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_3531,c_8])).

cnf(c_3685,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_3676,c_8])).

cnf(c_14,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1786,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3690,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3685,c_1786])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1834,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1840,plain,
    ( sK3 = X0
    | r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1834])).

cnf(c_1842,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_1422,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1820,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_1821,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_20,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_28,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3690,c_1842,c_1821,c_28,c_25,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.70/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.00  
% 3.70/1.00  ------  iProver source info
% 3.70/1.00  
% 3.70/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.00  git: non_committed_changes: false
% 3.70/1.00  git: last_make_outside_of_git: false
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    ""
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         true
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     num_symb
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       true
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     true
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_input_bw                          []
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  ------ Parsing...
% 3.70/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.00  ------ Proving...
% 3.70/1.00  ------ Problem Properties 
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  clauses                                 23
% 3.70/1.00  conjectures                             2
% 3.70/1.00  EPR                                     3
% 3.70/1.00  Horn                                    20
% 3.70/1.00  unary                                   12
% 3.70/1.00  binary                                  3
% 3.70/1.00  lits                                    45
% 3.70/1.00  lits eq                                 28
% 3.70/1.00  fd_pure                                 0
% 3.70/1.00  fd_pseudo                               0
% 3.70/1.00  fd_cond                                 0
% 3.70/1.00  fd_pseudo_cond                          7
% 3.70/1.00  AC symbols                              0
% 3.70/1.00  
% 3.70/1.00  ------ Schedule dynamic 5 is on 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  Current options:
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    ""
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         true
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     none
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       false
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     true
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_input_bw                          []
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ Proving...
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS status Theorem for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  fof(f1,axiom,(
% 3.70/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f39,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f1])).
% 3.70/1.00  
% 3.70/1.00  fof(f12,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f63,plain,(
% 3.70/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f12])).
% 3.70/1.00  
% 3.70/1.00  fof(f8,axiom,(
% 3.70/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f49,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f8])).
% 3.70/1.00  
% 3.70/1.00  fof(f5,axiom,(
% 3.70/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f46,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f5])).
% 3.70/1.00  
% 3.70/1.00  fof(f73,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f49,f46])).
% 3.70/1.00  
% 3.70/1.00  fof(f13,axiom,(
% 3.70/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f64,plain,(
% 3.70/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f13])).
% 3.70/1.00  
% 3.70/1.00  fof(f14,axiom,(
% 3.70/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f65,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f14])).
% 3.70/1.00  
% 3.70/1.00  fof(f15,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f66,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f15])).
% 3.70/1.00  
% 3.70/1.00  fof(f16,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f67,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f16])).
% 3.70/1.00  
% 3.70/1.00  fof(f17,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f68,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f17])).
% 3.70/1.00  
% 3.70/1.00  fof(f18,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f69,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f18])).
% 3.70/1.00  
% 3.70/1.00  fof(f19,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f70,plain,(
% 3.70/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f19])).
% 3.70/1.00  
% 3.70/1.00  fof(f74,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f69,f70])).
% 3.70/1.00  
% 3.70/1.00  fof(f75,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f68,f74])).
% 3.70/1.00  
% 3.70/1.00  fof(f76,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f67,f75])).
% 3.70/1.00  
% 3.70/1.00  fof(f77,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f66,f76])).
% 3.70/1.00  
% 3.70/1.00  fof(f78,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f65,f77])).
% 3.70/1.00  
% 3.70/1.00  fof(f79,plain,(
% 3.70/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f64,f78])).
% 3.70/1.00  
% 3.70/1.00  fof(f81,plain,(
% 3.70/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f63,f73,f70,f79])).
% 3.70/1.00  
% 3.70/1.00  fof(f7,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f48,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f7])).
% 3.70/1.00  
% 3.70/1.00  fof(f20,conjecture,(
% 3.70/1.00    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f21,negated_conjecture,(
% 3.70/1.00    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.70/1.00    inference(negated_conjecture,[],[f20])).
% 3.70/1.00  
% 3.70/1.00  fof(f24,plain,(
% 3.70/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.70/1.00    inference(ennf_transformation,[],[f21])).
% 3.70/1.00  
% 3.70/1.00  fof(f37,plain,(
% 3.70/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f38,plain,(
% 3.70/1.00    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f37])).
% 3.70/1.00  
% 3.70/1.00  fof(f71,plain,(
% 3.70/1.00    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.70/1.00    inference(cnf_transformation,[],[f38])).
% 3.70/1.00  
% 3.70/1.00  fof(f96,plain,(
% 3.70/1.00    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 3.70/1.00    inference(definition_unfolding,[],[f71,f73,f79,f79,f79])).
% 3.70/1.00  
% 3.70/1.00  fof(f6,axiom,(
% 3.70/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f47,plain,(
% 3.70/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.70/1.00    inference(cnf_transformation,[],[f6])).
% 3.70/1.00  
% 3.70/1.00  fof(f9,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f23,plain,(
% 3.70/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.70/1.00    inference(ennf_transformation,[],[f9])).
% 3.70/1.00  
% 3.70/1.00  fof(f28,plain,(
% 3.70/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.70/1.00    inference(nnf_transformation,[],[f23])).
% 3.70/1.00  
% 3.70/1.00  fof(f29,plain,(
% 3.70/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.70/1.00    inference(flattening,[],[f28])).
% 3.70/1.00  
% 3.70/1.00  fof(f30,plain,(
% 3.70/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.70/1.00    inference(rectify,[],[f29])).
% 3.70/1.00  
% 3.70/1.00  fof(f31,plain,(
% 3.70/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f32,plain,(
% 3.70/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.70/1.00  
% 3.70/1.00  fof(f53,plain,(
% 3.70/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.70/1.00    inference(cnf_transformation,[],[f32])).
% 3.70/1.00  
% 3.70/1.00  fof(f88,plain,(
% 3.70/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.70/1.00    inference(definition_unfolding,[],[f53,f77])).
% 3.70/1.00  
% 3.70/1.00  fof(f99,plain,(
% 3.70/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 3.70/1.00    inference(equality_resolution,[],[f88])).
% 3.70/1.00  
% 3.70/1.00  fof(f100,plain,(
% 3.70/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 3.70/1.00    inference(equality_resolution,[],[f99])).
% 3.70/1.00  
% 3.70/1.00  fof(f10,axiom,(
% 3.70/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f33,plain,(
% 3.70/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.70/1.00    inference(nnf_transformation,[],[f10])).
% 3.70/1.00  
% 3.70/1.00  fof(f34,plain,(
% 3.70/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.70/1.00    inference(rectify,[],[f33])).
% 3.70/1.00  
% 3.70/1.00  fof(f35,plain,(
% 3.70/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f36,plain,(
% 3.70/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 3.70/1.00  
% 3.70/1.00  fof(f58,plain,(
% 3.70/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.70/1.00    inference(cnf_transformation,[],[f36])).
% 3.70/1.00  
% 3.70/1.00  fof(f95,plain,(
% 3.70/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.70/1.00    inference(definition_unfolding,[],[f58,f79])).
% 3.70/1.00  
% 3.70/1.00  fof(f108,plain,(
% 3.70/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 3.70/1.00    inference(equality_resolution,[],[f95])).
% 3.70/1.00  
% 3.70/1.00  fof(f59,plain,(
% 3.70/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.70/1.00    inference(cnf_transformation,[],[f36])).
% 3.70/1.00  
% 3.70/1.00  fof(f94,plain,(
% 3.70/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.70/1.00    inference(definition_unfolding,[],[f59,f79])).
% 3.70/1.00  
% 3.70/1.00  fof(f106,plain,(
% 3.70/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 3.70/1.00    inference(equality_resolution,[],[f94])).
% 3.70/1.00  
% 3.70/1.00  fof(f107,plain,(
% 3.70/1.00    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 3.70/1.00    inference(equality_resolution,[],[f106])).
% 3.70/1.00  
% 3.70/1.00  fof(f72,plain,(
% 3.70/1.00    sK2 != sK3),
% 3.70/1.00    inference(cnf_transformation,[],[f38])).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1,plain,
% 3.70/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_0,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.70/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9,plain,
% 3.70/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_23,negated_conjecture,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.70/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2087,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_1,c_23]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2198,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2087,c_9]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2439,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0),X1) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2198,c_9]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2519,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0),X1) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_9,c_2439]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2530,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0),X1) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_2519,c_2198]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2599,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X1)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),X1) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_0,c_2530]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2768,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),X1) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1,c_2599]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3531,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2768,c_2198]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8,plain,
% 3.70/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3676,plain,
% 3.70/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_3531,c_8]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3685,plain,
% 3.70/1.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_3676,c_8]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14,plain,
% 3.70/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1786,plain,
% 3.70/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3690,plain,
% 3.70/1.00      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_3685,c_1786]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_21,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.70/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1834,plain,
% 3.70/1.00      ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.70/1.00      | sK3 = X0 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1840,plain,
% 3.70/1.00      ( sK3 = X0
% 3.70/1.00      | r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1834]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1842,plain,
% 3.70/1.00      ( sK3 = sK2
% 3.70/1.00      | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1840]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1422,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1820,plain,
% 3.70/1.00      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1422]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1821,plain,
% 3.70/1.00      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1820]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_20,plain,
% 3.70/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_28,plain,
% 3.70/1.00      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_25,plain,
% 3.70/1.00      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.70/1.00      | sK2 = sK2 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_22,negated_conjecture,
% 3.70/1.00      ( sK2 != sK3 ),
% 3.70/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(contradiction,plain,
% 3.70/1.00      ( $false ),
% 3.70/1.00      inference(minisat,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_3690,c_1842,c_1821,c_28,c_25,c_22]) ).
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  ------                               Statistics
% 3.70/1.00  
% 3.70/1.00  ------ General
% 3.70/1.00  
% 3.70/1.00  abstr_ref_over_cycles:                  0
% 3.70/1.00  abstr_ref_under_cycles:                 0
% 3.70/1.00  gc_basic_clause_elim:                   0
% 3.70/1.00  forced_gc_time:                         0
% 3.70/1.00  parsing_time:                           0.011
% 3.70/1.00  unif_index_cands_time:                  0.
% 3.70/1.00  unif_index_add_time:                    0.
% 3.70/1.00  orderings_time:                         0.
% 3.70/1.00  out_proof_time:                         0.009
% 3.70/1.00  total_time:                             0.136
% 3.70/1.00  num_of_symbols:                         41
% 3.70/1.00  num_of_terms:                           3447
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing
% 3.70/1.00  
% 3.70/1.00  num_of_splits:                          0
% 3.70/1.00  num_of_split_atoms:                     0
% 3.70/1.00  num_of_reused_defs:                     0
% 3.70/1.00  num_eq_ax_congr_red:                    24
% 3.70/1.00  num_of_sem_filtered_clauses:            1
% 3.70/1.00  num_of_subtypes:                        0
% 3.70/1.00  monotx_restored_types:                  0
% 3.70/1.00  sat_num_of_epr_types:                   0
% 3.70/1.00  sat_num_of_non_cyclic_types:            0
% 3.70/1.00  sat_guarded_non_collapsed_types:        0
% 3.70/1.00  num_pure_diseq_elim:                    0
% 3.70/1.00  simp_replaced_by:                       0
% 3.70/1.00  res_preprocessed:                       105
% 3.70/1.00  prep_upred:                             0
% 3.70/1.00  prep_unflattend:                        72
% 3.70/1.00  smt_new_axioms:                         0
% 3.70/1.00  pred_elim_cands:                        2
% 3.70/1.00  pred_elim:                              0
% 3.70/1.00  pred_elim_cl:                           0
% 3.70/1.00  pred_elim_cycles:                       2
% 3.70/1.00  merged_defs:                            8
% 3.70/1.00  merged_defs_ncl:                        0
% 3.70/1.00  bin_hyper_res:                          8
% 3.70/1.00  prep_cycles:                            4
% 3.70/1.00  pred_elim_time:                         0.011
% 3.70/1.00  splitting_time:                         0.
% 3.70/1.00  sem_filter_time:                        0.
% 3.70/1.00  monotx_time:                            0.
% 3.70/1.00  subtype_inf_time:                       0.
% 3.70/1.00  
% 3.70/1.00  ------ Problem properties
% 3.70/1.00  
% 3.70/1.00  clauses:                                23
% 3.70/1.00  conjectures:                            2
% 3.70/1.00  epr:                                    3
% 3.70/1.00  horn:                                   20
% 3.70/1.00  ground:                                 2
% 3.70/1.00  unary:                                  12
% 3.70/1.00  binary:                                 3
% 3.70/1.00  lits:                                   45
% 3.70/1.00  lits_eq:                                28
% 3.70/1.00  fd_pure:                                0
% 3.70/1.00  fd_pseudo:                              0
% 3.70/1.00  fd_cond:                                0
% 3.70/1.00  fd_pseudo_cond:                         7
% 3.70/1.00  ac_symbols:                             0
% 3.70/1.00  
% 3.70/1.00  ------ Propositional Solver
% 3.70/1.00  
% 3.70/1.00  prop_solver_calls:                      29
% 3.70/1.00  prop_fast_solver_calls:                 722
% 3.70/1.00  smt_solver_calls:                       0
% 3.70/1.00  smt_fast_solver_calls:                  0
% 3.70/1.00  prop_num_of_clauses:                    866
% 3.70/1.00  prop_preprocess_simplified:             3667
% 3.70/1.00  prop_fo_subsumed:                       0
% 3.70/1.00  prop_solver_time:                       0.
% 3.70/1.00  smt_solver_time:                        0.
% 3.70/1.00  smt_fast_solver_time:                   0.
% 3.70/1.00  prop_fast_solver_time:                  0.
% 3.70/1.00  prop_unsat_core_time:                   0.
% 3.70/1.00  
% 3.70/1.00  ------ QBF
% 3.70/1.00  
% 3.70/1.00  qbf_q_res:                              0
% 3.70/1.00  qbf_num_tautologies:                    0
% 3.70/1.00  qbf_prep_cycles:                        0
% 3.70/1.00  
% 3.70/1.00  ------ BMC1
% 3.70/1.00  
% 3.70/1.00  bmc1_current_bound:                     -1
% 3.70/1.00  bmc1_last_solved_bound:                 -1
% 3.70/1.00  bmc1_unsat_core_size:                   -1
% 3.70/1.00  bmc1_unsat_core_parents_size:           -1
% 3.70/1.00  bmc1_merge_next_fun:                    0
% 3.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation
% 3.70/1.00  
% 3.70/1.00  inst_num_of_clauses:                    240
% 3.70/1.00  inst_num_in_passive:                    17
% 3.70/1.00  inst_num_in_active:                     149
% 3.70/1.00  inst_num_in_unprocessed:                74
% 3.70/1.00  inst_num_of_loops:                      170
% 3.70/1.00  inst_num_of_learning_restarts:          0
% 3.70/1.00  inst_num_moves_active_passive:          18
% 3.70/1.00  inst_lit_activity:                      0
% 3.70/1.00  inst_lit_activity_moves:                0
% 3.70/1.00  inst_num_tautologies:                   0
% 3.70/1.00  inst_num_prop_implied:                  0
% 3.70/1.00  inst_num_existing_simplified:           0
% 3.70/1.00  inst_num_eq_res_simplified:             0
% 3.70/1.00  inst_num_child_elim:                    0
% 3.70/1.00  inst_num_of_dismatching_blockings:      186
% 3.70/1.00  inst_num_of_non_proper_insts:           334
% 3.70/1.00  inst_num_of_duplicates:                 0
% 3.70/1.00  inst_inst_num_from_inst_to_res:         0
% 3.70/1.00  inst_dismatching_checking_time:         0.
% 3.70/1.00  
% 3.70/1.00  ------ Resolution
% 3.70/1.00  
% 3.70/1.00  res_num_of_clauses:                     0
% 3.70/1.00  res_num_in_passive:                     0
% 3.70/1.00  res_num_in_active:                      0
% 3.70/1.00  res_num_of_loops:                       109
% 3.70/1.00  res_forward_subset_subsumed:            159
% 3.70/1.00  res_backward_subset_subsumed:           0
% 3.70/1.00  res_forward_subsumed:                   2
% 3.70/1.00  res_backward_subsumed:                  0
% 3.70/1.00  res_forward_subsumption_resolution:     0
% 3.70/1.00  res_backward_subsumption_resolution:    0
% 3.70/1.00  res_clause_to_clause_subsumption:       329
% 3.70/1.00  res_orphan_elimination:                 0
% 3.70/1.00  res_tautology_del:                      30
% 3.70/1.00  res_num_eq_res_simplified:              0
% 3.70/1.00  res_num_sel_changes:                    0
% 3.70/1.00  res_moves_from_active_to_pass:          0
% 3.70/1.00  
% 3.70/1.00  ------ Superposition
% 3.70/1.00  
% 3.70/1.00  sup_time_total:                         0.
% 3.70/1.00  sup_time_generating:                    0.
% 3.70/1.00  sup_time_sim_full:                      0.
% 3.70/1.00  sup_time_sim_immed:                     0.
% 3.70/1.00  
% 3.70/1.00  sup_num_of_clauses:                     59
% 3.70/1.00  sup_num_in_active:                      27
% 3.70/1.00  sup_num_in_passive:                     32
% 3.70/1.00  sup_num_of_loops:                       33
% 3.70/1.00  sup_fw_superposition:                   131
% 3.70/1.00  sup_bw_superposition:                   68
% 3.70/1.00  sup_immediate_simplified:               169
% 3.70/1.00  sup_given_eliminated:                   3
% 3.70/1.00  comparisons_done:                       0
% 3.70/1.00  comparisons_avoided:                    2
% 3.70/1.00  
% 3.70/1.00  ------ Simplifications
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  sim_fw_subset_subsumed:                 1
% 3.70/1.00  sim_bw_subset_subsumed:                 0
% 3.70/1.00  sim_fw_subsumed:                        43
% 3.70/1.00  sim_bw_subsumed:                        6
% 3.70/1.00  sim_fw_subsumption_res:                 0
% 3.70/1.00  sim_bw_subsumption_res:                 0
% 3.70/1.00  sim_tautology_del:                      0
% 3.70/1.00  sim_eq_tautology_del:                   42
% 3.70/1.00  sim_eq_res_simp:                        0
% 3.70/1.00  sim_fw_demodulated:                     108
% 3.70/1.00  sim_bw_demodulated:                     5
% 3.70/1.00  sim_light_normalised:                   51
% 3.70/1.00  sim_joinable_taut:                      0
% 3.70/1.00  sim_joinable_simp:                      0
% 3.70/1.00  sim_ac_normalised:                      0
% 3.70/1.00  sim_smt_subsumption:                    0
% 3.70/1.00  
%------------------------------------------------------------------------------
