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
% DateTime   : Thu Dec  3 11:38:33 EST 2020

% Result     : Timeout 59.26s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  126 ( 580 expanded)
%              Number of clauses        :   64 (  95 expanded)
%              Number of leaves         :   17 ( 162 expanded)
%              Depth                    :   19
%              Number of atoms          :  357 (1864 expanded)
%              Number of equality atoms :  167 ( 730 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
      & r2_hidden(sK4,sK1)
      & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
    & r2_hidden(sK4,sK1)
    & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f25])).

fof(f44,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f45,plain,(
    k3_xboole_0(sK2,sK3) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f63,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f45,f34,f53])).

fof(f46,plain,(
    r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f34,f52,f53])).

fof(f67,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f47,plain,(
    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f47,f34,f53])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f34])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_397,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_396,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_121,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_122,plain,
    ( r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_121])).

cnf(c_389,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_122])).

cnf(c_814,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = X1
    | r2_hidden(sK0(sK1,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK1,X0,X1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_396,c_389])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_395,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_390,plain,
    ( r2_hidden(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_392,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_935,plain,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK1)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_390,c_392])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_394,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1999,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_935,c_394])).

cnf(c_2361,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1999])).

cnf(c_2390,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_395,c_2361])).

cnf(c_2895,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = X1
    | r2_hidden(sK0(sK1,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK1,X0,X1),sK3) != iProver_top
    | r2_hidden(sK0(sK1,X0,X1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_2390])).

cnf(c_127518,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = X0
    | r2_hidden(sK0(sK1,sK3,X0),X0) = iProver_top
    | r2_hidden(sK0(sK1,sK3,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_397,c_2895])).

cnf(c_934,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_395,c_392])).

cnf(c_8660,plain,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_390,c_934])).

cnf(c_32405,plain,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_390,c_8660])).

cnf(c_32996,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_32405,c_394])).

cnf(c_128138,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = iProver_top
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_127518,c_32996])).

cnf(c_209,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3480,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_27880,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3480])).

cnf(c_30023,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_27880])).

cnf(c_30024,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30023])).

cnf(c_2487,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(X3,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))
    | X3 != X2 ),
    inference(resolution,[status(thm)],[c_7,c_209])).

cnf(c_9,negated_conjecture,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2194,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(resolution,[status(thm)],[c_2,c_9])).

cnf(c_9896,plain,
    ( r2_hidden(X0,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X1)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
    | ~ r2_hidden(sK4,X1)
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_2487,c_2194])).

cnf(c_3493,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_980,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_209,c_11])).

cnf(c_3010,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_2194,c_980])).

cnf(c_207,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4123,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(resolution,[status(thm)],[c_3010,c_207])).

cnf(c_10772,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9896,c_3493,c_4123])).

cnf(c_10774,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10772])).

cnf(c_3789,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3790,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3789])).

cnf(c_2264,plain,
    ( sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_1099,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_1102,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2) = iProver_top
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_435,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,X1)))
    | ~ r2_hidden(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_856,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_860,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_208,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_549,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_208,c_207])).

cnf(c_642,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_549,c_11])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_608,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_609,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_569,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_428,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != X0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_568,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_428])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_128138,c_30024,c_10774,c_3790,c_2264,c_1102,c_860,c_642,c_609,c_569,c_568,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.26/7.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.26/7.98  
% 59.26/7.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.26/7.98  
% 59.26/7.98  ------  iProver source info
% 59.26/7.98  
% 59.26/7.98  git: date: 2020-06-30 10:37:57 +0100
% 59.26/7.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.26/7.98  git: non_committed_changes: false
% 59.26/7.98  git: last_make_outside_of_git: false
% 59.26/7.98  
% 59.26/7.98  ------ 
% 59.26/7.98  ------ Parsing...
% 59.26/7.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.26/7.98  
% 59.26/7.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 59.26/7.98  
% 59.26/7.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.26/7.98  
% 59.26/7.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.26/7.98  ------ Proving...
% 59.26/7.98  ------ Problem Properties 
% 59.26/7.98  
% 59.26/7.98  
% 59.26/7.98  clauses                                 12
% 59.26/7.98  conjectures                             3
% 59.26/7.98  EPR                                     2
% 59.26/7.98  Horn                                    9
% 59.26/7.98  unary                                   3
% 59.26/7.98  binary                                  4
% 59.26/7.98  lits                                    27
% 59.26/7.98  lits eq                                 7
% 59.26/7.98  fd_pure                                 0
% 59.26/7.98  fd_pseudo                               0
% 59.26/7.98  fd_cond                                 0
% 59.26/7.98  fd_pseudo_cond                          3
% 59.26/7.98  AC symbols                              0
% 59.26/7.98  
% 59.26/7.98  ------ Input Options Time Limit: Unbounded
% 59.26/7.98  
% 59.26/7.98  
% 59.26/7.98  ------ 
% 59.26/7.98  Current options:
% 59.26/7.98  ------ 
% 59.26/7.98  
% 59.26/7.98  
% 59.26/7.98  
% 59.26/7.98  
% 59.26/7.98  ------ Proving...
% 59.26/7.98  
% 59.26/7.98  
% 59.26/7.98  % SZS status Theorem for theBenchmark.p
% 59.26/7.98  
% 59.26/7.98  % SZS output start CNFRefutation for theBenchmark.p
% 59.26/7.98  
% 59.26/7.98  fof(f2,axiom,(
% 59.26/7.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f20,plain,(
% 59.26/7.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 59.26/7.98    inference(nnf_transformation,[],[f2])).
% 59.26/7.98  
% 59.26/7.98  fof(f21,plain,(
% 59.26/7.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 59.26/7.98    inference(flattening,[],[f20])).
% 59.26/7.98  
% 59.26/7.98  fof(f22,plain,(
% 59.26/7.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 59.26/7.98    inference(rectify,[],[f21])).
% 59.26/7.98  
% 59.26/7.98  fof(f23,plain,(
% 59.26/7.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 59.26/7.98    introduced(choice_axiom,[])).
% 59.26/7.98  
% 59.26/7.98  fof(f24,plain,(
% 59.26/7.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 59.26/7.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 59.26/7.98  
% 59.26/7.98  fof(f32,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f24])).
% 59.26/7.98  
% 59.26/7.98  fof(f3,axiom,(
% 59.26/7.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f34,plain,(
% 59.26/7.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 59.26/7.98    inference(cnf_transformation,[],[f3])).
% 59.26/7.98  
% 59.26/7.98  fof(f55,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f32,f34])).
% 59.26/7.98  
% 59.26/7.98  fof(f31,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f24])).
% 59.26/7.98  
% 59.26/7.98  fof(f56,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f31,f34])).
% 59.26/7.98  
% 59.26/7.98  fof(f1,axiom,(
% 59.26/7.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f14,plain,(
% 59.26/7.98    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 59.26/7.98    inference(unused_predicate_definition_removal,[],[f1])).
% 59.26/7.98  
% 59.26/7.98  fof(f15,plain,(
% 59.26/7.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 59.26/7.98    inference(ennf_transformation,[],[f14])).
% 59.26/7.98  
% 59.26/7.98  fof(f27,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f15])).
% 59.26/7.98  
% 59.26/7.98  fof(f12,conjecture,(
% 59.26/7.98    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f13,negated_conjecture,(
% 59.26/7.98    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 59.26/7.98    inference(negated_conjecture,[],[f12])).
% 59.26/7.98  
% 59.26/7.98  fof(f18,plain,(
% 59.26/7.98    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 59.26/7.98    inference(ennf_transformation,[],[f13])).
% 59.26/7.98  
% 59.26/7.98  fof(f19,plain,(
% 59.26/7.98    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 59.26/7.98    inference(flattening,[],[f18])).
% 59.26/7.98  
% 59.26/7.98  fof(f25,plain,(
% 59.26/7.98    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2))),
% 59.26/7.98    introduced(choice_axiom,[])).
% 59.26/7.98  
% 59.26/7.98  fof(f26,plain,(
% 59.26/7.98    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2)),
% 59.26/7.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f25])).
% 59.26/7.98  
% 59.26/7.98  fof(f44,plain,(
% 59.26/7.98    r1_tarski(sK1,sK2)),
% 59.26/7.98    inference(cnf_transformation,[],[f26])).
% 59.26/7.98  
% 59.26/7.98  fof(f30,plain,(
% 59.26/7.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 59.26/7.98    inference(cnf_transformation,[],[f24])).
% 59.26/7.98  
% 59.26/7.98  fof(f57,plain,(
% 59.26/7.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 59.26/7.98    inference(definition_unfolding,[],[f30,f34])).
% 59.26/7.98  
% 59.26/7.98  fof(f64,plain,(
% 59.26/7.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 59.26/7.98    inference(equality_resolution,[],[f57])).
% 59.26/7.98  
% 59.26/7.98  fof(f45,plain,(
% 59.26/7.98    k3_xboole_0(sK2,sK3) = k1_tarski(sK4)),
% 59.26/7.98    inference(cnf_transformation,[],[f26])).
% 59.26/7.98  
% 59.26/7.98  fof(f4,axiom,(
% 59.26/7.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f35,plain,(
% 59.26/7.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f4])).
% 59.26/7.98  
% 59.26/7.98  fof(f5,axiom,(
% 59.26/7.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f36,plain,(
% 59.26/7.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f5])).
% 59.26/7.98  
% 59.26/7.98  fof(f6,axiom,(
% 59.26/7.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f37,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f6])).
% 59.26/7.98  
% 59.26/7.98  fof(f7,axiom,(
% 59.26/7.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f38,plain,(
% 59.26/7.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f7])).
% 59.26/7.98  
% 59.26/7.98  fof(f8,axiom,(
% 59.26/7.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f39,plain,(
% 59.26/7.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f8])).
% 59.26/7.98  
% 59.26/7.98  fof(f9,axiom,(
% 59.26/7.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f40,plain,(
% 59.26/7.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f9])).
% 59.26/7.98  
% 59.26/7.98  fof(f10,axiom,(
% 59.26/7.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f41,plain,(
% 59.26/7.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f10])).
% 59.26/7.98  
% 59.26/7.98  fof(f48,plain,(
% 59.26/7.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f40,f41])).
% 59.26/7.98  
% 59.26/7.98  fof(f49,plain,(
% 59.26/7.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f39,f48])).
% 59.26/7.98  
% 59.26/7.98  fof(f50,plain,(
% 59.26/7.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f38,f49])).
% 59.26/7.98  
% 59.26/7.98  fof(f51,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f37,f50])).
% 59.26/7.98  
% 59.26/7.98  fof(f52,plain,(
% 59.26/7.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f36,f51])).
% 59.26/7.98  
% 59.26/7.98  fof(f53,plain,(
% 59.26/7.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f35,f52])).
% 59.26/7.98  
% 59.26/7.98  fof(f63,plain,(
% 59.26/7.98    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 59.26/7.98    inference(definition_unfolding,[],[f45,f34,f53])).
% 59.26/7.98  
% 59.26/7.98  fof(f46,plain,(
% 59.26/7.98    r2_hidden(sK4,sK1)),
% 59.26/7.98    inference(cnf_transformation,[],[f26])).
% 59.26/7.98  
% 59.26/7.98  fof(f11,axiom,(
% 59.26/7.98    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 59.26/7.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.98  
% 59.26/7.98  fof(f16,plain,(
% 59.26/7.98    ! [X0,X1,X2] : ((k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 59.26/7.98    inference(ennf_transformation,[],[f11])).
% 59.26/7.98  
% 59.26/7.98  fof(f17,plain,(
% 59.26/7.98    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 59.26/7.98    inference(flattening,[],[f16])).
% 59.26/7.98  
% 59.26/7.98  fof(f43,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f17])).
% 59.26/7.98  
% 59.26/7.98  fof(f60,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f43,f34,f52,f53])).
% 59.26/7.98  
% 59.26/7.98  fof(f67,plain,(
% 59.26/7.98    ( ! [X2,X1] : (k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) | ~r2_hidden(X2,X1)) )),
% 59.26/7.98    inference(equality_resolution,[],[f60])).
% 59.26/7.98  
% 59.26/7.98  fof(f29,plain,(
% 59.26/7.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 59.26/7.98    inference(cnf_transformation,[],[f24])).
% 59.26/7.98  
% 59.26/7.98  fof(f58,plain,(
% 59.26/7.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 59.26/7.98    inference(definition_unfolding,[],[f29,f34])).
% 59.26/7.98  
% 59.26/7.98  fof(f65,plain,(
% 59.26/7.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 59.26/7.98    inference(equality_resolution,[],[f58])).
% 59.26/7.98  
% 59.26/7.98  fof(f47,plain,(
% 59.26/7.98    k3_xboole_0(sK1,sK3) != k1_tarski(sK4)),
% 59.26/7.98    inference(cnf_transformation,[],[f26])).
% 59.26/7.98  
% 59.26/7.98  fof(f62,plain,(
% 59.26/7.98    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 59.26/7.98    inference(definition_unfolding,[],[f47,f34,f53])).
% 59.26/7.98  
% 59.26/7.98  fof(f33,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 59.26/7.98    inference(cnf_transformation,[],[f24])).
% 59.26/7.98  
% 59.26/7.98  fof(f54,plain,(
% 59.26/7.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 59.26/7.98    inference(definition_unfolding,[],[f33,f34])).
% 59.26/7.98  
% 59.26/7.98  cnf(c_2,plain,
% 59.26/7.98      ( r2_hidden(sK0(X0,X1,X2),X1)
% 59.26/7.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 59.26/7.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 59.26/7.98      inference(cnf_transformation,[],[f55]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_397,plain,
% 59.26/7.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 59.26/7.98      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 59.26/7.98      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_3,plain,
% 59.26/7.98      ( r2_hidden(sK0(X0,X1,X2),X0)
% 59.26/7.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 59.26/7.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 59.26/7.98      inference(cnf_transformation,[],[f56]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_396,plain,
% 59.26/7.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 59.26/7.98      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 59.26/7.98      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_0,plain,
% 59.26/7.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 59.26/7.98      inference(cnf_transformation,[],[f27]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_12,negated_conjecture,
% 59.26/7.98      ( r1_tarski(sK1,sK2) ),
% 59.26/7.98      inference(cnf_transformation,[],[f44]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_121,plain,
% 59.26/7.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK2 != X2 | sK1 != X1 ),
% 59.26/7.98      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_122,plain,
% 59.26/7.98      ( r2_hidden(X0,sK2) | ~ r2_hidden(X0,sK1) ),
% 59.26/7.98      inference(unflattening,[status(thm)],[c_121]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_389,plain,
% 59.26/7.98      ( r2_hidden(X0,sK2) = iProver_top
% 59.26/7.98      | r2_hidden(X0,sK1) != iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_122]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_814,plain,
% 59.26/7.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = X1
% 59.26/7.98      | r2_hidden(sK0(sK1,X0,X1),X1) = iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,X0,X1),sK2) = iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_396,c_389]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_4,plain,
% 59.26/7.98      ( ~ r2_hidden(X0,X1)
% 59.26/7.98      | ~ r2_hidden(X0,X2)
% 59.26/7.98      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 59.26/7.98      inference(cnf_transformation,[],[f64]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_395,plain,
% 59.26/7.98      ( r2_hidden(X0,X1) != iProver_top
% 59.26/7.98      | r2_hidden(X0,X2) != iProver_top
% 59.26/7.98      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_11,negated_conjecture,
% 59.26/7.98      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 59.26/7.98      inference(cnf_transformation,[],[f63]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_10,negated_conjecture,
% 59.26/7.98      ( r2_hidden(sK4,sK1) ),
% 59.26/7.98      inference(cnf_transformation,[],[f46]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_390,plain,
% 59.26/7.98      ( r2_hidden(sK4,sK1) = iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_7,plain,
% 59.26/7.98      ( ~ r2_hidden(X0,X1)
% 59.26/7.98      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 59.26/7.98      inference(cnf_transformation,[],[f67]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_392,plain,
% 59.26/7.98      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 59.26/7.98      | r2_hidden(X0,X1) != iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_935,plain,
% 59.26/7.98      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK1)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_390,c_392]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_5,plain,
% 59.26/7.98      ( r2_hidden(X0,X1)
% 59.26/7.98      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 59.26/7.98      inference(cnf_transformation,[],[f65]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_394,plain,
% 59.26/7.98      ( r2_hidden(X0,X1) = iProver_top
% 59.26/7.98      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_1999,plain,
% 59.26/7.98      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 59.26/7.98      | r2_hidden(X0,sK1) = iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_935,c_394]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_2361,plain,
% 59.26/7.98      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
% 59.26/7.98      | r2_hidden(X0,sK1) = iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_11,c_1999]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_2390,plain,
% 59.26/7.98      ( r2_hidden(X0,sK2) != iProver_top
% 59.26/7.98      | r2_hidden(X0,sK3) != iProver_top
% 59.26/7.98      | r2_hidden(X0,sK1) = iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_395,c_2361]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_2895,plain,
% 59.26/7.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = X1
% 59.26/7.98      | r2_hidden(sK0(sK1,X0,X1),X1) = iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,X0,X1),sK3) != iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,X0,X1),sK1) = iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_814,c_2390]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_127518,plain,
% 59.26/7.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = X0
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,X0),X0) = iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,X0),sK1) = iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_397,c_2895]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_934,plain,
% 59.26/7.98      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 59.26/7.98      | r2_hidden(X0,X2) != iProver_top
% 59.26/7.98      | r2_hidden(X0,X1) != iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_395,c_392]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_8660,plain,
% 59.26/7.98      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 59.26/7.98      | r2_hidden(sK4,X0) != iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_390,c_934]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_32405,plain,
% 59.26/7.98      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_390,c_8660]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_32996,plain,
% 59.26/7.98      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 59.26/7.98      | r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_32405,c_394]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_128138,plain,
% 59.26/7.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) = iProver_top ),
% 59.26/7.98      inference(superposition,[status(thm)],[c_127518,c_32996]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_209,plain,
% 59.26/7.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 59.26/7.98      theory(equality) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_3480,plain,
% 59.26/7.98      ( r2_hidden(X0,X1)
% 59.26/7.98      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 59.26/7.98      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 59.26/7.98      | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_209]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_27880,plain,
% 59.26/7.98      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 59.26/7.98      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 59.26/7.98      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 59.26/7.98      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_3480]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_30023,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 59.26/7.98      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 59.26/7.98      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 59.26/7.98      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_27880]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_30024,plain,
% 59.26/7.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 59.26/7.98      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_30023]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_2487,plain,
% 59.26/7.98      ( ~ r2_hidden(X0,X1)
% 59.26/7.98      | ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 59.26/7.98      | r2_hidden(X3,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))
% 59.26/7.98      | X3 != X2 ),
% 59.26/7.98      inference(resolution,[status(thm)],[c_7,c_209]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_9,negated_conjecture,
% 59.26/7.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 59.26/7.98      inference(cnf_transformation,[],[f62]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_2194,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 59.26/7.98      inference(resolution,[status(thm)],[c_2,c_9]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_9896,plain,
% 59.26/7.98      ( r2_hidden(X0,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X1)))
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
% 59.26/7.98      | ~ r2_hidden(sK4,X1)
% 59.26/7.98      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 59.26/7.98      inference(resolution,[status(thm)],[c_2487,c_2194]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_3493,plain,
% 59.26/7.98      ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_5]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_980,plain,
% 59.26/7.98      ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 59.26/7.98      | r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 59.26/7.98      | X1 != X0 ),
% 59.26/7.98      inference(resolution,[status(thm)],[c_209,c_11]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_3010,plain,
% 59.26/7.98      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
% 59.26/7.98      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 59.26/7.98      inference(resolution,[status(thm)],[c_2194,c_980]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_207,plain,( X0 = X0 ),theory(equality) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_4123,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 59.26/7.98      inference(resolution,[status(thm)],[c_3010,c_207]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_10772,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 59.26/7.98      inference(global_propositional_subsumption,
% 59.26/7.98                [status(thm)],
% 59.26/7.98                [c_9896,c_3493,c_4123]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_10774,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) = iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_10772]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_3789,plain,
% 59.26/7.98      ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_5]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_3790,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) != iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) = iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_3789]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_2264,plain,
% 59.26/7.98      ( sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_207]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_1099,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2)
% 59.26/7.98      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_122]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_1102,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2) = iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) != iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_1099]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_435,plain,
% 59.26/7.98      ( ~ r2_hidden(X0,X1)
% 59.26/7.98      | r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,X1)))
% 59.26/7.98      | ~ r2_hidden(X0,sK2) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_4]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_856,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 59.26/7.98      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2)
% 59.26/7.98      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_435]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_860,plain,
% 59.26/7.98      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2) != iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) != iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_208,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_549,plain,
% 59.26/7.98      ( X0 != X1 | X1 = X0 ),
% 59.26/7.98      inference(resolution,[status(thm)],[c_208,c_207]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_642,plain,
% 59.26/7.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 59.26/7.98      inference(resolution,[status(thm)],[c_549,c_11]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_1,plain,
% 59.26/7.98      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 59.26/7.98      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 59.26/7.98      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 59.26/7.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 59.26/7.98      inference(cnf_transformation,[],[f54]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_608,plain,
% 59.26/7.98      ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 59.26/7.98      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
% 59.26/7.98      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 59.26/7.98      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_1]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_609,plain,
% 59.26/7.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) != iProver_top
% 59.26/7.98      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) != iProver_top ),
% 59.26/7.98      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_569,plain,
% 59.26/7.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_207]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_428,plain,
% 59.26/7.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 59.26/7.98      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != X0
% 59.26/7.98      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_208]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(c_568,plain,
% 59.26/7.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
% 59.26/7.98      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 59.26/7.98      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
% 59.26/7.98      inference(instantiation,[status(thm)],[c_428]) ).
% 59.26/7.98  
% 59.26/7.98  cnf(contradiction,plain,
% 59.26/7.98      ( $false ),
% 59.26/7.98      inference(minisat,
% 59.26/7.98                [status(thm)],
% 59.26/7.98                [c_128138,c_30024,c_10774,c_3790,c_2264,c_1102,c_860,
% 59.26/7.98                 c_642,c_609,c_569,c_568,c_9]) ).
% 59.26/7.98  
% 59.26/7.98  
% 59.26/7.98  % SZS output end CNFRefutation for theBenchmark.p
% 59.26/7.98  
% 59.26/7.98  ------                               Statistics
% 59.26/7.98  
% 59.26/7.98  ------ Selected
% 59.26/7.98  
% 59.26/7.98  total_time:                             7.072
% 59.26/7.98  
%------------------------------------------------------------------------------
