%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:33 EST 2020

% Result     : Theorem 12.09s
% Output     : CNFRefutation 12.09s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 707 expanded)
%              Number of clauses        :   36 (  77 expanded)
%              Number of leaves         :   15 ( 200 expanded)
%              Depth                    :   19
%              Number of atoms          :  353 (2150 expanded)
%              Number of equality atoms :  185 (1182 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f34,f37])).

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

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
      & r2_hidden(sK5,sK2)
      & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
    & r2_hidden(sK5,sK2)
    & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f28])).

fof(f51,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f52,plain,(
    k3_xboole_0(sK3,sK4) = k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f74,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f52,f37,f60])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f38,f59])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f54,plain,(
    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f54,f37,f60])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f80,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f71])).

fof(f81,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f53,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28890,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28889,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_28883,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_28892,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_29599,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_28883,c_28892])).

cnf(c_29885,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = X1
    | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_28889,c_29599])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28888,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28885,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_29448,plain,
    ( sK5 = X0
    | r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_28885])).

cnf(c_29606,plain,
    ( sK5 = X0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_28888,c_29448])).

cnf(c_30549,plain,
    ( sK0(sK2,X0,X1) = sK5
    | k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = X1
    | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_29885,c_29606])).

cnf(c_37906,plain,
    ( sK0(sK2,sK4,X0) = sK5
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = X0
    | r2_hidden(sK0(sK2,sK4,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_28890,c_30549])).

cnf(c_39524,plain,
    ( sK0(sK2,sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_37906,c_29448])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3904,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_13,c_15])).

cnf(c_40017,plain,
    ( sK0(sK2,sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_39524,c_3904])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28891,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_40020,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
    | r2_hidden(sK0(sK2,sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(sK0(sK2,sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),sK4) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_40017,c_28891])).

cnf(c_40037,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
    | r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_40020,c_40017])).

cnf(c_11,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3886,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4170,plain,
    ( r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_3886])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3889,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4449,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4170,c_3889])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,plain,
    ( r2_hidden(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_40037,c_4449,c_4170,c_3904,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 12.09/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.09/2.00  
% 12.09/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.09/2.00  
% 12.09/2.00  ------  iProver source info
% 12.09/2.00  
% 12.09/2.00  git: date: 2020-06-30 10:37:57 +0100
% 12.09/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.09/2.00  git: non_committed_changes: false
% 12.09/2.00  git: last_make_outside_of_git: false
% 12.09/2.00  
% 12.09/2.00  ------ 
% 12.09/2.00  ------ Parsing...
% 12.09/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  ------ Proving...
% 12.09/2.00  ------ Problem Properties 
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  clauses                                 17
% 12.09/2.00  conjectures                             4
% 12.09/2.00  EPR                                     3
% 12.09/2.00  Horn                                    13
% 12.09/2.00  unary                                   6
% 12.09/2.00  binary                                  2
% 12.09/2.00  lits                                    39
% 12.09/2.00  lits eq                                 14
% 12.09/2.00  fd_pure                                 0
% 12.09/2.00  fd_pseudo                               0
% 12.09/2.00  fd_cond                                 0
% 12.09/2.00  fd_pseudo_cond                          6
% 12.09/2.00  AC symbols                              0
% 12.09/2.00  
% 12.09/2.00  ------ Input Options Time Limit: Unbounded
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing...
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 12.09/2.00  Current options:
% 12.09/2.00  ------ 
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.09/2.00  
% 12.09/2.00  ------ Proving...
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  % SZS status Theorem for theBenchmark.p
% 12.09/2.00  
% 12.09/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 12.09/2.00  
% 12.09/2.00  fof(f2,axiom,(
% 12.09/2.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f18,plain,(
% 12.09/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 12.09/2.00    inference(nnf_transformation,[],[f2])).
% 12.09/2.00  
% 12.09/2.00  fof(f19,plain,(
% 12.09/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 12.09/2.00    inference(flattening,[],[f18])).
% 12.09/2.00  
% 12.09/2.00  fof(f20,plain,(
% 12.09/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 12.09/2.00    inference(rectify,[],[f19])).
% 12.09/2.00  
% 12.09/2.00  fof(f21,plain,(
% 12.09/2.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 12.09/2.00    introduced(choice_axiom,[])).
% 12.09/2.00  
% 12.09/2.00  fof(f22,plain,(
% 12.09/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 12.09/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 12.09/2.00  
% 12.09/2.00  fof(f35,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f22])).
% 12.09/2.00  
% 12.09/2.00  fof(f3,axiom,(
% 12.09/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f37,plain,(
% 12.09/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.09/2.00    inference(cnf_transformation,[],[f3])).
% 12.09/2.00  
% 12.09/2.00  fof(f62,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f35,f37])).
% 12.09/2.00  
% 12.09/2.00  fof(f34,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f22])).
% 12.09/2.00  
% 12.09/2.00  fof(f63,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f34,f37])).
% 12.09/2.00  
% 12.09/2.00  fof(f12,conjecture,(
% 12.09/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f13,negated_conjecture,(
% 12.09/2.00    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 12.09/2.00    inference(negated_conjecture,[],[f12])).
% 12.09/2.00  
% 12.09/2.00  fof(f16,plain,(
% 12.09/2.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 12.09/2.00    inference(ennf_transformation,[],[f13])).
% 12.09/2.00  
% 12.09/2.00  fof(f17,plain,(
% 12.09/2.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 12.09/2.00    inference(flattening,[],[f16])).
% 12.09/2.00  
% 12.09/2.00  fof(f28,plain,(
% 12.09/2.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3))),
% 12.09/2.00    introduced(choice_axiom,[])).
% 12.09/2.00  
% 12.09/2.00  fof(f29,plain,(
% 12.09/2.00    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3)),
% 12.09/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f28])).
% 12.09/2.00  
% 12.09/2.00  fof(f51,plain,(
% 12.09/2.00    r1_tarski(sK2,sK3)),
% 12.09/2.00    inference(cnf_transformation,[],[f29])).
% 12.09/2.00  
% 12.09/2.00  fof(f1,axiom,(
% 12.09/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f14,plain,(
% 12.09/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.09/2.00    inference(unused_predicate_definition_removal,[],[f1])).
% 12.09/2.00  
% 12.09/2.00  fof(f15,plain,(
% 12.09/2.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 12.09/2.00    inference(ennf_transformation,[],[f14])).
% 12.09/2.00  
% 12.09/2.00  fof(f30,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f15])).
% 12.09/2.00  
% 12.09/2.00  fof(f33,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 12.09/2.00    inference(cnf_transformation,[],[f22])).
% 12.09/2.00  
% 12.09/2.00  fof(f64,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 12.09/2.00    inference(definition_unfolding,[],[f33,f37])).
% 12.09/2.00  
% 12.09/2.00  fof(f75,plain,(
% 12.09/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 12.09/2.00    inference(equality_resolution,[],[f64])).
% 12.09/2.00  
% 12.09/2.00  fof(f52,plain,(
% 12.09/2.00    k3_xboole_0(sK3,sK4) = k1_tarski(sK5)),
% 12.09/2.00    inference(cnf_transformation,[],[f29])).
% 12.09/2.00  
% 12.09/2.00  fof(f5,axiom,(
% 12.09/2.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f44,plain,(
% 12.09/2.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f5])).
% 12.09/2.00  
% 12.09/2.00  fof(f6,axiom,(
% 12.09/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f45,plain,(
% 12.09/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f6])).
% 12.09/2.00  
% 12.09/2.00  fof(f7,axiom,(
% 12.09/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f46,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f7])).
% 12.09/2.00  
% 12.09/2.00  fof(f8,axiom,(
% 12.09/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f47,plain,(
% 12.09/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f8])).
% 12.09/2.00  
% 12.09/2.00  fof(f9,axiom,(
% 12.09/2.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f48,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f9])).
% 12.09/2.00  
% 12.09/2.00  fof(f10,axiom,(
% 12.09/2.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f49,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f10])).
% 12.09/2.00  
% 12.09/2.00  fof(f11,axiom,(
% 12.09/2.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f50,plain,(
% 12.09/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f11])).
% 12.09/2.00  
% 12.09/2.00  fof(f55,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f49,f50])).
% 12.09/2.00  
% 12.09/2.00  fof(f56,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f48,f55])).
% 12.09/2.00  
% 12.09/2.00  fof(f57,plain,(
% 12.09/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f47,f56])).
% 12.09/2.00  
% 12.09/2.00  fof(f58,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f46,f57])).
% 12.09/2.00  
% 12.09/2.00  fof(f59,plain,(
% 12.09/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f45,f58])).
% 12.09/2.00  
% 12.09/2.00  fof(f60,plain,(
% 12.09/2.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f44,f59])).
% 12.09/2.00  
% 12.09/2.00  fof(f74,plain,(
% 12.09/2.00    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),
% 12.09/2.00    inference(definition_unfolding,[],[f52,f37,f60])).
% 12.09/2.00  
% 12.09/2.00  fof(f4,axiom,(
% 12.09/2.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f23,plain,(
% 12.09/2.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 12.09/2.00    inference(nnf_transformation,[],[f4])).
% 12.09/2.00  
% 12.09/2.00  fof(f24,plain,(
% 12.09/2.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 12.09/2.00    inference(flattening,[],[f23])).
% 12.09/2.00  
% 12.09/2.00  fof(f25,plain,(
% 12.09/2.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 12.09/2.00    inference(rectify,[],[f24])).
% 12.09/2.00  
% 12.09/2.00  fof(f26,plain,(
% 12.09/2.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 12.09/2.00    introduced(choice_axiom,[])).
% 12.09/2.00  
% 12.09/2.00  fof(f27,plain,(
% 12.09/2.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 12.09/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 12.09/2.00  
% 12.09/2.00  fof(f38,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 12.09/2.00    inference(cnf_transformation,[],[f27])).
% 12.09/2.00  
% 12.09/2.00  fof(f72,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 12.09/2.00    inference(definition_unfolding,[],[f38,f59])).
% 12.09/2.00  
% 12.09/2.00  fof(f82,plain,(
% 12.09/2.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 12.09/2.00    inference(equality_resolution,[],[f72])).
% 12.09/2.00  
% 12.09/2.00  fof(f54,plain,(
% 12.09/2.00    k3_xboole_0(sK2,sK4) != k1_tarski(sK5)),
% 12.09/2.00    inference(cnf_transformation,[],[f29])).
% 12.09/2.00  
% 12.09/2.00  fof(f73,plain,(
% 12.09/2.00    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),
% 12.09/2.00    inference(definition_unfolding,[],[f54,f37,f60])).
% 12.09/2.00  
% 12.09/2.00  fof(f36,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f22])).
% 12.09/2.00  
% 12.09/2.00  fof(f61,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f36,f37])).
% 12.09/2.00  
% 12.09/2.00  fof(f39,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 12.09/2.00    inference(cnf_transformation,[],[f27])).
% 12.09/2.00  
% 12.09/2.00  fof(f71,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 12.09/2.00    inference(definition_unfolding,[],[f39,f59])).
% 12.09/2.00  
% 12.09/2.00  fof(f80,plain,(
% 12.09/2.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 12.09/2.00    inference(equality_resolution,[],[f71])).
% 12.09/2.00  
% 12.09/2.00  fof(f81,plain,(
% 12.09/2.00    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 12.09/2.00    inference(equality_resolution,[],[f80])).
% 12.09/2.00  
% 12.09/2.00  fof(f32,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 12.09/2.00    inference(cnf_transformation,[],[f22])).
% 12.09/2.00  
% 12.09/2.00  fof(f65,plain,(
% 12.09/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 12.09/2.00    inference(definition_unfolding,[],[f32,f37])).
% 12.09/2.00  
% 12.09/2.00  fof(f76,plain,(
% 12.09/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 12.09/2.00    inference(equality_resolution,[],[f65])).
% 12.09/2.00  
% 12.09/2.00  fof(f53,plain,(
% 12.09/2.00    r2_hidden(sK5,sK2)),
% 12.09/2.00    inference(cnf_transformation,[],[f29])).
% 12.09/2.00  
% 12.09/2.00  cnf(c_2,plain,
% 12.09/2.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 12.09/2.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 12.09/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 12.09/2.00      inference(cnf_transformation,[],[f62]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_28890,plain,
% 12.09/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 12.09/2.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 12.09/2.00      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_3,plain,
% 12.09/2.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 12.09/2.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 12.09/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 12.09/2.00      inference(cnf_transformation,[],[f63]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_28889,plain,
% 12.09/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 12.09/2.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 12.09/2.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_16,negated_conjecture,
% 12.09/2.00      ( r1_tarski(sK2,sK3) ),
% 12.09/2.00      inference(cnf_transformation,[],[f51]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_28883,plain,
% 12.09/2.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_0,plain,
% 12.09/2.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 12.09/2.00      inference(cnf_transformation,[],[f30]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_28892,plain,
% 12.09/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.09/2.00      | r2_hidden(X2,X0) != iProver_top
% 12.09/2.00      | r2_hidden(X2,X1) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_29599,plain,
% 12.09/2.00      ( r2_hidden(X0,sK3) = iProver_top
% 12.09/2.00      | r2_hidden(X0,sK2) != iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_28883,c_28892]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_29885,plain,
% 12.09/2.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = X1
% 12.09/2.00      | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
% 12.09/2.00      | r2_hidden(sK0(sK2,X0,X1),sK3) = iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_28889,c_29599]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_4,plain,
% 12.09/2.00      ( ~ r2_hidden(X0,X1)
% 12.09/2.00      | ~ r2_hidden(X0,X2)
% 12.09/2.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 12.09/2.00      inference(cnf_transformation,[],[f75]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_28888,plain,
% 12.09/2.00      ( r2_hidden(X0,X1) != iProver_top
% 12.09/2.00      | r2_hidden(X0,X2) != iProver_top
% 12.09/2.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_15,negated_conjecture,
% 12.09/2.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 12.09/2.00      inference(cnf_transformation,[],[f74]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_12,plain,
% 12.09/2.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 12.09/2.00      | X0 = X1
% 12.09/2.00      | X0 = X2 ),
% 12.09/2.00      inference(cnf_transformation,[],[f82]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_28885,plain,
% 12.09/2.00      ( X0 = X1
% 12.09/2.00      | X0 = X2
% 12.09/2.00      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_29448,plain,
% 12.09/2.00      ( sK5 = X0
% 12.09/2.00      | r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_15,c_28885]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_29606,plain,
% 12.09/2.00      ( sK5 = X0
% 12.09/2.00      | r2_hidden(X0,sK3) != iProver_top
% 12.09/2.00      | r2_hidden(X0,sK4) != iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_28888,c_29448]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_30549,plain,
% 12.09/2.00      ( sK0(sK2,X0,X1) = sK5
% 12.09/2.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = X1
% 12.09/2.00      | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
% 12.09/2.00      | r2_hidden(sK0(sK2,X0,X1),sK4) != iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_29885,c_29606]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_37906,plain,
% 12.09/2.00      ( sK0(sK2,sK4,X0) = sK5
% 12.09/2.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = X0
% 12.09/2.00      | r2_hidden(sK0(sK2,sK4,X0),X0) = iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_28890,c_30549]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_39524,plain,
% 12.09/2.00      ( sK0(sK2,sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5
% 12.09/2.00      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_37906,c_29448]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_13,negated_conjecture,
% 12.09/2.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 12.09/2.00      inference(cnf_transformation,[],[f73]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_3904,plain,
% 12.09/2.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 12.09/2.00      inference(light_normalisation,[status(thm)],[c_13,c_15]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_40017,plain,
% 12.09/2.00      ( sK0(sK2,sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5 ),
% 12.09/2.00      inference(global_propositional_subsumption,
% 12.09/2.00                [status(thm)],
% 12.09/2.00                [c_39524,c_3904]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1,plain,
% 12.09/2.00      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 12.09/2.00      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 12.09/2.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 12.09/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 12.09/2.00      inference(cnf_transformation,[],[f61]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_28891,plain,
% 12.09/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 12.09/2.00      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 12.09/2.00      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 12.09/2.00      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_40020,plain,
% 12.09/2.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
% 12.09/2.00      | r2_hidden(sK0(sK2,sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
% 12.09/2.00      | r2_hidden(sK0(sK2,sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),sK4) != iProver_top
% 12.09/2.00      | r2_hidden(sK5,sK2) != iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_40017,c_28891]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_40037,plain,
% 12.09/2.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
% 12.09/2.00      | r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
% 12.09/2.00      | r2_hidden(sK5,sK4) != iProver_top
% 12.09/2.00      | r2_hidden(sK5,sK2) != iProver_top ),
% 12.09/2.00      inference(light_normalisation,[status(thm)],[c_40020,c_40017]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_11,plain,
% 12.09/2.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 12.09/2.00      inference(cnf_transformation,[],[f81]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_3886,plain,
% 12.09/2.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_4170,plain,
% 12.09/2.00      ( r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_15,c_3886]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_5,plain,
% 12.09/2.00      ( r2_hidden(X0,X1)
% 12.09/2.00      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 12.09/2.00      inference(cnf_transformation,[],[f76]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_3889,plain,
% 12.09/2.00      ( r2_hidden(X0,X1) = iProver_top
% 12.09/2.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_4449,plain,
% 12.09/2.00      ( r2_hidden(sK5,sK4) = iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_4170,c_3889]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_14,negated_conjecture,
% 12.09/2.00      ( r2_hidden(sK5,sK2) ),
% 12.09/2.00      inference(cnf_transformation,[],[f53]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_18,plain,
% 12.09/2.00      ( r2_hidden(sK5,sK2) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(contradiction,plain,
% 12.09/2.00      ( $false ),
% 12.09/2.00      inference(minisat,[status(thm)],[c_40037,c_4449,c_4170,c_3904,c_18]) ).
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 12.09/2.00  
% 12.09/2.00  ------                               Statistics
% 12.09/2.00  
% 12.09/2.00  ------ Selected
% 12.09/2.00  
% 12.09/2.00  total_time:                             1.456
% 12.09/2.00  
%------------------------------------------------------------------------------
