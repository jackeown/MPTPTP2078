%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:16 EST 2020

% Result     : Theorem 23.19s
% Output     : CNFRefutation 23.19s
% Verified   : 
% Statistics : Number of formulae       :  150 (1459 expanded)
%              Number of clauses        :   65 ( 362 expanded)
%              Number of leaves         :   27 ( 418 expanded)
%              Depth                    :   22
%              Number of atoms          :  337 (2284 expanded)
%              Number of equality atoms :  232 (1417 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f51,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK3 != sK6
      & sK3 != sK5
      & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( sK3 != sK6
    & sK3 != sK5
    & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f36,f51])).

fof(f91,plain,(
    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f95,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f116,plain,(
    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f91,f95,f95])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f69,f62])).

fof(f101,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f94,f94])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X3),k3_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f94,f95,f95])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f39])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f37])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f99,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f66,f62,f62])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f25,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f77,f95])).

fof(f113,plain,(
    ! [X0,X1] : k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f88,f96,f95,f96])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f48])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) = k2_enumset1(X0,X0,X0,X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f87,f62,f95,f96])).

fof(f124,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k2_enumset1(X1,X1,X1,X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f109])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f70,f95])).

fof(f123,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f107])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f115,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f89,f62,f96,f96,f96])).

fof(f125,plain,(
    ! [X1] : k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f115])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f90,f62,f96,f96,f96])).

fof(f93,plain,(
    sK3 != sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_703,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_714,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2750,plain,
    ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_703,c_714])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2849,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(superposition,[status(thm)],[c_2750,c_2])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X3),k3_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2178,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X3),k3_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X2,X3,X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_719,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_265,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_701,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_2273,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_719,c_701])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2420,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2273,c_0])).

cnf(c_2430,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2420,c_2273])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2431,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2430,c_4,c_14])).

cnf(c_2852,plain,
    ( k2_enumset1(sK5,sK6,sK3,sK4) = k2_enumset1(sK5,sK5,sK5,sK6) ),
    inference(demodulation,[status(thm)],[c_2849,c_14,c_2178,c_2431])).

cnf(c_3022,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k3_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X0,X1,sK5,sK6) ),
    inference(superposition,[status(thm)],[c_2852,c_1])).

cnf(c_2862,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k5_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k3_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4)))) = k5_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(light_normalisation,[status(thm)],[c_2849,c_2852])).

cnf(c_2863,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k5_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k3_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4)))) = k2_enumset1(sK5,sK6,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2862,c_14,c_2431])).

cnf(c_5150,plain,
    ( k2_enumset1(sK3,sK4,sK5,sK6) = k2_enumset1(sK5,sK6,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3022,c_2863])).

cnf(c_3016,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK6,sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2852,c_703])).

cnf(c_6537,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK4,sK5,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5150,c_3016])).

cnf(c_27,plain,
    ( k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_716,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1186,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_716])).

cnf(c_1664,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1186])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_715,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8110,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) != iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_715])).

cnf(c_64579,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK4,sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6537,c_8110])).

cnf(c_67654,plain,
    ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK4,sK5,sK6)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_64579,c_714])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_707,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_708,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3027,plain,
    ( sK5 = X0
    | sK6 = X0
    | r2_hidden(X0,k2_enumset1(sK5,sK6,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2852,c_708])).

cnf(c_6229,plain,
    ( sK5 = X0
    | sK6 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK4,sK5,sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3027,c_5150])).

cnf(c_6235,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK3,sK4,sK5,sK6))) = k2_enumset1(X0,X0,X0,X0)
    | sK5 = X0
    | sK6 = X0 ),
    inference(superposition,[status(thm)],[c_707,c_6229])).

cnf(c_67737,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK3,sK3,sK3)) = k2_enumset1(sK3,sK3,sK3,sK3)
    | sK5 = sK3
    | sK6 = sK3 ),
    inference(superposition,[status(thm)],[c_67654,c_6235])).

cnf(c_68096,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK5 = sK3
    | sK6 = sK3 ),
    inference(demodulation,[status(thm)],[c_67737,c_2431])).

cnf(c_29,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_720,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_29,c_27])).

cnf(c_10531,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_720,c_2431])).

cnf(c_10532,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10531])).

cnf(c_407,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_771,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_772,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_754,plain,
    ( sK6 != X0
    | sK3 != X0
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_755,plain,
    ( sK6 != sK3
    | sK3 = sK6
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_28,plain,
    ( X0 = X1
    | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_35,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK3,sK3,sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_34,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK3,sK3,sK3))) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( sK3 != sK6 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_31,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_68096,c_10532,c_772,c_755,c_35,c_34,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:41:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.19/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.19/3.49  
% 23.19/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.19/3.49  
% 23.19/3.49  ------  iProver source info
% 23.19/3.49  
% 23.19/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.19/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.19/3.49  git: non_committed_changes: false
% 23.19/3.49  git: last_make_outside_of_git: false
% 23.19/3.49  
% 23.19/3.49  ------ 
% 23.19/3.49  
% 23.19/3.49  ------ Input Options
% 23.19/3.49  
% 23.19/3.49  --out_options                           all
% 23.19/3.49  --tptp_safe_out                         true
% 23.19/3.49  --problem_path                          ""
% 23.19/3.49  --include_path                          ""
% 23.19/3.49  --clausifier                            res/vclausify_rel
% 23.19/3.49  --clausifier_options                    ""
% 23.19/3.49  --stdin                                 false
% 23.19/3.49  --stats_out                             all
% 23.19/3.49  
% 23.19/3.49  ------ General Options
% 23.19/3.49  
% 23.19/3.49  --fof                                   false
% 23.19/3.49  --time_out_real                         305.
% 23.19/3.49  --time_out_virtual                      -1.
% 23.19/3.49  --symbol_type_check                     false
% 23.19/3.49  --clausify_out                          false
% 23.19/3.49  --sig_cnt_out                           false
% 23.19/3.49  --trig_cnt_out                          false
% 23.19/3.49  --trig_cnt_out_tolerance                1.
% 23.19/3.49  --trig_cnt_out_sk_spl                   false
% 23.19/3.49  --abstr_cl_out                          false
% 23.19/3.49  
% 23.19/3.49  ------ Global Options
% 23.19/3.49  
% 23.19/3.49  --schedule                              default
% 23.19/3.49  --add_important_lit                     false
% 23.19/3.49  --prop_solver_per_cl                    1000
% 23.19/3.49  --min_unsat_core                        false
% 23.19/3.49  --soft_assumptions                      false
% 23.19/3.49  --soft_lemma_size                       3
% 23.19/3.49  --prop_impl_unit_size                   0
% 23.19/3.49  --prop_impl_unit                        []
% 23.19/3.49  --share_sel_clauses                     true
% 23.19/3.49  --reset_solvers                         false
% 23.19/3.49  --bc_imp_inh                            [conj_cone]
% 23.19/3.49  --conj_cone_tolerance                   3.
% 23.19/3.49  --extra_neg_conj                        none
% 23.19/3.49  --large_theory_mode                     true
% 23.19/3.49  --prolific_symb_bound                   200
% 23.19/3.49  --lt_threshold                          2000
% 23.19/3.49  --clause_weak_htbl                      true
% 23.19/3.49  --gc_record_bc_elim                     false
% 23.19/3.49  
% 23.19/3.49  ------ Preprocessing Options
% 23.19/3.49  
% 23.19/3.49  --preprocessing_flag                    true
% 23.19/3.49  --time_out_prep_mult                    0.1
% 23.19/3.49  --splitting_mode                        input
% 23.19/3.49  --splitting_grd                         true
% 23.19/3.49  --splitting_cvd                         false
% 23.19/3.49  --splitting_cvd_svl                     false
% 23.19/3.49  --splitting_nvd                         32
% 23.19/3.49  --sub_typing                            true
% 23.19/3.49  --prep_gs_sim                           true
% 23.19/3.49  --prep_unflatten                        true
% 23.19/3.49  --prep_res_sim                          true
% 23.19/3.49  --prep_upred                            true
% 23.19/3.49  --prep_sem_filter                       exhaustive
% 23.19/3.49  --prep_sem_filter_out                   false
% 23.19/3.49  --pred_elim                             true
% 23.19/3.49  --res_sim_input                         true
% 23.19/3.49  --eq_ax_congr_red                       true
% 23.19/3.49  --pure_diseq_elim                       true
% 23.19/3.49  --brand_transform                       false
% 23.19/3.49  --non_eq_to_eq                          false
% 23.19/3.49  --prep_def_merge                        true
% 23.19/3.49  --prep_def_merge_prop_impl              false
% 23.19/3.49  --prep_def_merge_mbd                    true
% 23.19/3.49  --prep_def_merge_tr_red                 false
% 23.19/3.49  --prep_def_merge_tr_cl                  false
% 23.19/3.49  --smt_preprocessing                     true
% 23.19/3.49  --smt_ac_axioms                         fast
% 23.19/3.49  --preprocessed_out                      false
% 23.19/3.49  --preprocessed_stats                    false
% 23.19/3.49  
% 23.19/3.49  ------ Abstraction refinement Options
% 23.19/3.49  
% 23.19/3.49  --abstr_ref                             []
% 23.19/3.49  --abstr_ref_prep                        false
% 23.19/3.49  --abstr_ref_until_sat                   false
% 23.19/3.49  --abstr_ref_sig_restrict                funpre
% 23.19/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.19/3.49  --abstr_ref_under                       []
% 23.19/3.49  
% 23.19/3.49  ------ SAT Options
% 23.19/3.49  
% 23.19/3.49  --sat_mode                              false
% 23.19/3.49  --sat_fm_restart_options                ""
% 23.19/3.49  --sat_gr_def                            false
% 23.19/3.49  --sat_epr_types                         true
% 23.19/3.49  --sat_non_cyclic_types                  false
% 23.19/3.49  --sat_finite_models                     false
% 23.19/3.49  --sat_fm_lemmas                         false
% 23.19/3.49  --sat_fm_prep                           false
% 23.19/3.49  --sat_fm_uc_incr                        true
% 23.19/3.49  --sat_out_model                         small
% 23.19/3.49  --sat_out_clauses                       false
% 23.19/3.49  
% 23.19/3.49  ------ QBF Options
% 23.19/3.49  
% 23.19/3.49  --qbf_mode                              false
% 23.19/3.49  --qbf_elim_univ                         false
% 23.19/3.49  --qbf_dom_inst                          none
% 23.19/3.49  --qbf_dom_pre_inst                      false
% 23.19/3.49  --qbf_sk_in                             false
% 23.19/3.49  --qbf_pred_elim                         true
% 23.19/3.49  --qbf_split                             512
% 23.19/3.49  
% 23.19/3.49  ------ BMC1 Options
% 23.19/3.49  
% 23.19/3.49  --bmc1_incremental                      false
% 23.19/3.49  --bmc1_axioms                           reachable_all
% 23.19/3.49  --bmc1_min_bound                        0
% 23.19/3.49  --bmc1_max_bound                        -1
% 23.19/3.49  --bmc1_max_bound_default                -1
% 23.19/3.49  --bmc1_symbol_reachability              true
% 23.19/3.49  --bmc1_property_lemmas                  false
% 23.19/3.49  --bmc1_k_induction                      false
% 23.19/3.49  --bmc1_non_equiv_states                 false
% 23.19/3.49  --bmc1_deadlock                         false
% 23.19/3.49  --bmc1_ucm                              false
% 23.19/3.49  --bmc1_add_unsat_core                   none
% 23.19/3.49  --bmc1_unsat_core_children              false
% 23.19/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.19/3.49  --bmc1_out_stat                         full
% 23.19/3.49  --bmc1_ground_init                      false
% 23.19/3.49  --bmc1_pre_inst_next_state              false
% 23.19/3.49  --bmc1_pre_inst_state                   false
% 23.19/3.49  --bmc1_pre_inst_reach_state             false
% 23.19/3.49  --bmc1_out_unsat_core                   false
% 23.19/3.49  --bmc1_aig_witness_out                  false
% 23.19/3.49  --bmc1_verbose                          false
% 23.19/3.49  --bmc1_dump_clauses_tptp                false
% 23.19/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.19/3.49  --bmc1_dump_file                        -
% 23.19/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.19/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.19/3.49  --bmc1_ucm_extend_mode                  1
% 23.19/3.49  --bmc1_ucm_init_mode                    2
% 23.19/3.49  --bmc1_ucm_cone_mode                    none
% 23.19/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.19/3.49  --bmc1_ucm_relax_model                  4
% 23.19/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.19/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.19/3.49  --bmc1_ucm_layered_model                none
% 23.19/3.49  --bmc1_ucm_max_lemma_size               10
% 23.19/3.49  
% 23.19/3.49  ------ AIG Options
% 23.19/3.49  
% 23.19/3.49  --aig_mode                              false
% 23.19/3.49  
% 23.19/3.49  ------ Instantiation Options
% 23.19/3.49  
% 23.19/3.49  --instantiation_flag                    true
% 23.19/3.49  --inst_sos_flag                         true
% 23.19/3.49  --inst_sos_phase                        true
% 23.19/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.19/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.19/3.49  --inst_lit_sel_side                     num_symb
% 23.19/3.49  --inst_solver_per_active                1400
% 23.19/3.49  --inst_solver_calls_frac                1.
% 23.19/3.49  --inst_passive_queue_type               priority_queues
% 23.19/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.19/3.49  --inst_passive_queues_freq              [25;2]
% 23.19/3.49  --inst_dismatching                      true
% 23.19/3.49  --inst_eager_unprocessed_to_passive     true
% 23.19/3.49  --inst_prop_sim_given                   true
% 23.19/3.49  --inst_prop_sim_new                     false
% 23.19/3.49  --inst_subs_new                         false
% 23.19/3.49  --inst_eq_res_simp                      false
% 23.19/3.49  --inst_subs_given                       false
% 23.19/3.49  --inst_orphan_elimination               true
% 23.19/3.49  --inst_learning_loop_flag               true
% 23.19/3.49  --inst_learning_start                   3000
% 23.19/3.49  --inst_learning_factor                  2
% 23.19/3.49  --inst_start_prop_sim_after_learn       3
% 23.19/3.49  --inst_sel_renew                        solver
% 23.19/3.49  --inst_lit_activity_flag                true
% 23.19/3.49  --inst_restr_to_given                   false
% 23.19/3.49  --inst_activity_threshold               500
% 23.19/3.49  --inst_out_proof                        true
% 23.19/3.49  
% 23.19/3.49  ------ Resolution Options
% 23.19/3.49  
% 23.19/3.49  --resolution_flag                       true
% 23.19/3.49  --res_lit_sel                           adaptive
% 23.19/3.49  --res_lit_sel_side                      none
% 23.19/3.49  --res_ordering                          kbo
% 23.19/3.49  --res_to_prop_solver                    active
% 23.19/3.49  --res_prop_simpl_new                    false
% 23.19/3.49  --res_prop_simpl_given                  true
% 23.19/3.49  --res_passive_queue_type                priority_queues
% 23.19/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.19/3.49  --res_passive_queues_freq               [15;5]
% 23.19/3.49  --res_forward_subs                      full
% 23.19/3.49  --res_backward_subs                     full
% 23.19/3.49  --res_forward_subs_resolution           true
% 23.19/3.49  --res_backward_subs_resolution          true
% 23.19/3.49  --res_orphan_elimination                true
% 23.19/3.49  --res_time_limit                        2.
% 23.19/3.49  --res_out_proof                         true
% 23.19/3.49  
% 23.19/3.49  ------ Superposition Options
% 23.19/3.49  
% 23.19/3.49  --superposition_flag                    true
% 23.19/3.49  --sup_passive_queue_type                priority_queues
% 23.19/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.19/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.19/3.49  --demod_completeness_check              fast
% 23.19/3.49  --demod_use_ground                      true
% 23.19/3.49  --sup_to_prop_solver                    passive
% 23.19/3.49  --sup_prop_simpl_new                    true
% 23.19/3.49  --sup_prop_simpl_given                  true
% 23.19/3.49  --sup_fun_splitting                     true
% 23.19/3.49  --sup_smt_interval                      50000
% 23.19/3.49  
% 23.19/3.49  ------ Superposition Simplification Setup
% 23.19/3.49  
% 23.19/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.19/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.19/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.19/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.19/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.19/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.19/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.19/3.49  --sup_immed_triv                        [TrivRules]
% 23.19/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.19/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.19/3.49  --sup_immed_bw_main                     []
% 23.19/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.19/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.19/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.19/3.49  --sup_input_bw                          []
% 23.19/3.49  
% 23.19/3.49  ------ Combination Options
% 23.19/3.49  
% 23.19/3.49  --comb_res_mult                         3
% 23.19/3.49  --comb_sup_mult                         2
% 23.19/3.49  --comb_inst_mult                        10
% 23.19/3.49  
% 23.19/3.49  ------ Debug Options
% 23.19/3.49  
% 23.19/3.49  --dbg_backtrace                         false
% 23.19/3.49  --dbg_dump_prop_clauses                 false
% 23.19/3.49  --dbg_dump_prop_clauses_file            -
% 23.19/3.49  --dbg_out_stat                          false
% 23.19/3.49  ------ Parsing...
% 23.19/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.19/3.49  
% 23.19/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.19/3.49  
% 23.19/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.19/3.49  
% 23.19/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.19/3.49  ------ Proving...
% 23.19/3.49  ------ Problem Properties 
% 23.19/3.49  
% 23.19/3.49  
% 23.19/3.49  clauses                                 31
% 23.19/3.49  conjectures                             3
% 23.19/3.49  EPR                                     5
% 23.19/3.49  Horn                                    24
% 23.19/3.49  unary                                   17
% 23.19/3.49  binary                                  6
% 23.19/3.49  lits                                    54
% 23.19/3.49  lits eq                                 30
% 23.19/3.49  fd_pure                                 0
% 23.19/3.49  fd_pseudo                               0
% 23.19/3.49  fd_cond                                 1
% 23.19/3.49  fd_pseudo_cond                          6
% 23.19/3.49  AC symbols                              0
% 23.19/3.49  
% 23.19/3.49  ------ Schedule dynamic 5 is on 
% 23.19/3.49  
% 23.19/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.19/3.49  
% 23.19/3.49  
% 23.19/3.49  ------ 
% 23.19/3.49  Current options:
% 23.19/3.49  ------ 
% 23.19/3.49  
% 23.19/3.49  ------ Input Options
% 23.19/3.49  
% 23.19/3.49  --out_options                           all
% 23.19/3.49  --tptp_safe_out                         true
% 23.19/3.49  --problem_path                          ""
% 23.19/3.49  --include_path                          ""
% 23.19/3.49  --clausifier                            res/vclausify_rel
% 23.19/3.49  --clausifier_options                    ""
% 23.19/3.49  --stdin                                 false
% 23.19/3.49  --stats_out                             all
% 23.19/3.49  
% 23.19/3.49  ------ General Options
% 23.19/3.49  
% 23.19/3.49  --fof                                   false
% 23.19/3.49  --time_out_real                         305.
% 23.19/3.49  --time_out_virtual                      -1.
% 23.19/3.49  --symbol_type_check                     false
% 23.19/3.49  --clausify_out                          false
% 23.19/3.49  --sig_cnt_out                           false
% 23.19/3.49  --trig_cnt_out                          false
% 23.19/3.49  --trig_cnt_out_tolerance                1.
% 23.19/3.49  --trig_cnt_out_sk_spl                   false
% 23.19/3.49  --abstr_cl_out                          false
% 23.19/3.49  
% 23.19/3.49  ------ Global Options
% 23.19/3.49  
% 23.19/3.49  --schedule                              default
% 23.19/3.49  --add_important_lit                     false
% 23.19/3.49  --prop_solver_per_cl                    1000
% 23.19/3.49  --min_unsat_core                        false
% 23.19/3.49  --soft_assumptions                      false
% 23.19/3.49  --soft_lemma_size                       3
% 23.19/3.49  --prop_impl_unit_size                   0
% 23.19/3.49  --prop_impl_unit                        []
% 23.19/3.49  --share_sel_clauses                     true
% 23.19/3.49  --reset_solvers                         false
% 23.19/3.49  --bc_imp_inh                            [conj_cone]
% 23.19/3.49  --conj_cone_tolerance                   3.
% 23.19/3.49  --extra_neg_conj                        none
% 23.19/3.49  --large_theory_mode                     true
% 23.19/3.49  --prolific_symb_bound                   200
% 23.19/3.49  --lt_threshold                          2000
% 23.19/3.49  --clause_weak_htbl                      true
% 23.19/3.49  --gc_record_bc_elim                     false
% 23.19/3.49  
% 23.19/3.49  ------ Preprocessing Options
% 23.19/3.49  
% 23.19/3.49  --preprocessing_flag                    true
% 23.19/3.49  --time_out_prep_mult                    0.1
% 23.19/3.49  --splitting_mode                        input
% 23.19/3.49  --splitting_grd                         true
% 23.19/3.49  --splitting_cvd                         false
% 23.19/3.49  --splitting_cvd_svl                     false
% 23.19/3.49  --splitting_nvd                         32
% 23.19/3.49  --sub_typing                            true
% 23.19/3.49  --prep_gs_sim                           true
% 23.19/3.49  --prep_unflatten                        true
% 23.19/3.49  --prep_res_sim                          true
% 23.19/3.49  --prep_upred                            true
% 23.19/3.49  --prep_sem_filter                       exhaustive
% 23.19/3.49  --prep_sem_filter_out                   false
% 23.19/3.49  --pred_elim                             true
% 23.19/3.49  --res_sim_input                         true
% 23.19/3.49  --eq_ax_congr_red                       true
% 23.19/3.49  --pure_diseq_elim                       true
% 23.19/3.49  --brand_transform                       false
% 23.19/3.49  --non_eq_to_eq                          false
% 23.19/3.49  --prep_def_merge                        true
% 23.19/3.49  --prep_def_merge_prop_impl              false
% 23.19/3.49  --prep_def_merge_mbd                    true
% 23.19/3.49  --prep_def_merge_tr_red                 false
% 23.19/3.49  --prep_def_merge_tr_cl                  false
% 23.19/3.49  --smt_preprocessing                     true
% 23.19/3.49  --smt_ac_axioms                         fast
% 23.19/3.49  --preprocessed_out                      false
% 23.19/3.49  --preprocessed_stats                    false
% 23.19/3.49  
% 23.19/3.49  ------ Abstraction refinement Options
% 23.19/3.49  
% 23.19/3.49  --abstr_ref                             []
% 23.19/3.49  --abstr_ref_prep                        false
% 23.19/3.49  --abstr_ref_until_sat                   false
% 23.19/3.49  --abstr_ref_sig_restrict                funpre
% 23.19/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.19/3.49  --abstr_ref_under                       []
% 23.19/3.49  
% 23.19/3.49  ------ SAT Options
% 23.19/3.49  
% 23.19/3.49  --sat_mode                              false
% 23.19/3.49  --sat_fm_restart_options                ""
% 23.19/3.49  --sat_gr_def                            false
% 23.19/3.49  --sat_epr_types                         true
% 23.19/3.49  --sat_non_cyclic_types                  false
% 23.19/3.49  --sat_finite_models                     false
% 23.19/3.49  --sat_fm_lemmas                         false
% 23.19/3.49  --sat_fm_prep                           false
% 23.19/3.49  --sat_fm_uc_incr                        true
% 23.19/3.49  --sat_out_model                         small
% 23.19/3.49  --sat_out_clauses                       false
% 23.19/3.49  
% 23.19/3.49  ------ QBF Options
% 23.19/3.49  
% 23.19/3.49  --qbf_mode                              false
% 23.19/3.49  --qbf_elim_univ                         false
% 23.19/3.49  --qbf_dom_inst                          none
% 23.19/3.49  --qbf_dom_pre_inst                      false
% 23.19/3.49  --qbf_sk_in                             false
% 23.19/3.49  --qbf_pred_elim                         true
% 23.19/3.49  --qbf_split                             512
% 23.19/3.49  
% 23.19/3.49  ------ BMC1 Options
% 23.19/3.49  
% 23.19/3.49  --bmc1_incremental                      false
% 23.19/3.49  --bmc1_axioms                           reachable_all
% 23.19/3.49  --bmc1_min_bound                        0
% 23.19/3.49  --bmc1_max_bound                        -1
% 23.19/3.49  --bmc1_max_bound_default                -1
% 23.19/3.49  --bmc1_symbol_reachability              true
% 23.19/3.49  --bmc1_property_lemmas                  false
% 23.19/3.49  --bmc1_k_induction                      false
% 23.19/3.49  --bmc1_non_equiv_states                 false
% 23.19/3.49  --bmc1_deadlock                         false
% 23.19/3.49  --bmc1_ucm                              false
% 23.19/3.49  --bmc1_add_unsat_core                   none
% 23.19/3.49  --bmc1_unsat_core_children              false
% 23.19/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.19/3.49  --bmc1_out_stat                         full
% 23.19/3.49  --bmc1_ground_init                      false
% 23.19/3.49  --bmc1_pre_inst_next_state              false
% 23.19/3.49  --bmc1_pre_inst_state                   false
% 23.19/3.49  --bmc1_pre_inst_reach_state             false
% 23.19/3.49  --bmc1_out_unsat_core                   false
% 23.19/3.49  --bmc1_aig_witness_out                  false
% 23.19/3.49  --bmc1_verbose                          false
% 23.19/3.49  --bmc1_dump_clauses_tptp                false
% 23.19/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.19/3.49  --bmc1_dump_file                        -
% 23.19/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.19/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.19/3.49  --bmc1_ucm_extend_mode                  1
% 23.19/3.49  --bmc1_ucm_init_mode                    2
% 23.19/3.49  --bmc1_ucm_cone_mode                    none
% 23.19/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.19/3.49  --bmc1_ucm_relax_model                  4
% 23.19/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.19/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.19/3.49  --bmc1_ucm_layered_model                none
% 23.19/3.49  --bmc1_ucm_max_lemma_size               10
% 23.19/3.49  
% 23.19/3.49  ------ AIG Options
% 23.19/3.49  
% 23.19/3.49  --aig_mode                              false
% 23.19/3.49  
% 23.19/3.49  ------ Instantiation Options
% 23.19/3.49  
% 23.19/3.49  --instantiation_flag                    true
% 23.19/3.49  --inst_sos_flag                         true
% 23.19/3.49  --inst_sos_phase                        true
% 23.19/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.19/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.19/3.49  --inst_lit_sel_side                     none
% 23.19/3.49  --inst_solver_per_active                1400
% 23.19/3.49  --inst_solver_calls_frac                1.
% 23.19/3.49  --inst_passive_queue_type               priority_queues
% 23.19/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.19/3.49  --inst_passive_queues_freq              [25;2]
% 23.19/3.49  --inst_dismatching                      true
% 23.19/3.49  --inst_eager_unprocessed_to_passive     true
% 23.19/3.49  --inst_prop_sim_given                   true
% 23.19/3.49  --inst_prop_sim_new                     false
% 23.19/3.49  --inst_subs_new                         false
% 23.19/3.49  --inst_eq_res_simp                      false
% 23.19/3.49  --inst_subs_given                       false
% 23.19/3.49  --inst_orphan_elimination               true
% 23.19/3.49  --inst_learning_loop_flag               true
% 23.19/3.49  --inst_learning_start                   3000
% 23.19/3.49  --inst_learning_factor                  2
% 23.19/3.49  --inst_start_prop_sim_after_learn       3
% 23.19/3.49  --inst_sel_renew                        solver
% 23.19/3.49  --inst_lit_activity_flag                true
% 23.19/3.49  --inst_restr_to_given                   false
% 23.19/3.49  --inst_activity_threshold               500
% 23.19/3.49  --inst_out_proof                        true
% 23.19/3.49  
% 23.19/3.49  ------ Resolution Options
% 23.19/3.49  
% 23.19/3.49  --resolution_flag                       false
% 23.19/3.49  --res_lit_sel                           adaptive
% 23.19/3.49  --res_lit_sel_side                      none
% 23.19/3.49  --res_ordering                          kbo
% 23.19/3.49  --res_to_prop_solver                    active
% 23.19/3.49  --res_prop_simpl_new                    false
% 23.19/3.49  --res_prop_simpl_given                  true
% 23.19/3.49  --res_passive_queue_type                priority_queues
% 23.19/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.19/3.49  --res_passive_queues_freq               [15;5]
% 23.19/3.49  --res_forward_subs                      full
% 23.19/3.49  --res_backward_subs                     full
% 23.19/3.49  --res_forward_subs_resolution           true
% 23.19/3.49  --res_backward_subs_resolution          true
% 23.19/3.49  --res_orphan_elimination                true
% 23.19/3.49  --res_time_limit                        2.
% 23.19/3.49  --res_out_proof                         true
% 23.19/3.49  
% 23.19/3.49  ------ Superposition Options
% 23.19/3.49  
% 23.19/3.49  --superposition_flag                    true
% 23.19/3.49  --sup_passive_queue_type                priority_queues
% 23.19/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.19/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.19/3.49  --demod_completeness_check              fast
% 23.19/3.49  --demod_use_ground                      true
% 23.19/3.49  --sup_to_prop_solver                    passive
% 23.19/3.49  --sup_prop_simpl_new                    true
% 23.19/3.49  --sup_prop_simpl_given                  true
% 23.19/3.49  --sup_fun_splitting                     true
% 23.19/3.49  --sup_smt_interval                      50000
% 23.19/3.49  
% 23.19/3.49  ------ Superposition Simplification Setup
% 23.19/3.49  
% 23.19/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.19/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.19/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.19/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.19/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.19/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.19/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.19/3.49  --sup_immed_triv                        [TrivRules]
% 23.19/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.19/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.19/3.49  --sup_immed_bw_main                     []
% 23.19/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.19/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.19/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.19/3.49  --sup_input_bw                          []
% 23.19/3.49  
% 23.19/3.49  ------ Combination Options
% 23.19/3.49  
% 23.19/3.49  --comb_res_mult                         3
% 23.19/3.49  --comb_sup_mult                         2
% 23.19/3.49  --comb_inst_mult                        10
% 23.19/3.49  
% 23.19/3.49  ------ Debug Options
% 23.19/3.49  
% 23.19/3.49  --dbg_backtrace                         false
% 23.19/3.49  --dbg_dump_prop_clauses                 false
% 23.19/3.49  --dbg_dump_prop_clauses_file            -
% 23.19/3.49  --dbg_out_stat                          false
% 23.19/3.49  
% 23.19/3.49  
% 23.19/3.49  
% 23.19/3.49  
% 23.19/3.49  ------ Proving...
% 23.19/3.49  
% 23.19/3.49  
% 23.19/3.49  % SZS status Theorem for theBenchmark.p
% 23.19/3.49  
% 23.19/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.19/3.49  
% 23.19/3.49  fof(f27,conjecture,(
% 23.19/3.49    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f28,negated_conjecture,(
% 23.19/3.49    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 23.19/3.49    inference(negated_conjecture,[],[f27])).
% 23.19/3.49  
% 23.19/3.49  fof(f36,plain,(
% 23.19/3.49    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 23.19/3.49    inference(ennf_transformation,[],[f28])).
% 23.19/3.49  
% 23.19/3.49  fof(f51,plain,(
% 23.19/3.49    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 23.19/3.49    introduced(choice_axiom,[])).
% 23.19/3.49  
% 23.19/3.49  fof(f52,plain,(
% 23.19/3.49    sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 23.19/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f36,f51])).
% 23.19/3.49  
% 23.19/3.49  fof(f91,plain,(
% 23.19/3.49    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 23.19/3.49    inference(cnf_transformation,[],[f52])).
% 23.19/3.49  
% 23.19/3.49  fof(f18,axiom,(
% 23.19/3.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f78,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f18])).
% 23.19/3.49  
% 23.19/3.49  fof(f19,axiom,(
% 23.19/3.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f79,plain,(
% 23.19/3.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f19])).
% 23.19/3.49  
% 23.19/3.49  fof(f95,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.19/3.49    inference(definition_unfolding,[],[f78,f79])).
% 23.19/3.49  
% 23.19/3.49  fof(f116,plain,(
% 23.19/3.49    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))),
% 23.19/3.49    inference(definition_unfolding,[],[f91,f95,f95])).
% 23.19/3.49  
% 23.19/3.49  fof(f10,axiom,(
% 23.19/3.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f35,plain,(
% 23.19/3.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.19/3.49    inference(ennf_transformation,[],[f10])).
% 23.19/3.49  
% 23.19/3.49  fof(f65,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f35])).
% 23.19/3.49  
% 23.19/3.49  fof(f1,axiom,(
% 23.19/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f53,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f1])).
% 23.19/3.49  
% 23.19/3.49  fof(f14,axiom,(
% 23.19/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f69,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.19/3.49    inference(cnf_transformation,[],[f14])).
% 23.19/3.49  
% 23.19/3.49  fof(f7,axiom,(
% 23.19/3.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f62,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.19/3.49    inference(cnf_transformation,[],[f7])).
% 23.19/3.49  
% 23.19/3.49  fof(f94,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 23.19/3.49    inference(definition_unfolding,[],[f69,f62])).
% 23.19/3.49  
% 23.19/3.49  fof(f101,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 23.19/3.49    inference(definition_unfolding,[],[f53,f94,f94])).
% 23.19/3.49  
% 23.19/3.49  fof(f12,axiom,(
% 23.19/3.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f67,plain,(
% 23.19/3.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.19/3.49    inference(cnf_transformation,[],[f12])).
% 23.19/3.49  
% 23.19/3.49  fof(f16,axiom,(
% 23.19/3.49    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f76,plain,(
% 23.19/3.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f16])).
% 23.19/3.49  
% 23.19/3.49  fof(f100,plain,(
% 23.19/3.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X3),k3_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 23.19/3.49    inference(definition_unfolding,[],[f76,f94,f95,f95])).
% 23.19/3.49  
% 23.19/3.49  fof(f5,axiom,(
% 23.19/3.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f32,plain,(
% 23.19/3.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 23.19/3.49    inference(ennf_transformation,[],[f5])).
% 23.19/3.49  
% 23.19/3.49  fof(f39,plain,(
% 23.19/3.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 23.19/3.49    introduced(choice_axiom,[])).
% 23.19/3.49  
% 23.19/3.49  fof(f40,plain,(
% 23.19/3.49    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 23.19/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f39])).
% 23.19/3.49  
% 23.19/3.49  fof(f58,plain,(
% 23.19/3.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 23.19/3.49    inference(cnf_transformation,[],[f40])).
% 23.19/3.49  
% 23.19/3.49  fof(f4,axiom,(
% 23.19/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f30,plain,(
% 23.19/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 23.19/3.49    inference(rectify,[],[f4])).
% 23.19/3.49  
% 23.19/3.49  fof(f31,plain,(
% 23.19/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 23.19/3.49    inference(ennf_transformation,[],[f30])).
% 23.19/3.49  
% 23.19/3.49  fof(f37,plain,(
% 23.19/3.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 23.19/3.49    introduced(choice_axiom,[])).
% 23.19/3.49  
% 23.19/3.49  fof(f38,plain,(
% 23.19/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 23.19/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f37])).
% 23.19/3.49  
% 23.19/3.49  fof(f57,plain,(
% 23.19/3.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 23.19/3.49    inference(cnf_transformation,[],[f38])).
% 23.19/3.49  
% 23.19/3.49  fof(f13,axiom,(
% 23.19/3.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f68,plain,(
% 23.19/3.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f13])).
% 23.19/3.49  
% 23.19/3.49  fof(f11,axiom,(
% 23.19/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f66,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.19/3.49    inference(cnf_transformation,[],[f11])).
% 23.19/3.49  
% 23.19/3.49  fof(f99,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 23.19/3.49    inference(definition_unfolding,[],[f66,f62,f62])).
% 23.19/3.49  
% 23.19/3.49  fof(f3,axiom,(
% 23.19/3.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f29,plain,(
% 23.19/3.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 23.19/3.49    inference(rectify,[],[f3])).
% 23.19/3.49  
% 23.19/3.49  fof(f55,plain,(
% 23.19/3.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 23.19/3.49    inference(cnf_transformation,[],[f29])).
% 23.19/3.49  
% 23.19/3.49  fof(f25,axiom,(
% 23.19/3.49    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f88,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f25])).
% 23.19/3.49  
% 23.19/3.49  fof(f17,axiom,(
% 23.19/3.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f77,plain,(
% 23.19/3.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f17])).
% 23.19/3.49  
% 23.19/3.49  fof(f96,plain,(
% 23.19/3.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 23.19/3.49    inference(definition_unfolding,[],[f77,f95])).
% 23.19/3.49  
% 23.19/3.49  fof(f113,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(X0,X0,X0,X0)) )),
% 23.19/3.49    inference(definition_unfolding,[],[f88,f96,f95,f96])).
% 23.19/3.49  
% 23.19/3.49  fof(f2,axiom,(
% 23.19/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f54,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f2])).
% 23.19/3.49  
% 23.19/3.49  fof(f8,axiom,(
% 23.19/3.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f63,plain,(
% 23.19/3.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f8])).
% 23.19/3.49  
% 23.19/3.49  fof(f9,axiom,(
% 23.19/3.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f33,plain,(
% 23.19/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 23.19/3.49    inference(ennf_transformation,[],[f9])).
% 23.19/3.49  
% 23.19/3.49  fof(f34,plain,(
% 23.19/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 23.19/3.49    inference(flattening,[],[f33])).
% 23.19/3.49  
% 23.19/3.49  fof(f64,plain,(
% 23.19/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f34])).
% 23.19/3.49  
% 23.19/3.49  fof(f24,axiom,(
% 23.19/3.49    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f48,plain,(
% 23.19/3.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 23.19/3.49    inference(nnf_transformation,[],[f24])).
% 23.19/3.49  
% 23.19/3.49  fof(f49,plain,(
% 23.19/3.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 23.19/3.49    inference(flattening,[],[f48])).
% 23.19/3.49  
% 23.19/3.49  fof(f87,plain,(
% 23.19/3.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f49])).
% 23.19/3.49  
% 23.19/3.49  fof(f109,plain,(
% 23.19/3.49    ( ! [X2,X0,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) = k2_enumset1(X0,X0,X0,X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 23.19/3.49    inference(definition_unfolding,[],[f87,f62,f95,f96])).
% 23.19/3.49  
% 23.19/3.49  fof(f124,plain,(
% 23.19/3.49    ( ! [X2,X1] : (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k2_enumset1(X1,X1,X1,X1) | r2_hidden(X1,X2)) )),
% 23.19/3.49    inference(equality_resolution,[],[f109])).
% 23.19/3.49  
% 23.19/3.49  fof(f15,axiom,(
% 23.19/3.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f43,plain,(
% 23.19/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.19/3.49    inference(nnf_transformation,[],[f15])).
% 23.19/3.49  
% 23.19/3.49  fof(f44,plain,(
% 23.19/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.19/3.49    inference(flattening,[],[f43])).
% 23.19/3.49  
% 23.19/3.49  fof(f45,plain,(
% 23.19/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.19/3.49    inference(rectify,[],[f44])).
% 23.19/3.49  
% 23.19/3.49  fof(f46,plain,(
% 23.19/3.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 23.19/3.49    introduced(choice_axiom,[])).
% 23.19/3.49  
% 23.19/3.49  fof(f47,plain,(
% 23.19/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.19/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 23.19/3.49  
% 23.19/3.49  fof(f70,plain,(
% 23.19/3.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 23.19/3.49    inference(cnf_transformation,[],[f47])).
% 23.19/3.49  
% 23.19/3.49  fof(f107,plain,(
% 23.19/3.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 23.19/3.49    inference(definition_unfolding,[],[f70,f95])).
% 23.19/3.49  
% 23.19/3.49  fof(f123,plain,(
% 23.19/3.49    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 23.19/3.49    inference(equality_resolution,[],[f107])).
% 23.19/3.49  
% 23.19/3.49  fof(f26,axiom,(
% 23.19/3.49    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 23.19/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.19/3.49  
% 23.19/3.49  fof(f50,plain,(
% 23.19/3.49    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 23.19/3.49    inference(nnf_transformation,[],[f26])).
% 23.19/3.49  
% 23.19/3.49  fof(f89,plain,(
% 23.19/3.49    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 23.19/3.49    inference(cnf_transformation,[],[f50])).
% 23.19/3.49  
% 23.19/3.49  fof(f115,plain,(
% 23.19/3.49    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) != k2_enumset1(X0,X0,X0,X0)) )),
% 23.19/3.49    inference(definition_unfolding,[],[f89,f62,f96,f96,f96])).
% 23.19/3.49  
% 23.19/3.49  fof(f125,plain,(
% 23.19/3.49    ( ! [X1] : (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) != k2_enumset1(X1,X1,X1,X1)) )),
% 23.19/3.49    inference(equality_resolution,[],[f115])).
% 23.19/3.49  
% 23.19/3.49  fof(f90,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 23.19/3.49    inference(cnf_transformation,[],[f50])).
% 23.19/3.49  
% 23.19/3.49  fof(f114,plain,(
% 23.19/3.49    ( ! [X0,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(X0,X0,X0,X0) | X0 = X1) )),
% 23.19/3.49    inference(definition_unfolding,[],[f90,f62,f96,f96,f96])).
% 23.19/3.49  
% 23.19/3.49  fof(f93,plain,(
% 23.19/3.49    sK3 != sK6),
% 23.19/3.49    inference(cnf_transformation,[],[f52])).
% 23.19/3.49  
% 23.19/3.49  fof(f92,plain,(
% 23.19/3.49    sK3 != sK5),
% 23.19/3.49    inference(cnf_transformation,[],[f52])).
% 23.19/3.49  
% 23.19/3.49  cnf(c_32,negated_conjecture,
% 23.19/3.49      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
% 23.19/3.49      inference(cnf_transformation,[],[f116]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_703,plain,
% 23.19/3.49      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
% 23.19/3.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_13,plain,
% 23.19/3.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.19/3.49      inference(cnf_transformation,[],[f65]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_714,plain,
% 23.19/3.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.19/3.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2750,plain,
% 23.19/3.49      ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_703,c_714]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2,plain,
% 23.19/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 23.19/3.49      inference(cnf_transformation,[],[f101]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2849,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4))) ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_2750,c_2]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_14,plain,
% 23.19/3.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.19/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_1,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X3),k3_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3) ),
% 23.19/3.49      inference(cnf_transformation,[],[f100]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2178,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X3),k3_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X2,X3,X0,X1) ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_7,plain,
% 23.19/3.49      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 23.19/3.49      inference(cnf_transformation,[],[f58]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_719,plain,
% 23.19/3.49      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 23.19/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_5,plain,
% 23.19/3.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 23.19/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_15,plain,
% 23.19/3.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 23.19/3.49      inference(cnf_transformation,[],[f68]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_264,plain,
% 23.19/3.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 23.19/3.49      | X3 != X1
% 23.19/3.49      | k1_xboole_0 != X2 ),
% 23.19/3.49      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_265,plain,
% 23.19/3.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 23.19/3.49      inference(unflattening,[status(thm)],[c_264]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_701,plain,
% 23.19/3.49      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 23.19/3.49      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2273,plain,
% 23.19/3.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_719,c_701]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_0,plain,
% 23.19/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 23.19/3.49      inference(cnf_transformation,[],[f99]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2420,plain,
% 23.19/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_2273,c_0]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2430,plain,
% 23.19/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 23.19/3.49      inference(demodulation,[status(thm)],[c_2420,c_2273]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_4,plain,
% 23.19/3.49      ( k3_xboole_0(X0,X0) = X0 ),
% 23.19/3.49      inference(cnf_transformation,[],[f55]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2431,plain,
% 23.19/3.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.19/3.49      inference(light_normalisation,[status(thm)],[c_2430,c_4,c_14]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2852,plain,
% 23.19/3.49      ( k2_enumset1(sK5,sK6,sK3,sK4) = k2_enumset1(sK5,sK5,sK5,sK6) ),
% 23.19/3.49      inference(demodulation,[status(thm)],[c_2849,c_14,c_2178,c_2431]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_3022,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k3_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X0,X1,sK5,sK6) ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_2852,c_1]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2862,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k5_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k3_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4)))) = k5_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4))) ),
% 23.19/3.49      inference(light_normalisation,[status(thm)],[c_2849,c_2852]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_2863,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k5_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k3_xboole_0(k2_enumset1(sK5,sK6,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4)))) = k2_enumset1(sK5,sK6,sK3,sK4) ),
% 23.19/3.49      inference(demodulation,[status(thm)],[c_2862,c_14,c_2431]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_5150,plain,
% 23.19/3.49      ( k2_enumset1(sK3,sK4,sK5,sK6) = k2_enumset1(sK5,sK6,sK3,sK4) ),
% 23.19/3.49      inference(demodulation,[status(thm)],[c_3022,c_2863]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_3016,plain,
% 23.19/3.49      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK6,sK3,sK4)) = iProver_top ),
% 23.19/3.49      inference(demodulation,[status(thm)],[c_2852,c_703]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_6537,plain,
% 23.19/3.49      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK4,sK5,sK6)) = iProver_top ),
% 23.19/3.49      inference(demodulation,[status(thm)],[c_5150,c_3016]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_27,plain,
% 23.19/3.49      ( k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(X0,X0,X0,X0) ),
% 23.19/3.49      inference(cnf_transformation,[],[f113]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_3,plain,
% 23.19/3.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.19/3.49      inference(cnf_transformation,[],[f54]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_11,plain,
% 23.19/3.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 23.19/3.49      inference(cnf_transformation,[],[f63]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_716,plain,
% 23.19/3.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 23.19/3.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_1186,plain,
% 23.19/3.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_3,c_716]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_1664,plain,
% 23.19/3.49      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_27,c_1186]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_12,plain,
% 23.19/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 23.19/3.49      inference(cnf_transformation,[],[f64]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_715,plain,
% 23.19/3.49      ( r1_tarski(X0,X1) != iProver_top
% 23.19/3.49      | r1_tarski(X1,X2) != iProver_top
% 23.19/3.49      | r1_tarski(X0,X2) = iProver_top ),
% 23.19/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_8110,plain,
% 23.19/3.49      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) != iProver_top
% 23.19/3.49      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X2) = iProver_top ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_1664,c_715]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_64579,plain,
% 23.19/3.49      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK4,sK5,sK6)) = iProver_top ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_6537,c_8110]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_67654,plain,
% 23.19/3.49      ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK4,sK5,sK6)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_64579,c_714]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_23,plain,
% 23.19/3.49      ( r2_hidden(X0,X1)
% 23.19/3.49      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
% 23.19/3.49      inference(cnf_transformation,[],[f124]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_707,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
% 23.19/3.49      | r2_hidden(X0,X1) = iProver_top ),
% 23.19/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_21,plain,
% 23.19/3.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 23.19/3.49      inference(cnf_transformation,[],[f123]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_708,plain,
% 23.19/3.49      ( X0 = X1
% 23.19/3.49      | X0 = X2
% 23.19/3.49      | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
% 23.19/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_3027,plain,
% 23.19/3.49      ( sK5 = X0
% 23.19/3.49      | sK6 = X0
% 23.19/3.49      | r2_hidden(X0,k2_enumset1(sK5,sK6,sK3,sK4)) != iProver_top ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_2852,c_708]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_6229,plain,
% 23.19/3.49      ( sK5 = X0
% 23.19/3.49      | sK6 = X0
% 23.19/3.49      | r2_hidden(X0,k2_enumset1(sK3,sK4,sK5,sK6)) != iProver_top ),
% 23.19/3.49      inference(light_normalisation,[status(thm)],[c_3027,c_5150]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_6235,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK3,sK4,sK5,sK6))) = k2_enumset1(X0,X0,X0,X0)
% 23.19/3.49      | sK5 = X0
% 23.19/3.49      | sK6 = X0 ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_707,c_6229]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_67737,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK3,sK3,sK3)) = k2_enumset1(sK3,sK3,sK3,sK3)
% 23.19/3.49      | sK5 = sK3
% 23.19/3.49      | sK6 = sK3 ),
% 23.19/3.49      inference(superposition,[status(thm)],[c_67654,c_6235]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_68096,plain,
% 23.19/3.49      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 23.19/3.49      | sK5 = sK3
% 23.19/3.49      | sK6 = sK3 ),
% 23.19/3.49      inference(demodulation,[status(thm)],[c_67737,c_2431]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_29,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) != k2_enumset1(X0,X0,X0,X0) ),
% 23.19/3.49      inference(cnf_transformation,[],[f125]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_720,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 23.19/3.49      inference(demodulation,[status(thm)],[c_29,c_27]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_10531,plain,
% 23.19/3.49      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 23.19/3.49      inference(demodulation,[status(thm)],[c_720,c_2431]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_10532,plain,
% 23.19/3.49      ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0 ),
% 23.19/3.49      inference(instantiation,[status(thm)],[c_10531]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_407,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_771,plain,
% 23.19/3.49      ( sK5 != X0 | sK3 != X0 | sK3 = sK5 ),
% 23.19/3.49      inference(instantiation,[status(thm)],[c_407]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_772,plain,
% 23.19/3.49      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 23.19/3.49      inference(instantiation,[status(thm)],[c_771]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_754,plain,
% 23.19/3.49      ( sK6 != X0 | sK3 != X0 | sK3 = sK6 ),
% 23.19/3.49      inference(instantiation,[status(thm)],[c_407]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_755,plain,
% 23.19/3.49      ( sK6 != sK3 | sK3 = sK6 | sK3 != sK3 ),
% 23.19/3.49      inference(instantiation,[status(thm)],[c_754]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_28,plain,
% 23.19/3.49      ( X0 = X1
% 23.19/3.49      | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X1,X1,X1,X1) ),
% 23.19/3.49      inference(cnf_transformation,[],[f114]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_35,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK3,sK3,sK3,sK3)
% 23.19/3.49      | sK3 = sK3 ),
% 23.19/3.49      inference(instantiation,[status(thm)],[c_28]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_34,plain,
% 23.19/3.49      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK3,sK3,sK3,sK3))) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 23.19/3.49      inference(instantiation,[status(thm)],[c_29]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_30,negated_conjecture,
% 23.19/3.49      ( sK3 != sK6 ),
% 23.19/3.49      inference(cnf_transformation,[],[f93]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(c_31,negated_conjecture,
% 23.19/3.49      ( sK3 != sK5 ),
% 23.19/3.49      inference(cnf_transformation,[],[f92]) ).
% 23.19/3.49  
% 23.19/3.49  cnf(contradiction,plain,
% 23.19/3.49      ( $false ),
% 23.19/3.49      inference(minisat,
% 23.19/3.49                [status(thm)],
% 23.19/3.49                [c_68096,c_10532,c_772,c_755,c_35,c_34,c_30,c_31]) ).
% 23.19/3.49  
% 23.19/3.49  
% 23.19/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.19/3.49  
% 23.19/3.49  ------                               Statistics
% 23.19/3.49  
% 23.19/3.49  ------ General
% 23.19/3.49  
% 23.19/3.49  abstr_ref_over_cycles:                  0
% 23.19/3.49  abstr_ref_under_cycles:                 0
% 23.19/3.49  gc_basic_clause_elim:                   0
% 23.19/3.49  forced_gc_time:                         0
% 23.19/3.49  parsing_time:                           0.014
% 23.19/3.49  unif_index_cands_time:                  0.
% 23.19/3.49  unif_index_add_time:                    0.
% 23.19/3.49  orderings_time:                         0.
% 23.19/3.49  out_proof_time:                         0.014
% 23.19/3.49  total_time:                             2.644
% 23.19/3.49  num_of_symbols:                         46
% 23.19/3.49  num_of_terms:                           65890
% 23.19/3.49  
% 23.19/3.49  ------ Preprocessing
% 23.19/3.49  
% 23.19/3.49  num_of_splits:                          0
% 23.19/3.49  num_of_split_atoms:                     0
% 23.19/3.49  num_of_reused_defs:                     0
% 23.19/3.49  num_eq_ax_congr_red:                    43
% 23.19/3.49  num_of_sem_filtered_clauses:            1
% 23.19/3.49  num_of_subtypes:                        0
% 23.19/3.49  monotx_restored_types:                  0
% 23.19/3.49  sat_num_of_epr_types:                   0
% 23.19/3.49  sat_num_of_non_cyclic_types:            0
% 23.19/3.49  sat_guarded_non_collapsed_types:        0
% 23.19/3.49  num_pure_diseq_elim:                    0
% 23.19/3.49  simp_replaced_by:                       0
% 23.19/3.49  res_preprocessed:                       140
% 23.19/3.49  prep_upred:                             0
% 23.19/3.49  prep_unflattend:                        4
% 23.19/3.49  smt_new_axioms:                         0
% 23.19/3.49  pred_elim_cands:                        2
% 23.19/3.49  pred_elim:                              1
% 23.19/3.49  pred_elim_cl:                           1
% 23.19/3.49  pred_elim_cycles:                       3
% 23.19/3.49  merged_defs:                            0
% 23.19/3.49  merged_defs_ncl:                        0
% 23.19/3.49  bin_hyper_res:                          0
% 23.19/3.49  prep_cycles:                            4
% 23.19/3.49  pred_elim_time:                         0.002
% 23.19/3.49  splitting_time:                         0.
% 23.19/3.49  sem_filter_time:                        0.
% 23.19/3.49  monotx_time:                            0.001
% 23.19/3.49  subtype_inf_time:                       0.
% 23.19/3.49  
% 23.19/3.49  ------ Problem properties
% 23.19/3.49  
% 23.19/3.49  clauses:                                31
% 23.19/3.49  conjectures:                            3
% 23.19/3.49  epr:                                    5
% 23.19/3.49  horn:                                   24
% 23.19/3.49  ground:                                 3
% 23.19/3.49  unary:                                  17
% 23.19/3.49  binary:                                 6
% 23.19/3.49  lits:                                   54
% 23.19/3.49  lits_eq:                                30
% 23.19/3.49  fd_pure:                                0
% 23.19/3.49  fd_pseudo:                              0
% 23.19/3.49  fd_cond:                                1
% 23.19/3.49  fd_pseudo_cond:                         6
% 23.19/3.49  ac_symbols:                             0
% 23.19/3.49  
% 23.19/3.49  ------ Propositional Solver
% 23.19/3.49  
% 23.19/3.49  prop_solver_calls:                      32
% 23.19/3.49  prop_fast_solver_calls:                 2352
% 23.19/3.49  smt_solver_calls:                       0
% 23.19/3.49  smt_fast_solver_calls:                  0
% 23.19/3.49  prop_num_of_clauses:                    23487
% 23.19/3.49  prop_preprocess_simplified:             40093
% 23.19/3.49  prop_fo_subsumed:                       59
% 23.19/3.49  prop_solver_time:                       0.
% 23.19/3.49  smt_solver_time:                        0.
% 23.19/3.49  smt_fast_solver_time:                   0.
% 23.19/3.49  prop_fast_solver_time:                  0.
% 23.19/3.49  prop_unsat_core_time:                   0.002
% 23.19/3.49  
% 23.19/3.49  ------ QBF
% 23.19/3.49  
% 23.19/3.49  qbf_q_res:                              0
% 23.19/3.49  qbf_num_tautologies:                    0
% 23.19/3.49  qbf_prep_cycles:                        0
% 23.19/3.49  
% 23.19/3.49  ------ BMC1
% 23.19/3.49  
% 23.19/3.49  bmc1_current_bound:                     -1
% 23.19/3.49  bmc1_last_solved_bound:                 -1
% 23.19/3.49  bmc1_unsat_core_size:                   -1
% 23.19/3.49  bmc1_unsat_core_parents_size:           -1
% 23.19/3.49  bmc1_merge_next_fun:                    0
% 23.19/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.19/3.49  
% 23.19/3.49  ------ Instantiation
% 23.19/3.49  
% 23.19/3.49  inst_num_of_clauses:                    5452
% 23.19/3.49  inst_num_in_passive:                    1258
% 23.19/3.49  inst_num_in_active:                     1759
% 23.19/3.49  inst_num_in_unprocessed:                2436
% 23.19/3.49  inst_num_of_loops:                      2190
% 23.19/3.49  inst_num_of_learning_restarts:          0
% 23.19/3.49  inst_num_moves_active_passive:          431
% 23.19/3.49  inst_lit_activity:                      0
% 23.19/3.49  inst_lit_activity_moves:                1
% 23.19/3.49  inst_num_tautologies:                   0
% 23.19/3.49  inst_num_prop_implied:                  0
% 23.19/3.49  inst_num_existing_simplified:           0
% 23.19/3.49  inst_num_eq_res_simplified:             0
% 23.19/3.49  inst_num_child_elim:                    0
% 23.19/3.49  inst_num_of_dismatching_blockings:      9679
% 23.19/3.49  inst_num_of_non_proper_insts:           8066
% 23.19/3.49  inst_num_of_duplicates:                 0
% 23.19/3.49  inst_inst_num_from_inst_to_res:         0
% 23.19/3.49  inst_dismatching_checking_time:         0.
% 23.19/3.49  
% 23.19/3.49  ------ Resolution
% 23.19/3.49  
% 23.19/3.49  res_num_of_clauses:                     0
% 23.19/3.49  res_num_in_passive:                     0
% 23.19/3.49  res_num_in_active:                      0
% 23.19/3.49  res_num_of_loops:                       144
% 23.19/3.49  res_forward_subset_subsumed:            1198
% 23.19/3.49  res_backward_subset_subsumed:           20
% 23.19/3.49  res_forward_subsumed:                   0
% 23.19/3.49  res_backward_subsumed:                  0
% 23.19/3.49  res_forward_subsumption_resolution:     0
% 23.19/3.49  res_backward_subsumption_resolution:    0
% 23.19/3.49  res_clause_to_clause_subsumption:       83932
% 23.19/3.49  res_orphan_elimination:                 0
% 23.19/3.49  res_tautology_del:                      372
% 23.19/3.49  res_num_eq_res_simplified:              0
% 23.19/3.49  res_num_sel_changes:                    0
% 23.19/3.49  res_moves_from_active_to_pass:          0
% 23.19/3.49  
% 23.19/3.49  ------ Superposition
% 23.19/3.49  
% 23.19/3.49  sup_time_total:                         0.
% 23.19/3.49  sup_time_generating:                    0.
% 23.19/3.49  sup_time_sim_full:                      0.
% 23.19/3.49  sup_time_sim_immed:                     0.
% 23.19/3.49  
% 23.19/3.49  sup_num_of_clauses:                     4572
% 23.19/3.49  sup_num_in_active:                      381
% 23.19/3.49  sup_num_in_passive:                     4191
% 23.19/3.49  sup_num_of_loops:                       436
% 23.19/3.49  sup_fw_superposition:                   6472
% 23.19/3.49  sup_bw_superposition:                   11626
% 23.19/3.49  sup_immediate_simplified:               3503
% 23.19/3.49  sup_given_eliminated:                   5
% 23.19/3.49  comparisons_done:                       0
% 23.19/3.49  comparisons_avoided:                    1312
% 23.19/3.49  
% 23.19/3.49  ------ Simplifications
% 23.19/3.49  
% 23.19/3.49  
% 23.19/3.49  sim_fw_subset_subsumed:                 793
% 23.19/3.49  sim_bw_subset_subsumed:                 79
% 23.19/3.49  sim_fw_subsumed:                        678
% 23.19/3.49  sim_bw_subsumed:                        95
% 23.19/3.49  sim_fw_subsumption_res:                 0
% 23.19/3.49  sim_bw_subsumption_res:                 0
% 23.19/3.49  sim_tautology_del:                      53
% 23.19/3.49  sim_eq_tautology_del:                   1298
% 23.19/3.49  sim_eq_res_simp:                        14
% 23.19/3.49  sim_fw_demodulated:                     1669
% 23.19/3.49  sim_bw_demodulated:                     86
% 23.19/3.49  sim_light_normalised:                   847
% 23.19/3.49  sim_joinable_taut:                      0
% 23.19/3.49  sim_joinable_simp:                      0
% 23.19/3.49  sim_ac_normalised:                      0
% 23.19/3.49  sim_smt_subsumption:                    0
% 23.19/3.49  
%------------------------------------------------------------------------------
