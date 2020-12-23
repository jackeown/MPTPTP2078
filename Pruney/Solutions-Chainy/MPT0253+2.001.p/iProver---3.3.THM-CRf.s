%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:38 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 527 expanded)
%              Number of clauses        :   52 ( 103 expanded)
%              Number of leaves         :   20 ( 142 expanded)
%              Depth                    :   16
%              Number of atoms          :  364 (1101 expanded)
%              Number of equality atoms :  129 ( 535 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f86])).

fof(f97,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f75,f87,f87])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k2_tarski(sK4,sK6),sK5) != sK5
      & r2_hidden(sK6,sK5)
      & r2_hidden(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( k2_xboole_0(k2_tarski(sK4,sK6),sK5) != sK5
    & r2_hidden(sK6,sK5)
    & r2_hidden(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f47])).

fof(f83,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f82,f87])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f79,f87])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f96,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f74,f88,f88,f70])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f71,f88])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f85,plain,(
    k2_xboole_0(k2_tarski(sK4,sK6),sK5) != sK5 ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),sK5)) != sK5 ),
    inference(definition_unfolding,[],[f85,f88,f87])).

cnf(c_25,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_960,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_961,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_964,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_966,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2974,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_966])).

cnf(c_5359,plain,
    ( k3_xboole_0(k3_enumset1(sK6,sK6,sK6,sK6,X0),sK5) = k3_enumset1(sK6,sK6,sK6,sK6,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_2974])).

cnf(c_5534,plain,
    ( k3_xboole_0(k3_enumset1(sK6,sK6,sK6,sK6,sK4),sK5) = k3_enumset1(sK6,sK6,sK6,sK6,sK4) ),
    inference(superposition,[status(thm)],[c_960,c_5359])).

cnf(c_24,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6001,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k5_xboole_0(k3_enumset1(sK6,sK6,sK6,sK6,sK4),k3_enumset1(sK6,sK6,sK6,sK6,sK4)))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK6,sK6,sK6,sK6,sK4))) ),
    inference(superposition,[status(thm)],[c_5534,c_24])).

cnf(c_6980,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6)))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK6,sK6,sK6,sK6,sK4))) ),
    inference(superposition,[status(thm)],[c_25,c_6001])).

cnf(c_5360,plain,
    ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,X0),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_960,c_2974])).

cnf(c_6034,plain,
    ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK6),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,sK6) ),
    inference(superposition,[status(thm)],[c_961,c_5360])).

cnf(c_6344,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6)))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) ),
    inference(superposition,[status(thm)],[c_6034,c_24])).

cnf(c_6984,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK6,sK6,sK6,sK6,sK4))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) ),
    inference(light_normalisation,[status(thm)],[c_6980,c_6344])).

cnf(c_27369,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k5_xboole_0(k3_enumset1(sK6,sK6,sK6,sK6,sK4),k3_enumset1(sK6,sK6,sK6,sK6,sK4)))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) ),
    inference(demodulation,[status(thm)],[c_6984,c_6001])).

cnf(c_21,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_972,plain,
    ( X0 = X1
    | r2_hidden(sK2(X0,X1),X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_23,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_965,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2006,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_965,c_966])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_975,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3036,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_975])).

cnf(c_20,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_967,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2005,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_967,c_966])).

cnf(c_2127,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_25,c_21])).

cnf(c_2377,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2127,c_24])).

cnf(c_2378,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2377,c_2127])).

cnf(c_2526,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2005,c_2378])).

cnf(c_3037,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3036,c_2526])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_981,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2773,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_981])).

cnf(c_3195,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3037,c_2773])).

cnf(c_3201,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_972,c_3195])).

cnf(c_3035,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_975])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_974,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2799,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_974])).

cnf(c_3262,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3035,c_2799])).

cnf(c_8043,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3201,c_3262])).

cnf(c_27370,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) = sK5 ),
    inference(demodulation,[status(thm)],[c_27369,c_21,c_8043])).

cnf(c_29,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),sK5)) != sK5 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2124,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) != sK5 ),
    inference(demodulation,[status(thm)],[c_25,c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27370,c_2124])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.98/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.98/1.48  
% 7.98/1.48  ------  iProver source info
% 7.98/1.48  
% 7.98/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.98/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.98/1.48  git: non_committed_changes: false
% 7.98/1.48  git: last_make_outside_of_git: false
% 7.98/1.48  
% 7.98/1.48  ------ 
% 7.98/1.48  
% 7.98/1.48  ------ Input Options
% 7.98/1.48  
% 7.98/1.48  --out_options                           all
% 7.98/1.48  --tptp_safe_out                         true
% 7.98/1.48  --problem_path                          ""
% 7.98/1.48  --include_path                          ""
% 7.98/1.48  --clausifier                            res/vclausify_rel
% 7.98/1.48  --clausifier_options                    ""
% 7.98/1.48  --stdin                                 false
% 7.98/1.48  --stats_out                             all
% 7.98/1.48  
% 7.98/1.48  ------ General Options
% 7.98/1.48  
% 7.98/1.48  --fof                                   false
% 7.98/1.48  --time_out_real                         305.
% 7.98/1.48  --time_out_virtual                      -1.
% 7.98/1.48  --symbol_type_check                     false
% 7.98/1.48  --clausify_out                          false
% 7.98/1.48  --sig_cnt_out                           false
% 7.98/1.48  --trig_cnt_out                          false
% 7.98/1.48  --trig_cnt_out_tolerance                1.
% 7.98/1.48  --trig_cnt_out_sk_spl                   false
% 7.98/1.48  --abstr_cl_out                          false
% 7.98/1.48  
% 7.98/1.48  ------ Global Options
% 7.98/1.48  
% 7.98/1.48  --schedule                              default
% 7.98/1.48  --add_important_lit                     false
% 7.98/1.48  --prop_solver_per_cl                    1000
% 7.98/1.48  --min_unsat_core                        false
% 7.98/1.48  --soft_assumptions                      false
% 7.98/1.48  --soft_lemma_size                       3
% 7.98/1.48  --prop_impl_unit_size                   0
% 7.98/1.48  --prop_impl_unit                        []
% 7.98/1.48  --share_sel_clauses                     true
% 7.98/1.48  --reset_solvers                         false
% 7.98/1.48  --bc_imp_inh                            [conj_cone]
% 7.98/1.48  --conj_cone_tolerance                   3.
% 7.98/1.48  --extra_neg_conj                        none
% 7.98/1.48  --large_theory_mode                     true
% 7.98/1.48  --prolific_symb_bound                   200
% 7.98/1.48  --lt_threshold                          2000
% 7.98/1.48  --clause_weak_htbl                      true
% 7.98/1.48  --gc_record_bc_elim                     false
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing Options
% 7.98/1.48  
% 7.98/1.48  --preprocessing_flag                    true
% 7.98/1.48  --time_out_prep_mult                    0.1
% 7.98/1.48  --splitting_mode                        input
% 7.98/1.48  --splitting_grd                         true
% 7.98/1.48  --splitting_cvd                         false
% 7.98/1.48  --splitting_cvd_svl                     false
% 7.98/1.48  --splitting_nvd                         32
% 7.98/1.48  --sub_typing                            true
% 7.98/1.48  --prep_gs_sim                           true
% 7.98/1.48  --prep_unflatten                        true
% 7.98/1.48  --prep_res_sim                          true
% 7.98/1.48  --prep_upred                            true
% 7.98/1.48  --prep_sem_filter                       exhaustive
% 7.98/1.48  --prep_sem_filter_out                   false
% 7.98/1.48  --pred_elim                             true
% 7.98/1.48  --res_sim_input                         true
% 7.98/1.48  --eq_ax_congr_red                       true
% 7.98/1.48  --pure_diseq_elim                       true
% 7.98/1.48  --brand_transform                       false
% 7.98/1.48  --non_eq_to_eq                          false
% 7.98/1.48  --prep_def_merge                        true
% 7.98/1.48  --prep_def_merge_prop_impl              false
% 7.98/1.48  --prep_def_merge_mbd                    true
% 7.98/1.48  --prep_def_merge_tr_red                 false
% 7.98/1.48  --prep_def_merge_tr_cl                  false
% 7.98/1.48  --smt_preprocessing                     true
% 7.98/1.48  --smt_ac_axioms                         fast
% 7.98/1.48  --preprocessed_out                      false
% 7.98/1.48  --preprocessed_stats                    false
% 7.98/1.48  
% 7.98/1.48  ------ Abstraction refinement Options
% 7.98/1.48  
% 7.98/1.48  --abstr_ref                             []
% 7.98/1.48  --abstr_ref_prep                        false
% 7.98/1.48  --abstr_ref_until_sat                   false
% 7.98/1.48  --abstr_ref_sig_restrict                funpre
% 7.98/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.98/1.48  --abstr_ref_under                       []
% 7.98/1.48  
% 7.98/1.48  ------ SAT Options
% 7.98/1.48  
% 7.98/1.48  --sat_mode                              false
% 7.98/1.48  --sat_fm_restart_options                ""
% 7.98/1.48  --sat_gr_def                            false
% 7.98/1.48  --sat_epr_types                         true
% 7.98/1.48  --sat_non_cyclic_types                  false
% 7.98/1.48  --sat_finite_models                     false
% 7.98/1.48  --sat_fm_lemmas                         false
% 7.98/1.48  --sat_fm_prep                           false
% 7.98/1.48  --sat_fm_uc_incr                        true
% 7.98/1.48  --sat_out_model                         small
% 7.98/1.48  --sat_out_clauses                       false
% 7.98/1.48  
% 7.98/1.48  ------ QBF Options
% 7.98/1.48  
% 7.98/1.48  --qbf_mode                              false
% 7.98/1.48  --qbf_elim_univ                         false
% 7.98/1.48  --qbf_dom_inst                          none
% 7.98/1.48  --qbf_dom_pre_inst                      false
% 7.98/1.48  --qbf_sk_in                             false
% 7.98/1.48  --qbf_pred_elim                         true
% 7.98/1.48  --qbf_split                             512
% 7.98/1.48  
% 7.98/1.48  ------ BMC1 Options
% 7.98/1.48  
% 7.98/1.48  --bmc1_incremental                      false
% 7.98/1.48  --bmc1_axioms                           reachable_all
% 7.98/1.48  --bmc1_min_bound                        0
% 7.98/1.48  --bmc1_max_bound                        -1
% 7.98/1.48  --bmc1_max_bound_default                -1
% 7.98/1.48  --bmc1_symbol_reachability              true
% 7.98/1.48  --bmc1_property_lemmas                  false
% 7.98/1.48  --bmc1_k_induction                      false
% 7.98/1.48  --bmc1_non_equiv_states                 false
% 7.98/1.48  --bmc1_deadlock                         false
% 7.98/1.48  --bmc1_ucm                              false
% 7.98/1.48  --bmc1_add_unsat_core                   none
% 7.98/1.48  --bmc1_unsat_core_children              false
% 7.98/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.98/1.48  --bmc1_out_stat                         full
% 7.98/1.48  --bmc1_ground_init                      false
% 7.98/1.48  --bmc1_pre_inst_next_state              false
% 7.98/1.48  --bmc1_pre_inst_state                   false
% 7.98/1.48  --bmc1_pre_inst_reach_state             false
% 7.98/1.48  --bmc1_out_unsat_core                   false
% 7.98/1.48  --bmc1_aig_witness_out                  false
% 7.98/1.48  --bmc1_verbose                          false
% 7.98/1.48  --bmc1_dump_clauses_tptp                false
% 7.98/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.98/1.48  --bmc1_dump_file                        -
% 7.98/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.98/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.98/1.48  --bmc1_ucm_extend_mode                  1
% 7.98/1.48  --bmc1_ucm_init_mode                    2
% 7.98/1.48  --bmc1_ucm_cone_mode                    none
% 7.98/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.98/1.48  --bmc1_ucm_relax_model                  4
% 7.98/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.98/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.98/1.48  --bmc1_ucm_layered_model                none
% 7.98/1.48  --bmc1_ucm_max_lemma_size               10
% 7.98/1.48  
% 7.98/1.48  ------ AIG Options
% 7.98/1.48  
% 7.98/1.48  --aig_mode                              false
% 7.98/1.48  
% 7.98/1.48  ------ Instantiation Options
% 7.98/1.48  
% 7.98/1.48  --instantiation_flag                    true
% 7.98/1.48  --inst_sos_flag                         true
% 7.98/1.48  --inst_sos_phase                        true
% 7.98/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel_side                     num_symb
% 7.98/1.48  --inst_solver_per_active                1400
% 7.98/1.48  --inst_solver_calls_frac                1.
% 7.98/1.48  --inst_passive_queue_type               priority_queues
% 7.98/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.98/1.48  --inst_passive_queues_freq              [25;2]
% 7.98/1.48  --inst_dismatching                      true
% 7.98/1.48  --inst_eager_unprocessed_to_passive     true
% 7.98/1.48  --inst_prop_sim_given                   true
% 7.98/1.48  --inst_prop_sim_new                     false
% 7.98/1.48  --inst_subs_new                         false
% 7.98/1.48  --inst_eq_res_simp                      false
% 7.98/1.48  --inst_subs_given                       false
% 7.98/1.48  --inst_orphan_elimination               true
% 7.98/1.48  --inst_learning_loop_flag               true
% 7.98/1.48  --inst_learning_start                   3000
% 7.98/1.48  --inst_learning_factor                  2
% 7.98/1.48  --inst_start_prop_sim_after_learn       3
% 7.98/1.48  --inst_sel_renew                        solver
% 7.98/1.48  --inst_lit_activity_flag                true
% 7.98/1.48  --inst_restr_to_given                   false
% 7.98/1.48  --inst_activity_threshold               500
% 7.98/1.48  --inst_out_proof                        true
% 7.98/1.48  
% 7.98/1.48  ------ Resolution Options
% 7.98/1.48  
% 7.98/1.48  --resolution_flag                       true
% 7.98/1.48  --res_lit_sel                           adaptive
% 7.98/1.48  --res_lit_sel_side                      none
% 7.98/1.48  --res_ordering                          kbo
% 7.98/1.48  --res_to_prop_solver                    active
% 7.98/1.48  --res_prop_simpl_new                    false
% 7.98/1.48  --res_prop_simpl_given                  true
% 7.98/1.48  --res_passive_queue_type                priority_queues
% 7.98/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.98/1.48  --res_passive_queues_freq               [15;5]
% 7.98/1.48  --res_forward_subs                      full
% 7.98/1.48  --res_backward_subs                     full
% 7.98/1.48  --res_forward_subs_resolution           true
% 7.98/1.48  --res_backward_subs_resolution          true
% 7.98/1.48  --res_orphan_elimination                true
% 7.98/1.48  --res_time_limit                        2.
% 7.98/1.48  --res_out_proof                         true
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Options
% 7.98/1.48  
% 7.98/1.48  --superposition_flag                    true
% 7.98/1.48  --sup_passive_queue_type                priority_queues
% 7.98/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.98/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.98/1.48  --demod_completeness_check              fast
% 7.98/1.48  --demod_use_ground                      true
% 7.98/1.48  --sup_to_prop_solver                    passive
% 7.98/1.48  --sup_prop_simpl_new                    true
% 7.98/1.48  --sup_prop_simpl_given                  true
% 7.98/1.48  --sup_fun_splitting                     true
% 7.98/1.48  --sup_smt_interval                      50000
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Simplification Setup
% 7.98/1.48  
% 7.98/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.98/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.98/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_immed_triv                        [TrivRules]
% 7.98/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_bw_main                     []
% 7.98/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.98/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_input_bw                          []
% 7.98/1.48  
% 7.98/1.48  ------ Combination Options
% 7.98/1.48  
% 7.98/1.48  --comb_res_mult                         3
% 7.98/1.48  --comb_sup_mult                         2
% 7.98/1.48  --comb_inst_mult                        10
% 7.98/1.48  
% 7.98/1.48  ------ Debug Options
% 7.98/1.48  
% 7.98/1.48  --dbg_backtrace                         false
% 7.98/1.48  --dbg_dump_prop_clauses                 false
% 7.98/1.48  --dbg_dump_prop_clauses_file            -
% 7.98/1.48  --dbg_out_stat                          false
% 7.98/1.48  ------ Parsing...
% 7.98/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.98/1.48  ------ Proving...
% 7.98/1.48  ------ Problem Properties 
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  clauses                                 31
% 7.98/1.48  conjectures                             3
% 7.98/1.48  EPR                                     7
% 7.98/1.48  Horn                                    22
% 7.98/1.48  unary                                   8
% 7.98/1.48  binary                                  10
% 7.98/1.48  lits                                    69
% 7.98/1.48  lits eq                                 14
% 7.98/1.48  fd_pure                                 0
% 7.98/1.48  fd_pseudo                               0
% 7.98/1.48  fd_cond                                 0
% 7.98/1.48  fd_pseudo_cond                          9
% 7.98/1.48  AC symbols                              0
% 7.98/1.48  
% 7.98/1.48  ------ Schedule dynamic 5 is on 
% 7.98/1.48  
% 7.98/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  ------ 
% 7.98/1.48  Current options:
% 7.98/1.48  ------ 
% 7.98/1.48  
% 7.98/1.48  ------ Input Options
% 7.98/1.48  
% 7.98/1.48  --out_options                           all
% 7.98/1.48  --tptp_safe_out                         true
% 7.98/1.48  --problem_path                          ""
% 7.98/1.48  --include_path                          ""
% 7.98/1.48  --clausifier                            res/vclausify_rel
% 7.98/1.48  --clausifier_options                    ""
% 7.98/1.48  --stdin                                 false
% 7.98/1.48  --stats_out                             all
% 7.98/1.48  
% 7.98/1.48  ------ General Options
% 7.98/1.48  
% 7.98/1.48  --fof                                   false
% 7.98/1.48  --time_out_real                         305.
% 7.98/1.48  --time_out_virtual                      -1.
% 7.98/1.48  --symbol_type_check                     false
% 7.98/1.48  --clausify_out                          false
% 7.98/1.48  --sig_cnt_out                           false
% 7.98/1.48  --trig_cnt_out                          false
% 7.98/1.48  --trig_cnt_out_tolerance                1.
% 7.98/1.48  --trig_cnt_out_sk_spl                   false
% 7.98/1.48  --abstr_cl_out                          false
% 7.98/1.48  
% 7.98/1.48  ------ Global Options
% 7.98/1.48  
% 7.98/1.48  --schedule                              default
% 7.98/1.48  --add_important_lit                     false
% 7.98/1.48  --prop_solver_per_cl                    1000
% 7.98/1.48  --min_unsat_core                        false
% 7.98/1.48  --soft_assumptions                      false
% 7.98/1.48  --soft_lemma_size                       3
% 7.98/1.48  --prop_impl_unit_size                   0
% 7.98/1.48  --prop_impl_unit                        []
% 7.98/1.48  --share_sel_clauses                     true
% 7.98/1.48  --reset_solvers                         false
% 7.98/1.48  --bc_imp_inh                            [conj_cone]
% 7.98/1.48  --conj_cone_tolerance                   3.
% 7.98/1.48  --extra_neg_conj                        none
% 7.98/1.48  --large_theory_mode                     true
% 7.98/1.48  --prolific_symb_bound                   200
% 7.98/1.48  --lt_threshold                          2000
% 7.98/1.48  --clause_weak_htbl                      true
% 7.98/1.48  --gc_record_bc_elim                     false
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing Options
% 7.98/1.48  
% 7.98/1.48  --preprocessing_flag                    true
% 7.98/1.48  --time_out_prep_mult                    0.1
% 7.98/1.48  --splitting_mode                        input
% 7.98/1.48  --splitting_grd                         true
% 7.98/1.48  --splitting_cvd                         false
% 7.98/1.48  --splitting_cvd_svl                     false
% 7.98/1.48  --splitting_nvd                         32
% 7.98/1.48  --sub_typing                            true
% 7.98/1.48  --prep_gs_sim                           true
% 7.98/1.48  --prep_unflatten                        true
% 7.98/1.48  --prep_res_sim                          true
% 7.98/1.48  --prep_upred                            true
% 7.98/1.48  --prep_sem_filter                       exhaustive
% 7.98/1.48  --prep_sem_filter_out                   false
% 7.98/1.48  --pred_elim                             true
% 7.98/1.48  --res_sim_input                         true
% 7.98/1.48  --eq_ax_congr_red                       true
% 7.98/1.48  --pure_diseq_elim                       true
% 7.98/1.48  --brand_transform                       false
% 7.98/1.48  --non_eq_to_eq                          false
% 7.98/1.48  --prep_def_merge                        true
% 7.98/1.48  --prep_def_merge_prop_impl              false
% 7.98/1.48  --prep_def_merge_mbd                    true
% 7.98/1.48  --prep_def_merge_tr_red                 false
% 7.98/1.48  --prep_def_merge_tr_cl                  false
% 7.98/1.48  --smt_preprocessing                     true
% 7.98/1.48  --smt_ac_axioms                         fast
% 7.98/1.48  --preprocessed_out                      false
% 7.98/1.48  --preprocessed_stats                    false
% 7.98/1.48  
% 7.98/1.48  ------ Abstraction refinement Options
% 7.98/1.48  
% 7.98/1.48  --abstr_ref                             []
% 7.98/1.48  --abstr_ref_prep                        false
% 7.98/1.48  --abstr_ref_until_sat                   false
% 7.98/1.48  --abstr_ref_sig_restrict                funpre
% 7.98/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.98/1.48  --abstr_ref_under                       []
% 7.98/1.48  
% 7.98/1.48  ------ SAT Options
% 7.98/1.48  
% 7.98/1.48  --sat_mode                              false
% 7.98/1.48  --sat_fm_restart_options                ""
% 7.98/1.48  --sat_gr_def                            false
% 7.98/1.48  --sat_epr_types                         true
% 7.98/1.48  --sat_non_cyclic_types                  false
% 7.98/1.48  --sat_finite_models                     false
% 7.98/1.48  --sat_fm_lemmas                         false
% 7.98/1.48  --sat_fm_prep                           false
% 7.98/1.48  --sat_fm_uc_incr                        true
% 7.98/1.48  --sat_out_model                         small
% 7.98/1.48  --sat_out_clauses                       false
% 7.98/1.48  
% 7.98/1.48  ------ QBF Options
% 7.98/1.48  
% 7.98/1.48  --qbf_mode                              false
% 7.98/1.48  --qbf_elim_univ                         false
% 7.98/1.48  --qbf_dom_inst                          none
% 7.98/1.48  --qbf_dom_pre_inst                      false
% 7.98/1.48  --qbf_sk_in                             false
% 7.98/1.48  --qbf_pred_elim                         true
% 7.98/1.48  --qbf_split                             512
% 7.98/1.48  
% 7.98/1.48  ------ BMC1 Options
% 7.98/1.48  
% 7.98/1.48  --bmc1_incremental                      false
% 7.98/1.48  --bmc1_axioms                           reachable_all
% 7.98/1.48  --bmc1_min_bound                        0
% 7.98/1.48  --bmc1_max_bound                        -1
% 7.98/1.48  --bmc1_max_bound_default                -1
% 7.98/1.48  --bmc1_symbol_reachability              true
% 7.98/1.48  --bmc1_property_lemmas                  false
% 7.98/1.48  --bmc1_k_induction                      false
% 7.98/1.48  --bmc1_non_equiv_states                 false
% 7.98/1.48  --bmc1_deadlock                         false
% 7.98/1.48  --bmc1_ucm                              false
% 7.98/1.48  --bmc1_add_unsat_core                   none
% 7.98/1.48  --bmc1_unsat_core_children              false
% 7.98/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.98/1.48  --bmc1_out_stat                         full
% 7.98/1.48  --bmc1_ground_init                      false
% 7.98/1.48  --bmc1_pre_inst_next_state              false
% 7.98/1.48  --bmc1_pre_inst_state                   false
% 7.98/1.48  --bmc1_pre_inst_reach_state             false
% 7.98/1.48  --bmc1_out_unsat_core                   false
% 7.98/1.48  --bmc1_aig_witness_out                  false
% 7.98/1.48  --bmc1_verbose                          false
% 7.98/1.48  --bmc1_dump_clauses_tptp                false
% 7.98/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.98/1.48  --bmc1_dump_file                        -
% 7.98/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.98/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.98/1.48  --bmc1_ucm_extend_mode                  1
% 7.98/1.48  --bmc1_ucm_init_mode                    2
% 7.98/1.48  --bmc1_ucm_cone_mode                    none
% 7.98/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.98/1.48  --bmc1_ucm_relax_model                  4
% 7.98/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.98/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.98/1.48  --bmc1_ucm_layered_model                none
% 7.98/1.48  --bmc1_ucm_max_lemma_size               10
% 7.98/1.48  
% 7.98/1.48  ------ AIG Options
% 7.98/1.48  
% 7.98/1.48  --aig_mode                              false
% 7.98/1.48  
% 7.98/1.48  ------ Instantiation Options
% 7.98/1.48  
% 7.98/1.48  --instantiation_flag                    true
% 7.98/1.48  --inst_sos_flag                         true
% 7.98/1.48  --inst_sos_phase                        true
% 7.98/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel_side                     none
% 7.98/1.48  --inst_solver_per_active                1400
% 7.98/1.48  --inst_solver_calls_frac                1.
% 7.98/1.48  --inst_passive_queue_type               priority_queues
% 7.98/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.98/1.48  --inst_passive_queues_freq              [25;2]
% 7.98/1.48  --inst_dismatching                      true
% 7.98/1.48  --inst_eager_unprocessed_to_passive     true
% 7.98/1.48  --inst_prop_sim_given                   true
% 7.98/1.48  --inst_prop_sim_new                     false
% 7.98/1.48  --inst_subs_new                         false
% 7.98/1.48  --inst_eq_res_simp                      false
% 7.98/1.48  --inst_subs_given                       false
% 7.98/1.48  --inst_orphan_elimination               true
% 7.98/1.48  --inst_learning_loop_flag               true
% 7.98/1.48  --inst_learning_start                   3000
% 7.98/1.48  --inst_learning_factor                  2
% 7.98/1.48  --inst_start_prop_sim_after_learn       3
% 7.98/1.48  --inst_sel_renew                        solver
% 7.98/1.48  --inst_lit_activity_flag                true
% 7.98/1.48  --inst_restr_to_given                   false
% 7.98/1.48  --inst_activity_threshold               500
% 7.98/1.48  --inst_out_proof                        true
% 7.98/1.48  
% 7.98/1.48  ------ Resolution Options
% 7.98/1.48  
% 7.98/1.48  --resolution_flag                       false
% 7.98/1.48  --res_lit_sel                           adaptive
% 7.98/1.48  --res_lit_sel_side                      none
% 7.98/1.48  --res_ordering                          kbo
% 7.98/1.48  --res_to_prop_solver                    active
% 7.98/1.48  --res_prop_simpl_new                    false
% 7.98/1.48  --res_prop_simpl_given                  true
% 7.98/1.48  --res_passive_queue_type                priority_queues
% 7.98/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.98/1.48  --res_passive_queues_freq               [15;5]
% 7.98/1.48  --res_forward_subs                      full
% 7.98/1.48  --res_backward_subs                     full
% 7.98/1.48  --res_forward_subs_resolution           true
% 7.98/1.48  --res_backward_subs_resolution          true
% 7.98/1.48  --res_orphan_elimination                true
% 7.98/1.48  --res_time_limit                        2.
% 7.98/1.48  --res_out_proof                         true
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Options
% 7.98/1.48  
% 7.98/1.48  --superposition_flag                    true
% 7.98/1.48  --sup_passive_queue_type                priority_queues
% 7.98/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.98/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.98/1.48  --demod_completeness_check              fast
% 7.98/1.48  --demod_use_ground                      true
% 7.98/1.48  --sup_to_prop_solver                    passive
% 7.98/1.48  --sup_prop_simpl_new                    true
% 7.98/1.48  --sup_prop_simpl_given                  true
% 7.98/1.48  --sup_fun_splitting                     true
% 7.98/1.48  --sup_smt_interval                      50000
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Simplification Setup
% 7.98/1.48  
% 7.98/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.98/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.98/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_immed_triv                        [TrivRules]
% 7.98/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_bw_main                     []
% 7.98/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.98/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_input_bw                          []
% 7.98/1.48  
% 7.98/1.48  ------ Combination Options
% 7.98/1.48  
% 7.98/1.48  --comb_res_mult                         3
% 7.98/1.48  --comb_sup_mult                         2
% 7.98/1.48  --comb_inst_mult                        10
% 7.98/1.48  
% 7.98/1.48  ------ Debug Options
% 7.98/1.48  
% 7.98/1.48  --dbg_backtrace                         false
% 7.98/1.48  --dbg_dump_prop_clauses                 false
% 7.98/1.48  --dbg_dump_prop_clauses_file            -
% 7.98/1.48  --dbg_out_stat                          false
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  ------ Proving...
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  % SZS status Theorem for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  fof(f13,axiom,(
% 7.98/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f75,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f13])).
% 7.98/1.48  
% 7.98/1.48  fof(f14,axiom,(
% 7.98/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f76,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f14])).
% 7.98/1.48  
% 7.98/1.48  fof(f15,axiom,(
% 7.98/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f77,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f15])).
% 7.98/1.48  
% 7.98/1.48  fof(f16,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f78,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f16])).
% 7.98/1.48  
% 7.98/1.48  fof(f86,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f77,f78])).
% 7.98/1.48  
% 7.98/1.48  fof(f87,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f76,f86])).
% 7.98/1.48  
% 7.98/1.48  fof(f97,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f75,f87,f87])).
% 7.98/1.48  
% 7.98/1.48  fof(f19,conjecture,(
% 7.98/1.48    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f20,negated_conjecture,(
% 7.98/1.48    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 7.98/1.48    inference(negated_conjecture,[],[f19])).
% 7.98/1.48  
% 7.98/1.48  fof(f26,plain,(
% 7.98/1.48    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 7.98/1.48    inference(ennf_transformation,[],[f20])).
% 7.98/1.48  
% 7.98/1.48  fof(f27,plain,(
% 7.98/1.48    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 7.98/1.48    inference(flattening,[],[f26])).
% 7.98/1.48  
% 7.98/1.48  fof(f47,plain,(
% 7.98/1.48    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_xboole_0(k2_tarski(sK4,sK6),sK5) != sK5 & r2_hidden(sK6,sK5) & r2_hidden(sK4,sK5))),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f48,plain,(
% 7.98/1.48    k2_xboole_0(k2_tarski(sK4,sK6),sK5) != sK5 & r2_hidden(sK6,sK5) & r2_hidden(sK4,sK5)),
% 7.98/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f47])).
% 7.98/1.48  
% 7.98/1.48  fof(f83,plain,(
% 7.98/1.48    r2_hidden(sK4,sK5)),
% 7.98/1.48    inference(cnf_transformation,[],[f48])).
% 7.98/1.48  
% 7.98/1.48  fof(f84,plain,(
% 7.98/1.48    r2_hidden(sK6,sK5)),
% 7.98/1.48    inference(cnf_transformation,[],[f48])).
% 7.98/1.48  
% 7.98/1.48  fof(f18,axiom,(
% 7.98/1.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f45,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.98/1.48    inference(nnf_transformation,[],[f18])).
% 7.98/1.48  
% 7.98/1.48  fof(f46,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.98/1.48    inference(flattening,[],[f45])).
% 7.98/1.48  
% 7.98/1.48  fof(f82,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f46])).
% 7.98/1.48  
% 7.98/1.48  fof(f98,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f82,f87])).
% 7.98/1.48  
% 7.98/1.48  fof(f10,axiom,(
% 7.98/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f25,plain,(
% 7.98/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.98/1.48    inference(ennf_transformation,[],[f10])).
% 7.98/1.48  
% 7.98/1.48  fof(f72,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f25])).
% 7.98/1.48  
% 7.98/1.48  fof(f12,axiom,(
% 7.98/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f74,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.98/1.48    inference(cnf_transformation,[],[f12])).
% 7.98/1.48  
% 7.98/1.48  fof(f17,axiom,(
% 7.98/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f79,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.98/1.48    inference(cnf_transformation,[],[f17])).
% 7.98/1.48  
% 7.98/1.48  fof(f88,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 7.98/1.48    inference(definition_unfolding,[],[f79,f87])).
% 7.98/1.48  
% 7.98/1.48  fof(f8,axiom,(
% 7.98/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f70,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.98/1.48    inference(cnf_transformation,[],[f8])).
% 7.98/1.48  
% 7.98/1.48  fof(f96,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 7.98/1.48    inference(definition_unfolding,[],[f74,f88,f88,f70])).
% 7.98/1.48  
% 7.98/1.48  fof(f9,axiom,(
% 7.98/1.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f71,plain,(
% 7.98/1.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.98/1.48    inference(cnf_transformation,[],[f9])).
% 7.98/1.48  
% 7.98/1.48  fof(f95,plain,(
% 7.98/1.48    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 7.98/1.48    inference(definition_unfolding,[],[f71,f88])).
% 7.98/1.48  
% 7.98/1.48  fof(f5,axiom,(
% 7.98/1.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f23,plain,(
% 7.98/1.48    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 7.98/1.48    inference(ennf_transformation,[],[f5])).
% 7.98/1.48  
% 7.98/1.48  fof(f38,plain,(
% 7.98/1.48    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 7.98/1.48    inference(nnf_transformation,[],[f23])).
% 7.98/1.48  
% 7.98/1.48  fof(f39,plain,(
% 7.98/1.48    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f40,plain,(
% 7.98/1.48    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 7.98/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 7.98/1.48  
% 7.98/1.48  fof(f62,plain,(
% 7.98/1.48    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f40])).
% 7.98/1.48  
% 7.98/1.48  fof(f11,axiom,(
% 7.98/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f73,plain,(
% 7.98/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f11])).
% 7.98/1.48  
% 7.98/1.48  fof(f4,axiom,(
% 7.98/1.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f33,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.98/1.48    inference(nnf_transformation,[],[f4])).
% 7.98/1.48  
% 7.98/1.48  fof(f34,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.98/1.48    inference(flattening,[],[f33])).
% 7.98/1.48  
% 7.98/1.48  fof(f35,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.98/1.48    inference(rectify,[],[f34])).
% 7.98/1.48  
% 7.98/1.48  fof(f36,plain,(
% 7.98/1.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f37,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.98/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 7.98/1.48  
% 7.98/1.48  fof(f57,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.98/1.48    inference(cnf_transformation,[],[f37])).
% 7.98/1.48  
% 7.98/1.48  fof(f93,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.98/1.48    inference(definition_unfolding,[],[f57,f70])).
% 7.98/1.48  
% 7.98/1.48  fof(f106,plain,(
% 7.98/1.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.98/1.48    inference(equality_resolution,[],[f93])).
% 7.98/1.48  
% 7.98/1.48  fof(f7,axiom,(
% 7.98/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f43,plain,(
% 7.98/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.98/1.48    inference(nnf_transformation,[],[f7])).
% 7.98/1.48  
% 7.98/1.48  fof(f44,plain,(
% 7.98/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.98/1.48    inference(flattening,[],[f43])).
% 7.98/1.48  
% 7.98/1.48  fof(f67,plain,(
% 7.98/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.98/1.48    inference(cnf_transformation,[],[f44])).
% 7.98/1.48  
% 7.98/1.48  fof(f109,plain,(
% 7.98/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.98/1.48    inference(equality_resolution,[],[f67])).
% 7.98/1.48  
% 7.98/1.48  fof(f3,axiom,(
% 7.98/1.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f28,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.98/1.48    inference(nnf_transformation,[],[f3])).
% 7.98/1.48  
% 7.98/1.48  fof(f29,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.98/1.48    inference(flattening,[],[f28])).
% 7.98/1.48  
% 7.98/1.48  fof(f30,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.98/1.48    inference(rectify,[],[f29])).
% 7.98/1.48  
% 7.98/1.48  fof(f31,plain,(
% 7.98/1.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f32,plain,(
% 7.98/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.98/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.98/1.48  
% 7.98/1.48  fof(f51,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.98/1.48    inference(cnf_transformation,[],[f32])).
% 7.98/1.48  
% 7.98/1.48  fof(f103,plain,(
% 7.98/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.98/1.48    inference(equality_resolution,[],[f51])).
% 7.98/1.48  
% 7.98/1.48  fof(f56,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.98/1.48    inference(cnf_transformation,[],[f37])).
% 7.98/1.48  
% 7.98/1.48  fof(f94,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.98/1.48    inference(definition_unfolding,[],[f56,f70])).
% 7.98/1.48  
% 7.98/1.48  fof(f107,plain,(
% 7.98/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.98/1.48    inference(equality_resolution,[],[f94])).
% 7.98/1.48  
% 7.98/1.48  fof(f85,plain,(
% 7.98/1.48    k2_xboole_0(k2_tarski(sK4,sK6),sK5) != sK5),
% 7.98/1.48    inference(cnf_transformation,[],[f48])).
% 7.98/1.48  
% 7.98/1.48  fof(f101,plain,(
% 7.98/1.48    k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),sK5)) != sK5),
% 7.98/1.48    inference(definition_unfolding,[],[f85,f88,f87])).
% 7.98/1.48  
% 7.98/1.48  cnf(c_25,plain,
% 7.98/1.48      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 7.98/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_31,negated_conjecture,
% 7.98/1.48      ( r2_hidden(sK4,sK5) ),
% 7.98/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_960,plain,
% 7.98/1.48      ( r2_hidden(sK4,sK5) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_30,negated_conjecture,
% 7.98/1.48      ( r2_hidden(sK6,sK5) ),
% 7.98/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_961,plain,
% 7.98/1.48      ( r2_hidden(sK6,sK5) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_26,plain,
% 7.98/1.48      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 7.98/1.48      | ~ r2_hidden(X1,X2)
% 7.98/1.48      | ~ r2_hidden(X0,X2) ),
% 7.98/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_964,plain,
% 7.98/1.48      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
% 7.98/1.48      | r2_hidden(X0,X2) != iProver_top
% 7.98/1.48      | r2_hidden(X1,X2) != iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_22,plain,
% 7.98/1.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.98/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_966,plain,
% 7.98/1.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2974,plain,
% 7.98/1.48      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 7.98/1.48      | r2_hidden(X1,X2) != iProver_top
% 7.98/1.48      | r2_hidden(X0,X2) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_964,c_966]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_5359,plain,
% 7.98/1.48      ( k3_xboole_0(k3_enumset1(sK6,sK6,sK6,sK6,X0),sK5) = k3_enumset1(sK6,sK6,sK6,sK6,X0)
% 7.98/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_961,c_2974]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_5534,plain,
% 7.98/1.48      ( k3_xboole_0(k3_enumset1(sK6,sK6,sK6,sK6,sK4),sK5) = k3_enumset1(sK6,sK6,sK6,sK6,sK4) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_960,c_5359]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_24,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.98/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_6001,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k5_xboole_0(k3_enumset1(sK6,sK6,sK6,sK6,sK4),k3_enumset1(sK6,sK6,sK6,sK6,sK4)))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK6,sK6,sK6,sK6,sK4))) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_5534,c_24]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_6980,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6)))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK6,sK6,sK6,sK6,sK4))) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_25,c_6001]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_5360,plain,
% 7.98/1.48      ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,X0),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,X0)
% 7.98/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_960,c_2974]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_6034,plain,
% 7.98/1.48      ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK6),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,sK6) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_961,c_5360]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_6344,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6)))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_6034,c_24]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_6984,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK6,sK6,sK6,sK6,sK4))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) ),
% 7.98/1.48      inference(light_normalisation,[status(thm)],[c_6980,c_6344]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_27369,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k5_xboole_0(k3_enumset1(sK6,sK6,sK6,sK6,sK4),k3_enumset1(sK6,sK6,sK6,sK6,sK4)))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) ),
% 7.98/1.48      inference(demodulation,[status(thm)],[c_6984,c_6001]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_21,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 7.98/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_14,plain,
% 7.98/1.48      ( r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1 ),
% 7.98/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_972,plain,
% 7.98/1.48      ( X0 = X1
% 7.98/1.48      | r2_hidden(sK2(X0,X1),X1) = iProver_top
% 7.98/1.48      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_23,plain,
% 7.98/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.98/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_965,plain,
% 7.98/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2006,plain,
% 7.98/1.48      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_965,c_966]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_11,plain,
% 7.98/1.48      ( ~ r2_hidden(X0,X1)
% 7.98/1.48      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.98/1.48      inference(cnf_transformation,[],[f106]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_975,plain,
% 7.98/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.98/1.48      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_3036,plain,
% 7.98/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.98/1.48      | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_2006,c_975]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_20,plain,
% 7.98/1.48      ( r1_tarski(X0,X0) ),
% 7.98/1.48      inference(cnf_transformation,[],[f109]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_967,plain,
% 7.98/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2005,plain,
% 7.98/1.48      ( k3_xboole_0(X0,X0) = X0 ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_967,c_966]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2127,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_25,c_21]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2377,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_2127,c_24]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2378,plain,
% 7.98/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.98/1.48      inference(demodulation,[status(thm)],[c_2377,c_2127]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2526,plain,
% 7.98/1.48      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_2005,c_2378]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_3037,plain,
% 7.98/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.98/1.48      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.98/1.48      inference(light_normalisation,[status(thm)],[c_3036,c_2526]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_5,plain,
% 7.98/1.48      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 7.98/1.48      inference(cnf_transformation,[],[f103]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_981,plain,
% 7.98/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.98/1.48      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2773,plain,
% 7.98/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.98/1.48      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_2006,c_981]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_3195,plain,
% 7.98/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.98/1.48      inference(global_propositional_subsumption,
% 7.98/1.48                [status(thm)],
% 7.98/1.48                [c_3037,c_2773]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_3201,plain,
% 7.98/1.48      ( k1_xboole_0 = X0
% 7.98/1.48      | r2_hidden(sK2(X0,k1_xboole_0),X0) = iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_972,c_3195]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_3035,plain,
% 7.98/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.98/1.48      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_2005,c_975]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_12,plain,
% 7.98/1.48      ( r2_hidden(X0,X1)
% 7.98/1.48      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.98/1.48      inference(cnf_transformation,[],[f107]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_974,plain,
% 7.98/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.98/1.48      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2799,plain,
% 7.98/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.98/1.48      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_2005,c_974]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_3262,plain,
% 7.98/1.48      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 7.98/1.48      inference(global_propositional_subsumption,
% 7.98/1.48                [status(thm)],
% 7.98/1.48                [c_3035,c_2799]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_8043,plain,
% 7.98/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_3201,c_3262]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_27370,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) = sK5 ),
% 7.98/1.48      inference(demodulation,[status(thm)],[c_27369,c_21,c_8043]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_29,negated_conjecture,
% 7.98/1.48      ( k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK6),sK5)) != sK5 ),
% 7.98/1.48      inference(cnf_transformation,[],[f101]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2124,plain,
% 7.98/1.48      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK6))) != sK5 ),
% 7.98/1.48      inference(demodulation,[status(thm)],[c_25,c_29]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(contradiction,plain,
% 7.98/1.48      ( $false ),
% 7.98/1.48      inference(minisat,[status(thm)],[c_27370,c_2124]) ).
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  ------                               Statistics
% 7.98/1.48  
% 7.98/1.48  ------ General
% 7.98/1.48  
% 7.98/1.48  abstr_ref_over_cycles:                  0
% 7.98/1.48  abstr_ref_under_cycles:                 0
% 7.98/1.48  gc_basic_clause_elim:                   0
% 7.98/1.48  forced_gc_time:                         0
% 7.98/1.48  parsing_time:                           0.009
% 7.98/1.48  unif_index_cands_time:                  0.
% 7.98/1.48  unif_index_add_time:                    0.
% 7.98/1.48  orderings_time:                         0.
% 7.98/1.48  out_proof_time:                         0.009
% 7.98/1.48  total_time:                             0.912
% 7.98/1.48  num_of_symbols:                         46
% 7.98/1.48  num_of_terms:                           34657
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing
% 7.98/1.48  
% 7.98/1.48  num_of_splits:                          0
% 7.98/1.48  num_of_split_atoms:                     0
% 7.98/1.48  num_of_reused_defs:                     0
% 7.98/1.48  num_eq_ax_congr_red:                    48
% 7.98/1.48  num_of_sem_filtered_clauses:            1
% 7.98/1.48  num_of_subtypes:                        0
% 7.98/1.48  monotx_restored_types:                  0
% 7.98/1.48  sat_num_of_epr_types:                   0
% 7.98/1.48  sat_num_of_non_cyclic_types:            0
% 7.98/1.48  sat_guarded_non_collapsed_types:        0
% 7.98/1.48  num_pure_diseq_elim:                    0
% 7.98/1.48  simp_replaced_by:                       0
% 7.98/1.48  res_preprocessed:                       139
% 7.98/1.48  prep_upred:                             0
% 7.98/1.48  prep_unflattend:                        0
% 7.98/1.48  smt_new_axioms:                         0
% 7.98/1.48  pred_elim_cands:                        3
% 7.98/1.48  pred_elim:                              0
% 7.98/1.48  pred_elim_cl:                           0
% 7.98/1.48  pred_elim_cycles:                       2
% 7.98/1.48  merged_defs:                            0
% 7.98/1.48  merged_defs_ncl:                        0
% 7.98/1.48  bin_hyper_res:                          0
% 7.98/1.48  prep_cycles:                            4
% 7.98/1.48  pred_elim_time:                         0.001
% 7.98/1.48  splitting_time:                         0.
% 7.98/1.48  sem_filter_time:                        0.
% 7.98/1.48  monotx_time:                            0.
% 7.98/1.48  subtype_inf_time:                       0.
% 7.98/1.48  
% 7.98/1.48  ------ Problem properties
% 7.98/1.48  
% 7.98/1.48  clauses:                                31
% 7.98/1.48  conjectures:                            3
% 7.98/1.48  epr:                                    7
% 7.98/1.48  horn:                                   22
% 7.98/1.48  ground:                                 3
% 7.98/1.48  unary:                                  8
% 7.98/1.48  binary:                                 10
% 7.98/1.48  lits:                                   69
% 7.98/1.48  lits_eq:                                14
% 7.98/1.48  fd_pure:                                0
% 7.98/1.48  fd_pseudo:                              0
% 7.98/1.48  fd_cond:                                0
% 7.98/1.48  fd_pseudo_cond:                         9
% 7.98/1.48  ac_symbols:                             0
% 7.98/1.48  
% 7.98/1.48  ------ Propositional Solver
% 7.98/1.48  
% 7.98/1.48  prop_solver_calls:                      32
% 7.98/1.48  prop_fast_solver_calls:                 1048
% 7.98/1.48  smt_solver_calls:                       0
% 7.98/1.48  smt_fast_solver_calls:                  0
% 7.98/1.48  prop_num_of_clauses:                    13616
% 7.98/1.48  prop_preprocess_simplified:             23686
% 7.98/1.48  prop_fo_subsumed:                       4
% 7.98/1.48  prop_solver_time:                       0.
% 7.98/1.48  smt_solver_time:                        0.
% 7.98/1.48  smt_fast_solver_time:                   0.
% 7.98/1.48  prop_fast_solver_time:                  0.
% 7.98/1.48  prop_unsat_core_time:                   0.001
% 7.98/1.48  
% 7.98/1.48  ------ QBF
% 7.98/1.48  
% 7.98/1.48  qbf_q_res:                              0
% 7.98/1.48  qbf_num_tautologies:                    0
% 7.98/1.48  qbf_prep_cycles:                        0
% 7.98/1.48  
% 7.98/1.48  ------ BMC1
% 7.98/1.48  
% 7.98/1.48  bmc1_current_bound:                     -1
% 7.98/1.48  bmc1_last_solved_bound:                 -1
% 7.98/1.48  bmc1_unsat_core_size:                   -1
% 7.98/1.48  bmc1_unsat_core_parents_size:           -1
% 7.98/1.48  bmc1_merge_next_fun:                    0
% 7.98/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.98/1.48  
% 7.98/1.48  ------ Instantiation
% 7.98/1.48  
% 7.98/1.48  inst_num_of_clauses:                    3051
% 7.98/1.48  inst_num_in_passive:                    1303
% 7.98/1.48  inst_num_in_active:                     695
% 7.98/1.48  inst_num_in_unprocessed:                1053
% 7.98/1.48  inst_num_of_loops:                      960
% 7.98/1.48  inst_num_of_learning_restarts:          0
% 7.98/1.48  inst_num_moves_active_passive:          264
% 7.98/1.48  inst_lit_activity:                      0
% 7.98/1.48  inst_lit_activity_moves:                0
% 7.98/1.48  inst_num_tautologies:                   0
% 7.98/1.48  inst_num_prop_implied:                  0
% 7.98/1.48  inst_num_existing_simplified:           0
% 7.98/1.48  inst_num_eq_res_simplified:             0
% 7.98/1.48  inst_num_child_elim:                    0
% 7.98/1.48  inst_num_of_dismatching_blockings:      3022
% 7.98/1.48  inst_num_of_non_proper_insts:           3700
% 7.98/1.48  inst_num_of_duplicates:                 0
% 7.98/1.48  inst_inst_num_from_inst_to_res:         0
% 7.98/1.48  inst_dismatching_checking_time:         0.
% 7.98/1.48  
% 7.98/1.48  ------ Resolution
% 7.98/1.48  
% 7.98/1.48  res_num_of_clauses:                     0
% 7.98/1.48  res_num_in_passive:                     0
% 7.98/1.48  res_num_in_active:                      0
% 7.98/1.48  res_num_of_loops:                       143
% 7.98/1.48  res_forward_subset_subsumed:            175
% 7.98/1.48  res_backward_subset_subsumed:           0
% 7.98/1.48  res_forward_subsumed:                   0
% 7.98/1.48  res_backward_subsumed:                  0
% 7.98/1.48  res_forward_subsumption_resolution:     0
% 7.98/1.48  res_backward_subsumption_resolution:    0
% 7.98/1.48  res_clause_to_clause_subsumption:       6926
% 7.98/1.48  res_orphan_elimination:                 0
% 7.98/1.48  res_tautology_del:                      109
% 7.98/1.48  res_num_eq_res_simplified:              0
% 7.98/1.48  res_num_sel_changes:                    0
% 7.98/1.48  res_moves_from_active_to_pass:          0
% 7.98/1.48  
% 7.98/1.48  ------ Superposition
% 7.98/1.48  
% 7.98/1.48  sup_time_total:                         0.
% 7.98/1.48  sup_time_generating:                    0.
% 7.98/1.48  sup_time_sim_full:                      0.
% 7.98/1.48  sup_time_sim_immed:                     0.
% 7.98/1.48  
% 7.98/1.48  sup_num_of_clauses:                     1087
% 7.98/1.48  sup_num_in_active:                      185
% 7.98/1.48  sup_num_in_passive:                     902
% 7.98/1.48  sup_num_of_loops:                       190
% 7.98/1.48  sup_fw_superposition:                   501
% 7.98/1.48  sup_bw_superposition:                   1241
% 7.98/1.48  sup_immediate_simplified:               611
% 7.98/1.48  sup_given_eliminated:                   1
% 7.98/1.48  comparisons_done:                       0
% 7.98/1.48  comparisons_avoided:                    149
% 7.98/1.48  
% 7.98/1.48  ------ Simplifications
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  sim_fw_subset_subsumed:                 19
% 7.98/1.48  sim_bw_subset_subsumed:                 56
% 7.98/1.48  sim_fw_subsumed:                        245
% 7.98/1.48  sim_bw_subsumed:                        6
% 7.98/1.48  sim_fw_subsumption_res:                 0
% 7.98/1.48  sim_bw_subsumption_res:                 0
% 7.98/1.48  sim_tautology_del:                      77
% 7.98/1.48  sim_eq_tautology_del:                   23
% 7.98/1.48  sim_eq_res_simp:                        3
% 7.98/1.48  sim_fw_demodulated:                     349
% 7.98/1.48  sim_bw_demodulated:                     7
% 7.98/1.48  sim_light_normalised:                   102
% 7.98/1.48  sim_joinable_taut:                      0
% 7.98/1.48  sim_joinable_simp:                      0
% 7.98/1.48  sim_ac_normalised:                      0
% 7.98/1.48  sim_smt_subsumption:                    0
% 7.98/1.48  
%------------------------------------------------------------------------------
