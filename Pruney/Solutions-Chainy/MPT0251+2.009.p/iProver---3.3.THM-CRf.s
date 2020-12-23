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
% DateTime   : Thu Dec  3 11:33:02 EST 2020

% Result     : Theorem 15.18s
% Output     : CNFRefutation 15.18s
% Verified   : 
% Statistics : Number of formulae       :  156 (2783 expanded)
%              Number of clauses        :   72 ( 521 expanded)
%              Number of leaves         :   25 ( 783 expanded)
%              Depth                    :   22
%              Number of atoms          :  371 (5315 expanded)
%              Number of equality atoms :  146 (2550 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK4),sK5) != sK5
      & r2_hidden(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k2_xboole_0(k1_tarski(sK4),sK5) != sK5
    & r2_hidden(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f30,f48])).

fof(f83,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f85])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f82,f86])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f79,f86])).

fof(f89,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f51,f87,f87])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f91,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f72,f87,f87,f69])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f92,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f73,f69,f69,f87])).

fof(f10,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f90,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f70,f87])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f74,f87])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f6,axiom,(
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

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f42])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    k2_xboole_0(k1_tarski(sK4),sK5) != sK5 ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f75,f86])).

fof(f97,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)) != sK5 ),
    inference(definition_unfolding,[],[f84,f87,f88])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_956,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_959,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_961,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3259,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_961])).

cnf(c_45366,plain,
    ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,X0),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_3259])).

cnf(c_49275,plain,
    ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_956,c_45366])).

cnf(c_1,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_21,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_22,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1724,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_21,c_22])).

cnf(c_10380,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1,c_1724])).

cnf(c_50397,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)),k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k5_xboole_0(sK5,k3_xboole_0(sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)))) ),
    inference(superposition,[status(thm)],[c_49275,c_10380])).

cnf(c_50430,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)),k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k5_xboole_0(sK5,k3_xboole_0(sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
    inference(demodulation,[status(thm)],[c_50397,c_49275])).

cnf(c_19,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1682,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_19])).

cnf(c_1914,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1682,c_22])).

cnf(c_23,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_960,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1440,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_960,c_961])).

cnf(c_1917,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1682,c_1440])).

cnf(c_1921,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1914,c_1917])).

cnf(c_18,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_962,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1439,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_962,c_961])).

cnf(c_1922,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1921,c_1439])).

cnf(c_1919,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1682,c_21])).

cnf(c_1920,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1919,c_1682])).

cnf(c_2062,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1439,c_1920])).

cnf(c_2161,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1922,c_2062])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_967,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_970,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3058,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_970])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_978,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11816,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3058,c_978])).

cnf(c_23219,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_11816])).

cnf(c_23253,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3058,c_23219])).

cnf(c_25258,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_23253])).

cnf(c_25287,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_25258])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_965,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3521,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_965])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_966,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_25288,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_966,c_25258])).

cnf(c_25698,plain,
    ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25287,c_3521,c_25288])).

cnf(c_25699,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_25698])).

cnf(c_25707,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_25699])).

cnf(c_3515,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_965])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_976,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3514,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_965])).

cnf(c_1918,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_960])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_963,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4286,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1918,c_963])).

cnf(c_5049,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3514,c_4286])).

cnf(c_5460,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3515,c_5049])).

cnf(c_7023,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k1_xboole_0
    | r1_xboole_0(X2,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3515,c_5460])).

cnf(c_25740,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25707,c_7023])).

cnf(c_9485,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))) = k1_xboole_0
    | r1_xboole_0(X3,X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3515,c_7023])).

cnf(c_25741,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25707,c_9485])).

cnf(c_25742,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25740,c_25741])).

cnf(c_29938,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_25742,c_1920])).

cnf(c_50431,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_50430,c_2161,c_25742,c_29938])).

cnf(c_27,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)) != sK5 ),
    inference(cnf_transformation,[],[f97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50431,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n018.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 09:56:26 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running in FOF mode
% 15.18/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.18/2.49  
% 15.18/2.49  ------  iProver source info
% 15.18/2.49  
% 15.18/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.18/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.18/2.49  git: non_committed_changes: false
% 15.18/2.49  git: last_make_outside_of_git: false
% 15.18/2.49  
% 15.18/2.49  ------ 
% 15.18/2.49  
% 15.18/2.49  ------ Input Options
% 15.18/2.49  
% 15.18/2.49  --out_options                           all
% 15.18/2.49  --tptp_safe_out                         true
% 15.18/2.49  --problem_path                          ""
% 15.18/2.49  --include_path                          ""
% 15.18/2.49  --clausifier                            res/vclausify_rel
% 15.18/2.49  --clausifier_options                    ""
% 15.18/2.49  --stdin                                 false
% 15.18/2.49  --stats_out                             all
% 15.18/2.49  
% 15.18/2.49  ------ General Options
% 15.18/2.49  
% 15.18/2.49  --fof                                   false
% 15.18/2.49  --time_out_real                         305.
% 15.18/2.49  --time_out_virtual                      -1.
% 15.18/2.49  --symbol_type_check                     false
% 15.18/2.49  --clausify_out                          false
% 15.18/2.49  --sig_cnt_out                           false
% 15.18/2.49  --trig_cnt_out                          false
% 15.18/2.49  --trig_cnt_out_tolerance                1.
% 15.18/2.49  --trig_cnt_out_sk_spl                   false
% 15.18/2.49  --abstr_cl_out                          false
% 15.18/2.49  
% 15.18/2.49  ------ Global Options
% 15.18/2.49  
% 15.18/2.49  --schedule                              default
% 15.18/2.49  --add_important_lit                     false
% 15.18/2.49  --prop_solver_per_cl                    1000
% 15.18/2.49  --min_unsat_core                        false
% 15.18/2.49  --soft_assumptions                      false
% 15.18/2.49  --soft_lemma_size                       3
% 15.18/2.49  --prop_impl_unit_size                   0
% 15.18/2.49  --prop_impl_unit                        []
% 15.18/2.49  --share_sel_clauses                     true
% 15.18/2.49  --reset_solvers                         false
% 15.18/2.49  --bc_imp_inh                            [conj_cone]
% 15.18/2.49  --conj_cone_tolerance                   3.
% 15.18/2.49  --extra_neg_conj                        none
% 15.18/2.49  --large_theory_mode                     true
% 15.18/2.49  --prolific_symb_bound                   200
% 15.18/2.49  --lt_threshold                          2000
% 15.18/2.49  --clause_weak_htbl                      true
% 15.18/2.49  --gc_record_bc_elim                     false
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing Options
% 15.18/2.49  
% 15.18/2.49  --preprocessing_flag                    true
% 15.18/2.49  --time_out_prep_mult                    0.1
% 15.18/2.49  --splitting_mode                        input
% 15.18/2.49  --splitting_grd                         true
% 15.18/2.49  --splitting_cvd                         false
% 15.18/2.49  --splitting_cvd_svl                     false
% 15.18/2.49  --splitting_nvd                         32
% 15.18/2.49  --sub_typing                            true
% 15.18/2.49  --prep_gs_sim                           true
% 15.18/2.49  --prep_unflatten                        true
% 15.18/2.49  --prep_res_sim                          true
% 15.18/2.49  --prep_upred                            true
% 15.18/2.49  --prep_sem_filter                       exhaustive
% 15.18/2.49  --prep_sem_filter_out                   false
% 15.18/2.49  --pred_elim                             true
% 15.18/2.49  --res_sim_input                         true
% 15.18/2.49  --eq_ax_congr_red                       true
% 15.18/2.49  --pure_diseq_elim                       true
% 15.18/2.49  --brand_transform                       false
% 15.18/2.49  --non_eq_to_eq                          false
% 15.18/2.49  --prep_def_merge                        true
% 15.18/2.49  --prep_def_merge_prop_impl              false
% 15.18/2.49  --prep_def_merge_mbd                    true
% 15.18/2.49  --prep_def_merge_tr_red                 false
% 15.18/2.49  --prep_def_merge_tr_cl                  false
% 15.18/2.49  --smt_preprocessing                     true
% 15.18/2.49  --smt_ac_axioms                         fast
% 15.18/2.49  --preprocessed_out                      false
% 15.18/2.49  --preprocessed_stats                    false
% 15.18/2.49  
% 15.18/2.49  ------ Abstraction refinement Options
% 15.18/2.49  
% 15.18/2.49  --abstr_ref                             []
% 15.18/2.49  --abstr_ref_prep                        false
% 15.18/2.49  --abstr_ref_until_sat                   false
% 15.18/2.49  --abstr_ref_sig_restrict                funpre
% 15.18/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.18/2.49  --abstr_ref_under                       []
% 15.18/2.49  
% 15.18/2.49  ------ SAT Options
% 15.18/2.49  
% 15.18/2.49  --sat_mode                              false
% 15.18/2.49  --sat_fm_restart_options                ""
% 15.18/2.49  --sat_gr_def                            false
% 15.18/2.49  --sat_epr_types                         true
% 15.18/2.49  --sat_non_cyclic_types                  false
% 15.18/2.49  --sat_finite_models                     false
% 15.18/2.49  --sat_fm_lemmas                         false
% 15.18/2.49  --sat_fm_prep                           false
% 15.18/2.49  --sat_fm_uc_incr                        true
% 15.18/2.49  --sat_out_model                         small
% 15.18/2.49  --sat_out_clauses                       false
% 15.18/2.49  
% 15.18/2.49  ------ QBF Options
% 15.18/2.49  
% 15.18/2.49  --qbf_mode                              false
% 15.18/2.49  --qbf_elim_univ                         false
% 15.18/2.49  --qbf_dom_inst                          none
% 15.18/2.49  --qbf_dom_pre_inst                      false
% 15.18/2.49  --qbf_sk_in                             false
% 15.18/2.49  --qbf_pred_elim                         true
% 15.18/2.49  --qbf_split                             512
% 15.18/2.49  
% 15.18/2.49  ------ BMC1 Options
% 15.18/2.49  
% 15.18/2.49  --bmc1_incremental                      false
% 15.18/2.49  --bmc1_axioms                           reachable_all
% 15.18/2.49  --bmc1_min_bound                        0
% 15.18/2.49  --bmc1_max_bound                        -1
% 15.18/2.49  --bmc1_max_bound_default                -1
% 15.18/2.49  --bmc1_symbol_reachability              true
% 15.18/2.49  --bmc1_property_lemmas                  false
% 15.18/2.49  --bmc1_k_induction                      false
% 15.18/2.49  --bmc1_non_equiv_states                 false
% 15.18/2.49  --bmc1_deadlock                         false
% 15.18/2.49  --bmc1_ucm                              false
% 15.18/2.49  --bmc1_add_unsat_core                   none
% 15.18/2.49  --bmc1_unsat_core_children              false
% 15.18/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.18/2.49  --bmc1_out_stat                         full
% 15.18/2.49  --bmc1_ground_init                      false
% 15.18/2.49  --bmc1_pre_inst_next_state              false
% 15.18/2.49  --bmc1_pre_inst_state                   false
% 15.18/2.49  --bmc1_pre_inst_reach_state             false
% 15.18/2.49  --bmc1_out_unsat_core                   false
% 15.18/2.49  --bmc1_aig_witness_out                  false
% 15.18/2.49  --bmc1_verbose                          false
% 15.18/2.49  --bmc1_dump_clauses_tptp                false
% 15.18/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.18/2.49  --bmc1_dump_file                        -
% 15.18/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.18/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.18/2.49  --bmc1_ucm_extend_mode                  1
% 15.18/2.49  --bmc1_ucm_init_mode                    2
% 15.18/2.49  --bmc1_ucm_cone_mode                    none
% 15.18/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.18/2.49  --bmc1_ucm_relax_model                  4
% 15.18/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.18/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.18/2.49  --bmc1_ucm_layered_model                none
% 15.18/2.49  --bmc1_ucm_max_lemma_size               10
% 15.18/2.49  
% 15.18/2.49  ------ AIG Options
% 15.18/2.49  
% 15.18/2.49  --aig_mode                              false
% 15.18/2.49  
% 15.18/2.49  ------ Instantiation Options
% 15.18/2.49  
% 15.18/2.49  --instantiation_flag                    true
% 15.18/2.49  --inst_sos_flag                         true
% 15.18/2.49  --inst_sos_phase                        true
% 15.18/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel_side                     num_symb
% 15.18/2.49  --inst_solver_per_active                1400
% 15.18/2.49  --inst_solver_calls_frac                1.
% 15.18/2.49  --inst_passive_queue_type               priority_queues
% 15.18/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.18/2.49  --inst_passive_queues_freq              [25;2]
% 15.18/2.49  --inst_dismatching                      true
% 15.18/2.49  --inst_eager_unprocessed_to_passive     true
% 15.18/2.49  --inst_prop_sim_given                   true
% 15.18/2.49  --inst_prop_sim_new                     false
% 15.18/2.49  --inst_subs_new                         false
% 15.18/2.49  --inst_eq_res_simp                      false
% 15.18/2.49  --inst_subs_given                       false
% 15.18/2.49  --inst_orphan_elimination               true
% 15.18/2.49  --inst_learning_loop_flag               true
% 15.18/2.49  --inst_learning_start                   3000
% 15.18/2.49  --inst_learning_factor                  2
% 15.18/2.49  --inst_start_prop_sim_after_learn       3
% 15.18/2.49  --inst_sel_renew                        solver
% 15.18/2.49  --inst_lit_activity_flag                true
% 15.18/2.49  --inst_restr_to_given                   false
% 15.18/2.49  --inst_activity_threshold               500
% 15.18/2.49  --inst_out_proof                        true
% 15.18/2.49  
% 15.18/2.49  ------ Resolution Options
% 15.18/2.49  
% 15.18/2.49  --resolution_flag                       true
% 15.18/2.49  --res_lit_sel                           adaptive
% 15.18/2.49  --res_lit_sel_side                      none
% 15.18/2.49  --res_ordering                          kbo
% 15.18/2.49  --res_to_prop_solver                    active
% 15.18/2.49  --res_prop_simpl_new                    false
% 15.18/2.49  --res_prop_simpl_given                  true
% 15.18/2.49  --res_passive_queue_type                priority_queues
% 15.18/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.18/2.49  --res_passive_queues_freq               [15;5]
% 15.18/2.49  --res_forward_subs                      full
% 15.18/2.49  --res_backward_subs                     full
% 15.18/2.49  --res_forward_subs_resolution           true
% 15.18/2.49  --res_backward_subs_resolution          true
% 15.18/2.49  --res_orphan_elimination                true
% 15.18/2.49  --res_time_limit                        2.
% 15.18/2.49  --res_out_proof                         true
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Options
% 15.18/2.49  
% 15.18/2.49  --superposition_flag                    true
% 15.18/2.49  --sup_passive_queue_type                priority_queues
% 15.18/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.18/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.18/2.49  --demod_completeness_check              fast
% 15.18/2.49  --demod_use_ground                      true
% 15.18/2.49  --sup_to_prop_solver                    passive
% 15.18/2.49  --sup_prop_simpl_new                    true
% 15.18/2.49  --sup_prop_simpl_given                  true
% 15.18/2.49  --sup_fun_splitting                     true
% 15.18/2.49  --sup_smt_interval                      50000
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Simplification Setup
% 15.18/2.49  
% 15.18/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.18/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.18/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.18/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.18/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.18/2.49  --sup_immed_triv                        [TrivRules]
% 15.18/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_bw_main                     []
% 15.18/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.18/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.18/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_input_bw                          []
% 15.18/2.49  
% 15.18/2.49  ------ Combination Options
% 15.18/2.49  
% 15.18/2.49  --comb_res_mult                         3
% 15.18/2.49  --comb_sup_mult                         2
% 15.18/2.49  --comb_inst_mult                        10
% 15.18/2.49  
% 15.18/2.49  ------ Debug Options
% 15.18/2.49  
% 15.18/2.49  --dbg_backtrace                         false
% 15.18/2.49  --dbg_dump_prop_clauses                 false
% 15.18/2.49  --dbg_dump_prop_clauses_file            -
% 15.18/2.49  --dbg_out_stat                          false
% 15.18/2.49  ------ Parsing...
% 15.18/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.18/2.49  ------ Proving...
% 15.18/2.49  ------ Problem Properties 
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  clauses                                 28
% 15.18/2.49  conjectures                             2
% 15.18/2.49  EPR                                     6
% 15.18/2.49  Horn                                    22
% 15.18/2.49  unary                                   8
% 15.18/2.49  binary                                  12
% 15.18/2.49  lits                                    57
% 15.18/2.49  lits eq                                 10
% 15.18/2.49  fd_pure                                 0
% 15.18/2.49  fd_pseudo                               0
% 15.18/2.49  fd_cond                                 0
% 15.18/2.49  fd_pseudo_cond                          4
% 15.18/2.49  AC symbols                              0
% 15.18/2.49  
% 15.18/2.49  ------ Schedule dynamic 5 is on 
% 15.18/2.49  
% 15.18/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  ------ 
% 15.18/2.49  Current options:
% 15.18/2.49  ------ 
% 15.18/2.49  
% 15.18/2.49  ------ Input Options
% 15.18/2.49  
% 15.18/2.49  --out_options                           all
% 15.18/2.49  --tptp_safe_out                         true
% 15.18/2.49  --problem_path                          ""
% 15.18/2.49  --include_path                          ""
% 15.18/2.49  --clausifier                            res/vclausify_rel
% 15.18/2.49  --clausifier_options                    ""
% 15.18/2.49  --stdin                                 false
% 15.18/2.49  --stats_out                             all
% 15.18/2.49  
% 15.18/2.49  ------ General Options
% 15.18/2.49  
% 15.18/2.49  --fof                                   false
% 15.18/2.49  --time_out_real                         305.
% 15.18/2.49  --time_out_virtual                      -1.
% 15.18/2.49  --symbol_type_check                     false
% 15.18/2.49  --clausify_out                          false
% 15.18/2.49  --sig_cnt_out                           false
% 15.18/2.49  --trig_cnt_out                          false
% 15.18/2.49  --trig_cnt_out_tolerance                1.
% 15.18/2.49  --trig_cnt_out_sk_spl                   false
% 15.18/2.49  --abstr_cl_out                          false
% 15.18/2.49  
% 15.18/2.49  ------ Global Options
% 15.18/2.49  
% 15.18/2.49  --schedule                              default
% 15.18/2.49  --add_important_lit                     false
% 15.18/2.49  --prop_solver_per_cl                    1000
% 15.18/2.49  --min_unsat_core                        false
% 15.18/2.49  --soft_assumptions                      false
% 15.18/2.49  --soft_lemma_size                       3
% 15.18/2.49  --prop_impl_unit_size                   0
% 15.18/2.49  --prop_impl_unit                        []
% 15.18/2.49  --share_sel_clauses                     true
% 15.18/2.49  --reset_solvers                         false
% 15.18/2.49  --bc_imp_inh                            [conj_cone]
% 15.18/2.49  --conj_cone_tolerance                   3.
% 15.18/2.49  --extra_neg_conj                        none
% 15.18/2.49  --large_theory_mode                     true
% 15.18/2.49  --prolific_symb_bound                   200
% 15.18/2.49  --lt_threshold                          2000
% 15.18/2.49  --clause_weak_htbl                      true
% 15.18/2.49  --gc_record_bc_elim                     false
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing Options
% 15.18/2.49  
% 15.18/2.49  --preprocessing_flag                    true
% 15.18/2.49  --time_out_prep_mult                    0.1
% 15.18/2.49  --splitting_mode                        input
% 15.18/2.49  --splitting_grd                         true
% 15.18/2.49  --splitting_cvd                         false
% 15.18/2.49  --splitting_cvd_svl                     false
% 15.18/2.49  --splitting_nvd                         32
% 15.18/2.49  --sub_typing                            true
% 15.18/2.49  --prep_gs_sim                           true
% 15.18/2.49  --prep_unflatten                        true
% 15.18/2.49  --prep_res_sim                          true
% 15.18/2.49  --prep_upred                            true
% 15.18/2.49  --prep_sem_filter                       exhaustive
% 15.18/2.49  --prep_sem_filter_out                   false
% 15.18/2.49  --pred_elim                             true
% 15.18/2.49  --res_sim_input                         true
% 15.18/2.49  --eq_ax_congr_red                       true
% 15.18/2.49  --pure_diseq_elim                       true
% 15.18/2.49  --brand_transform                       false
% 15.18/2.49  --non_eq_to_eq                          false
% 15.18/2.49  --prep_def_merge                        true
% 15.18/2.49  --prep_def_merge_prop_impl              false
% 15.18/2.49  --prep_def_merge_mbd                    true
% 15.18/2.49  --prep_def_merge_tr_red                 false
% 15.18/2.49  --prep_def_merge_tr_cl                  false
% 15.18/2.49  --smt_preprocessing                     true
% 15.18/2.49  --smt_ac_axioms                         fast
% 15.18/2.49  --preprocessed_out                      false
% 15.18/2.49  --preprocessed_stats                    false
% 15.18/2.49  
% 15.18/2.49  ------ Abstraction refinement Options
% 15.18/2.49  
% 15.18/2.49  --abstr_ref                             []
% 15.18/2.49  --abstr_ref_prep                        false
% 15.18/2.49  --abstr_ref_until_sat                   false
% 15.18/2.49  --abstr_ref_sig_restrict                funpre
% 15.18/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.18/2.49  --abstr_ref_under                       []
% 15.18/2.49  
% 15.18/2.49  ------ SAT Options
% 15.18/2.49  
% 15.18/2.49  --sat_mode                              false
% 15.18/2.49  --sat_fm_restart_options                ""
% 15.18/2.49  --sat_gr_def                            false
% 15.18/2.49  --sat_epr_types                         true
% 15.18/2.49  --sat_non_cyclic_types                  false
% 15.18/2.49  --sat_finite_models                     false
% 15.18/2.49  --sat_fm_lemmas                         false
% 15.18/2.49  --sat_fm_prep                           false
% 15.18/2.49  --sat_fm_uc_incr                        true
% 15.18/2.49  --sat_out_model                         small
% 15.18/2.49  --sat_out_clauses                       false
% 15.18/2.49  
% 15.18/2.49  ------ QBF Options
% 15.18/2.49  
% 15.18/2.49  --qbf_mode                              false
% 15.18/2.49  --qbf_elim_univ                         false
% 15.18/2.49  --qbf_dom_inst                          none
% 15.18/2.49  --qbf_dom_pre_inst                      false
% 15.18/2.49  --qbf_sk_in                             false
% 15.18/2.49  --qbf_pred_elim                         true
% 15.18/2.49  --qbf_split                             512
% 15.18/2.49  
% 15.18/2.49  ------ BMC1 Options
% 15.18/2.49  
% 15.18/2.49  --bmc1_incremental                      false
% 15.18/2.49  --bmc1_axioms                           reachable_all
% 15.18/2.49  --bmc1_min_bound                        0
% 15.18/2.49  --bmc1_max_bound                        -1
% 15.18/2.49  --bmc1_max_bound_default                -1
% 15.18/2.49  --bmc1_symbol_reachability              true
% 15.18/2.49  --bmc1_property_lemmas                  false
% 15.18/2.49  --bmc1_k_induction                      false
% 15.18/2.49  --bmc1_non_equiv_states                 false
% 15.18/2.49  --bmc1_deadlock                         false
% 15.18/2.49  --bmc1_ucm                              false
% 15.18/2.49  --bmc1_add_unsat_core                   none
% 15.18/2.49  --bmc1_unsat_core_children              false
% 15.18/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.18/2.49  --bmc1_out_stat                         full
% 15.18/2.49  --bmc1_ground_init                      false
% 15.18/2.49  --bmc1_pre_inst_next_state              false
% 15.18/2.49  --bmc1_pre_inst_state                   false
% 15.18/2.49  --bmc1_pre_inst_reach_state             false
% 15.18/2.49  --bmc1_out_unsat_core                   false
% 15.18/2.49  --bmc1_aig_witness_out                  false
% 15.18/2.49  --bmc1_verbose                          false
% 15.18/2.49  --bmc1_dump_clauses_tptp                false
% 15.18/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.18/2.49  --bmc1_dump_file                        -
% 15.18/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.18/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.18/2.49  --bmc1_ucm_extend_mode                  1
% 15.18/2.49  --bmc1_ucm_init_mode                    2
% 15.18/2.49  --bmc1_ucm_cone_mode                    none
% 15.18/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.18/2.49  --bmc1_ucm_relax_model                  4
% 15.18/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.18/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.18/2.49  --bmc1_ucm_layered_model                none
% 15.18/2.49  --bmc1_ucm_max_lemma_size               10
% 15.18/2.49  
% 15.18/2.49  ------ AIG Options
% 15.18/2.49  
% 15.18/2.49  --aig_mode                              false
% 15.18/2.49  
% 15.18/2.49  ------ Instantiation Options
% 15.18/2.49  
% 15.18/2.49  --instantiation_flag                    true
% 15.18/2.49  --inst_sos_flag                         true
% 15.18/2.49  --inst_sos_phase                        true
% 15.18/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel_side                     none
% 15.18/2.49  --inst_solver_per_active                1400
% 15.18/2.49  --inst_solver_calls_frac                1.
% 15.18/2.49  --inst_passive_queue_type               priority_queues
% 15.18/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.18/2.49  --inst_passive_queues_freq              [25;2]
% 15.18/2.49  --inst_dismatching                      true
% 15.18/2.49  --inst_eager_unprocessed_to_passive     true
% 15.18/2.49  --inst_prop_sim_given                   true
% 15.18/2.49  --inst_prop_sim_new                     false
% 15.18/2.49  --inst_subs_new                         false
% 15.18/2.49  --inst_eq_res_simp                      false
% 15.18/2.49  --inst_subs_given                       false
% 15.18/2.49  --inst_orphan_elimination               true
% 15.18/2.49  --inst_learning_loop_flag               true
% 15.18/2.49  --inst_learning_start                   3000
% 15.18/2.49  --inst_learning_factor                  2
% 15.18/2.49  --inst_start_prop_sim_after_learn       3
% 15.18/2.49  --inst_sel_renew                        solver
% 15.18/2.49  --inst_lit_activity_flag                true
% 15.18/2.49  --inst_restr_to_given                   false
% 15.18/2.49  --inst_activity_threshold               500
% 15.18/2.49  --inst_out_proof                        true
% 15.18/2.49  
% 15.18/2.49  ------ Resolution Options
% 15.18/2.49  
% 15.18/2.49  --resolution_flag                       false
% 15.18/2.49  --res_lit_sel                           adaptive
% 15.18/2.49  --res_lit_sel_side                      none
% 15.18/2.49  --res_ordering                          kbo
% 15.18/2.49  --res_to_prop_solver                    active
% 15.18/2.49  --res_prop_simpl_new                    false
% 15.18/2.49  --res_prop_simpl_given                  true
% 15.18/2.49  --res_passive_queue_type                priority_queues
% 15.18/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.18/2.49  --res_passive_queues_freq               [15;5]
% 15.18/2.49  --res_forward_subs                      full
% 15.18/2.49  --res_backward_subs                     full
% 15.18/2.49  --res_forward_subs_resolution           true
% 15.18/2.49  --res_backward_subs_resolution          true
% 15.18/2.49  --res_orphan_elimination                true
% 15.18/2.49  --res_time_limit                        2.
% 15.18/2.49  --res_out_proof                         true
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Options
% 15.18/2.49  
% 15.18/2.49  --superposition_flag                    true
% 15.18/2.49  --sup_passive_queue_type                priority_queues
% 15.18/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.18/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.18/2.49  --demod_completeness_check              fast
% 15.18/2.49  --demod_use_ground                      true
% 15.18/2.49  --sup_to_prop_solver                    passive
% 15.18/2.49  --sup_prop_simpl_new                    true
% 15.18/2.49  --sup_prop_simpl_given                  true
% 15.18/2.49  --sup_fun_splitting                     true
% 15.18/2.49  --sup_smt_interval                      50000
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Simplification Setup
% 15.18/2.49  
% 15.18/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.18/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.18/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.18/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.18/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.18/2.49  --sup_immed_triv                        [TrivRules]
% 15.18/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_bw_main                     []
% 15.18/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.18/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.18/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_input_bw                          []
% 15.18/2.49  
% 15.18/2.49  ------ Combination Options
% 15.18/2.49  
% 15.18/2.49  --comb_res_mult                         3
% 15.18/2.49  --comb_sup_mult                         2
% 15.18/2.49  --comb_inst_mult                        10
% 15.18/2.49  
% 15.18/2.49  ------ Debug Options
% 15.18/2.49  
% 15.18/2.49  --dbg_backtrace                         false
% 15.18/2.49  --dbg_dump_prop_clauses                 false
% 15.18/2.49  --dbg_dump_prop_clauses_file            -
% 15.18/2.49  --dbg_out_stat                          false
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  ------ Proving...
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  % SZS status Theorem for theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  fof(f21,conjecture,(
% 15.18/2.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f22,negated_conjecture,(
% 15.18/2.49    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 15.18/2.49    inference(negated_conjecture,[],[f21])).
% 15.18/2.49  
% 15.18/2.49  fof(f30,plain,(
% 15.18/2.49    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 15.18/2.49    inference(ennf_transformation,[],[f22])).
% 15.18/2.49  
% 15.18/2.49  fof(f48,plain,(
% 15.18/2.49    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK4),sK5) != sK5 & r2_hidden(sK4,sK5))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f49,plain,(
% 15.18/2.49    k2_xboole_0(k1_tarski(sK4),sK5) != sK5 & r2_hidden(sK4,sK5)),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f30,f48])).
% 15.18/2.49  
% 15.18/2.49  fof(f83,plain,(
% 15.18/2.49    r2_hidden(sK4,sK5)),
% 15.18/2.49    inference(cnf_transformation,[],[f49])).
% 15.18/2.49  
% 15.18/2.49  fof(f20,axiom,(
% 15.18/2.49    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f46,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.18/2.49    inference(nnf_transformation,[],[f20])).
% 15.18/2.49  
% 15.18/2.49  fof(f47,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.18/2.49    inference(flattening,[],[f46])).
% 15.18/2.49  
% 15.18/2.49  fof(f82,plain,(
% 15.18/2.49    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f47])).
% 15.18/2.49  
% 15.18/2.49  fof(f16,axiom,(
% 15.18/2.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f76,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f16])).
% 15.18/2.49  
% 15.18/2.49  fof(f17,axiom,(
% 15.18/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f77,plain,(
% 15.18/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f17])).
% 15.18/2.49  
% 15.18/2.49  fof(f18,axiom,(
% 15.18/2.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f78,plain,(
% 15.18/2.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f18])).
% 15.18/2.49  
% 15.18/2.49  fof(f85,plain,(
% 15.18/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 15.18/2.49    inference(definition_unfolding,[],[f77,f78])).
% 15.18/2.49  
% 15.18/2.49  fof(f86,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 15.18/2.49    inference(definition_unfolding,[],[f76,f85])).
% 15.18/2.49  
% 15.18/2.49  fof(f94,plain,(
% 15.18/2.49    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 15.18/2.49    inference(definition_unfolding,[],[f82,f86])).
% 15.18/2.49  
% 15.18/2.49  fof(f11,axiom,(
% 15.18/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f29,plain,(
% 15.18/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.18/2.49    inference(ennf_transformation,[],[f11])).
% 15.18/2.49  
% 15.18/2.49  fof(f71,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f29])).
% 15.18/2.49  
% 15.18/2.49  fof(f2,axiom,(
% 15.18/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f51,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f2])).
% 15.18/2.49  
% 15.18/2.49  fof(f19,axiom,(
% 15.18/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f79,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f19])).
% 15.18/2.49  
% 15.18/2.49  fof(f87,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 15.18/2.49    inference(definition_unfolding,[],[f79,f86])).
% 15.18/2.49  
% 15.18/2.49  fof(f89,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 15.18/2.49    inference(definition_unfolding,[],[f51,f87,f87])).
% 15.18/2.49  
% 15.18/2.49  fof(f12,axiom,(
% 15.18/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f72,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f12])).
% 15.18/2.49  
% 15.18/2.49  fof(f9,axiom,(
% 15.18/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f69,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f9])).
% 15.18/2.49  
% 15.18/2.49  fof(f91,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 15.18/2.49    inference(definition_unfolding,[],[f72,f87,f87,f69])).
% 15.18/2.49  
% 15.18/2.49  fof(f13,axiom,(
% 15.18/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f73,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f13])).
% 15.18/2.49  
% 15.18/2.49  fof(f92,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 15.18/2.49    inference(definition_unfolding,[],[f73,f69,f69,f87])).
% 15.18/2.49  
% 15.18/2.49  fof(f10,axiom,(
% 15.18/2.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f70,plain,(
% 15.18/2.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.18/2.49    inference(cnf_transformation,[],[f10])).
% 15.18/2.49  
% 15.18/2.49  fof(f90,plain,(
% 15.18/2.49    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 15.18/2.49    inference(definition_unfolding,[],[f70,f87])).
% 15.18/2.49  
% 15.18/2.49  fof(f14,axiom,(
% 15.18/2.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f74,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f14])).
% 15.18/2.49  
% 15.18/2.49  fof(f93,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 15.18/2.49    inference(definition_unfolding,[],[f74,f87])).
% 15.18/2.49  
% 15.18/2.49  fof(f8,axiom,(
% 15.18/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f44,plain,(
% 15.18/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.18/2.49    inference(nnf_transformation,[],[f8])).
% 15.18/2.49  
% 15.18/2.49  fof(f45,plain,(
% 15.18/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.18/2.49    inference(flattening,[],[f44])).
% 15.18/2.49  
% 15.18/2.49  fof(f66,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.18/2.49    inference(cnf_transformation,[],[f45])).
% 15.18/2.49  
% 15.18/2.49  fof(f102,plain,(
% 15.18/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.18/2.49    inference(equality_resolution,[],[f66])).
% 15.18/2.49  
% 15.18/2.49  fof(f6,axiom,(
% 15.18/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f23,plain,(
% 15.18/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.18/2.49    inference(rectify,[],[f6])).
% 15.18/2.49  
% 15.18/2.49  fof(f27,plain,(
% 15.18/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 15.18/2.49    inference(ennf_transformation,[],[f23])).
% 15.18/2.49  
% 15.18/2.49  fof(f40,plain,(
% 15.18/2.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f41,plain,(
% 15.18/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f40])).
% 15.18/2.49  
% 15.18/2.49  fof(f62,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f41])).
% 15.18/2.49  
% 15.18/2.49  fof(f5,axiom,(
% 15.18/2.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f35,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.18/2.49    inference(nnf_transformation,[],[f5])).
% 15.18/2.49  
% 15.18/2.49  fof(f36,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.18/2.49    inference(flattening,[],[f35])).
% 15.18/2.49  
% 15.18/2.49  fof(f37,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.18/2.49    inference(rectify,[],[f36])).
% 15.18/2.49  
% 15.18/2.49  fof(f38,plain,(
% 15.18/2.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f39,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 15.18/2.49  
% 15.18/2.49  fof(f56,plain,(
% 15.18/2.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.18/2.49    inference(cnf_transformation,[],[f39])).
% 15.18/2.49  
% 15.18/2.49  fof(f99,plain,(
% 15.18/2.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 15.18/2.49    inference(equality_resolution,[],[f56])).
% 15.18/2.49  
% 15.18/2.49  fof(f1,axiom,(
% 15.18/2.49    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f25,plain,(
% 15.18/2.49    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 15.18/2.49    inference(ennf_transformation,[],[f1])).
% 15.18/2.49  
% 15.18/2.49  fof(f50,plain,(
% 15.18/2.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f25])).
% 15.18/2.49  
% 15.18/2.49  fof(f7,axiom,(
% 15.18/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f24,plain,(
% 15.18/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.18/2.49    inference(rectify,[],[f7])).
% 15.18/2.49  
% 15.18/2.49  fof(f28,plain,(
% 15.18/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.18/2.49    inference(ennf_transformation,[],[f24])).
% 15.18/2.49  
% 15.18/2.49  fof(f42,plain,(
% 15.18/2.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f43,plain,(
% 15.18/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f42])).
% 15.18/2.49  
% 15.18/2.49  fof(f65,plain,(
% 15.18/2.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f43])).
% 15.18/2.49  
% 15.18/2.49  fof(f61,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f41])).
% 15.18/2.49  
% 15.18/2.49  fof(f4,axiom,(
% 15.18/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f26,plain,(
% 15.18/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.18/2.49    inference(ennf_transformation,[],[f4])).
% 15.18/2.49  
% 15.18/2.49  fof(f31,plain,(
% 15.18/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.18/2.49    inference(nnf_transformation,[],[f26])).
% 15.18/2.49  
% 15.18/2.49  fof(f32,plain,(
% 15.18/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.18/2.49    inference(rectify,[],[f31])).
% 15.18/2.49  
% 15.18/2.49  fof(f33,plain,(
% 15.18/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f34,plain,(
% 15.18/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 15.18/2.49  
% 15.18/2.49  fof(f53,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f34])).
% 15.18/2.49  
% 15.18/2.49  fof(f68,plain,(
% 15.18/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f45])).
% 15.18/2.49  
% 15.18/2.49  fof(f84,plain,(
% 15.18/2.49    k2_xboole_0(k1_tarski(sK4),sK5) != sK5),
% 15.18/2.49    inference(cnf_transformation,[],[f49])).
% 15.18/2.49  
% 15.18/2.49  fof(f15,axiom,(
% 15.18/2.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f75,plain,(
% 15.18/2.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f15])).
% 15.18/2.49  
% 15.18/2.49  fof(f88,plain,(
% 15.18/2.49    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 15.18/2.49    inference(definition_unfolding,[],[f75,f86])).
% 15.18/2.49  
% 15.18/2.49  fof(f97,plain,(
% 15.18/2.49    k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)) != sK5),
% 15.18/2.49    inference(definition_unfolding,[],[f84,f87,f88])).
% 15.18/2.49  
% 15.18/2.49  cnf(c_28,negated_conjecture,
% 15.18/2.49      ( r2_hidden(sK4,sK5) ),
% 15.18/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_956,plain,
% 15.18/2.49      ( r2_hidden(sK4,sK5) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_24,plain,
% 15.18/2.49      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 15.18/2.49      | ~ r2_hidden(X1,X2)
% 15.18/2.49      | ~ r2_hidden(X0,X2) ),
% 15.18/2.49      inference(cnf_transformation,[],[f94]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_959,plain,
% 15.18/2.49      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
% 15.18/2.49      | r2_hidden(X0,X2) != iProver_top
% 15.18/2.49      | r2_hidden(X1,X2) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_20,plain,
% 15.18/2.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.18/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_961,plain,
% 15.18/2.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3259,plain,
% 15.18/2.49      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 15.18/2.49      | r2_hidden(X1,X2) != iProver_top
% 15.18/2.49      | r2_hidden(X0,X2) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_959,c_961]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_45366,plain,
% 15.18/2.49      ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,X0),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,X0)
% 15.18/2.49      | r2_hidden(X0,sK5) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_956,c_3259]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_49275,plain,
% 15.18/2.49      ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_956,c_45366]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1,plain,
% 15.18/2.49      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f89]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_21,plain,
% 15.18/2.49      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f91]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_22,plain,
% 15.18/2.49      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f92]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1724,plain,
% 15.18/2.49      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_21,c_22]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_10380,plain,
% 15.18/2.49      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1,c_1724]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_50397,plain,
% 15.18/2.49      ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)),k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k5_xboole_0(sK5,k3_xboole_0(sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)))) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_49275,c_10380]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_50430,plain,
% 15.18/2.49      ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)),k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k5_xboole_0(sK5,k3_xboole_0(sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
% 15.18/2.49      inference(demodulation,[status(thm)],[c_50397,c_49275]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_19,plain,
% 15.18/2.49      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 15.18/2.49      inference(cnf_transformation,[],[f90]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1682,plain,
% 15.18/2.49      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1,c_19]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1914,plain,
% 15.18/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1682,c_22]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_23,plain,
% 15.18/2.49      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 15.18/2.49      inference(cnf_transformation,[],[f93]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_960,plain,
% 15.18/2.49      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1440,plain,
% 15.18/2.49      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_960,c_961]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1917,plain,
% 15.18/2.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1682,c_1440]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1921,plain,
% 15.18/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 15.18/2.49      inference(demodulation,[status(thm)],[c_1914,c_1917]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_18,plain,
% 15.18/2.49      ( r1_tarski(X0,X0) ),
% 15.18/2.49      inference(cnf_transformation,[],[f102]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_962,plain,
% 15.18/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1439,plain,
% 15.18/2.49      ( k3_xboole_0(X0,X0) = X0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_962,c_961]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1922,plain,
% 15.18/2.49      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 15.18/2.49      inference(light_normalisation,[status(thm)],[c_1921,c_1439]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1919,plain,
% 15.18/2.49      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1682,c_21]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1920,plain,
% 15.18/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 15.18/2.49      inference(demodulation,[status(thm)],[c_1919,c_1682]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2062,plain,
% 15.18/2.49      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1439,c_1920]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2161,plain,
% 15.18/2.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.18/2.49      inference(light_normalisation,[status(thm)],[c_1922,c_2062]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_12,plain,
% 15.18/2.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 15.18/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_967,plain,
% 15.18/2.49      ( r1_xboole_0(X0,X1) = iProver_top
% 15.18/2.49      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f99]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_970,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) = iProver_top
% 15.18/2.49      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3058,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.18/2.49      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1440,c_970]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_0,plain,
% 15.18/2.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 15.18/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_978,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.18/2.49      | r2_hidden(X1,X0) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_11816,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.18/2.49      | r2_hidden(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_3058,c_978]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_23219,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.18/2.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1682,c_11816]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_23253,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.18/2.49      | r2_hidden(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_3058,c_23219]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25258,plain,
% 15.18/2.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 15.18/2.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1682,c_23253]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25287,plain,
% 15.18/2.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
% 15.18/2.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_967,c_25258]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_14,plain,
% 15.18/2.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_965,plain,
% 15.18/2.49      ( r1_xboole_0(X0,X1) != iProver_top
% 15.18/2.49      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3521,plain,
% 15.18/2.49      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 15.18/2.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1917,c_965]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_13,plain,
% 15.18/2.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 15.18/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_966,plain,
% 15.18/2.49      ( r1_xboole_0(X0,X1) = iProver_top
% 15.18/2.49      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25288,plain,
% 15.18/2.49      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
% 15.18/2.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_966,c_25258]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25698,plain,
% 15.18/2.49      ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(global_propositional_subsumption,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_25287,c_3521,c_25288]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25699,plain,
% 15.18/2.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(renaming,[status(thm)],[c_25698]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25707,plain,
% 15.18/2.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_967,c_25699]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3515,plain,
% 15.18/2.49      ( r1_xboole_0(X0,X1) != iProver_top
% 15.18/2.49      | r1_xboole_0(X2,k3_xboole_0(X0,X1)) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_967,c_965]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3,plain,
% 15.18/2.49      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 15.18/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_976,plain,
% 15.18/2.49      ( r1_tarski(X0,X1) = iProver_top
% 15.18/2.49      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3514,plain,
% 15.18/2.49      ( r1_xboole_0(X0,X1) != iProver_top
% 15.18/2.49      | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_976,c_965]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1918,plain,
% 15.18/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1682,c_960]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_16,plain,
% 15.18/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.18/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_963,plain,
% 15.18/2.49      ( X0 = X1
% 15.18/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.18/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_4286,plain,
% 15.18/2.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1918,c_963]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_5049,plain,
% 15.18/2.49      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 15.18/2.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_3514,c_4286]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_5460,plain,
% 15.18/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k1_xboole_0
% 15.18/2.49      | r1_xboole_0(X1,X2) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_3515,c_5049]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_7023,plain,
% 15.18/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k1_xboole_0
% 15.18/2.49      | r1_xboole_0(X2,X3) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_3515,c_5460]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25740,plain,
% 15.18/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))) = k1_xboole_0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_25707,c_7023]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9485,plain,
% 15.18/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))) = k1_xboole_0
% 15.18/2.49      | r1_xboole_0(X3,X4) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_3515,c_7023]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25741,plain,
% 15.18/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0)))) = k1_xboole_0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_25707,c_9485]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25742,plain,
% 15.18/2.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.18/2.49      inference(demodulation,[status(thm)],[c_25740,c_25741]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_29938,plain,
% 15.18/2.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.18/2.49      inference(demodulation,[status(thm)],[c_25742,c_1920]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_50431,plain,
% 15.18/2.49      ( k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)) = sK5 ),
% 15.18/2.49      inference(demodulation,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_50430,c_2161,c_25742,c_29938]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_27,negated_conjecture,
% 15.18/2.49      ( k3_tarski(k3_enumset1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)) != sK5 ),
% 15.18/2.49      inference(cnf_transformation,[],[f97]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(contradiction,plain,
% 15.18/2.49      ( $false ),
% 15.18/2.49      inference(minisat,[status(thm)],[c_50431,c_27]) ).
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  ------                               Statistics
% 15.18/2.49  
% 15.18/2.49  ------ General
% 15.18/2.49  
% 15.18/2.49  abstr_ref_over_cycles:                  0
% 15.18/2.49  abstr_ref_under_cycles:                 0
% 15.18/2.49  gc_basic_clause_elim:                   0
% 15.18/2.49  forced_gc_time:                         0
% 15.18/2.49  parsing_time:                           0.015
% 15.18/2.49  unif_index_cands_time:                  0.
% 15.18/2.49  unif_index_add_time:                    0.
% 15.18/2.49  orderings_time:                         0.
% 15.18/2.49  out_proof_time:                         0.017
% 15.18/2.49  total_time:                             1.545
% 15.18/2.49  num_of_symbols:                         45
% 15.18/2.49  num_of_terms:                           64104
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing
% 15.18/2.49  
% 15.18/2.49  num_of_splits:                          0
% 15.18/2.49  num_of_split_atoms:                     0
% 15.18/2.49  num_of_reused_defs:                     0
% 15.18/2.49  num_eq_ax_congr_red:                    36
% 15.18/2.49  num_of_sem_filtered_clauses:            1
% 15.18/2.49  num_of_subtypes:                        0
% 15.18/2.49  monotx_restored_types:                  0
% 15.18/2.49  sat_num_of_epr_types:                   0
% 15.18/2.49  sat_num_of_non_cyclic_types:            0
% 15.18/2.49  sat_guarded_non_collapsed_types:        0
% 15.18/2.49  num_pure_diseq_elim:                    0
% 15.18/2.49  simp_replaced_by:                       0
% 15.18/2.49  res_preprocessed:                       129
% 15.18/2.49  prep_upred:                             0
% 15.18/2.49  prep_unflattend:                        0
% 15.18/2.49  smt_new_axioms:                         0
% 15.18/2.49  pred_elim_cands:                        3
% 15.18/2.49  pred_elim:                              0
% 15.18/2.49  pred_elim_cl:                           0
% 15.18/2.49  pred_elim_cycles:                       2
% 15.18/2.49  merged_defs:                            0
% 15.18/2.49  merged_defs_ncl:                        0
% 15.18/2.49  bin_hyper_res:                          0
% 15.18/2.49  prep_cycles:                            4
% 15.18/2.49  pred_elim_time:                         0.003
% 15.18/2.49  splitting_time:                         0.
% 15.18/2.49  sem_filter_time:                        0.
% 15.18/2.49  monotx_time:                            0.
% 15.18/2.49  subtype_inf_time:                       0.
% 15.18/2.49  
% 15.18/2.49  ------ Problem properties
% 15.18/2.49  
% 15.18/2.49  clauses:                                28
% 15.18/2.49  conjectures:                            2
% 15.18/2.49  epr:                                    6
% 15.18/2.49  horn:                                   22
% 15.18/2.49  ground:                                 2
% 15.18/2.49  unary:                                  8
% 15.18/2.49  binary:                                 12
% 15.18/2.49  lits:                                   57
% 15.18/2.49  lits_eq:                                10
% 15.18/2.49  fd_pure:                                0
% 15.18/2.49  fd_pseudo:                              0
% 15.18/2.49  fd_cond:                                0
% 15.18/2.49  fd_pseudo_cond:                         4
% 15.18/2.49  ac_symbols:                             0
% 15.18/2.49  
% 15.18/2.49  ------ Propositional Solver
% 15.18/2.49  
% 15.18/2.49  prop_solver_calls:                      33
% 15.18/2.49  prop_fast_solver_calls:                 930
% 15.18/2.49  smt_solver_calls:                       0
% 15.18/2.49  smt_fast_solver_calls:                  0
% 15.18/2.49  prop_num_of_clauses:                    27557
% 15.18/2.49  prop_preprocess_simplified:             56618
% 15.18/2.49  prop_fo_subsumed:                       3
% 15.18/2.49  prop_solver_time:                       0.
% 15.18/2.49  smt_solver_time:                        0.
% 15.18/2.49  smt_fast_solver_time:                   0.
% 15.18/2.49  prop_fast_solver_time:                  0.
% 15.18/2.49  prop_unsat_core_time:                   0.004
% 15.18/2.49  
% 15.18/2.49  ------ QBF
% 15.18/2.49  
% 15.18/2.49  qbf_q_res:                              0
% 15.18/2.49  qbf_num_tautologies:                    0
% 15.18/2.49  qbf_prep_cycles:                        0
% 15.18/2.49  
% 15.18/2.49  ------ BMC1
% 15.18/2.49  
% 15.18/2.49  bmc1_current_bound:                     -1
% 15.18/2.49  bmc1_last_solved_bound:                 -1
% 15.18/2.49  bmc1_unsat_core_size:                   -1
% 15.18/2.49  bmc1_unsat_core_parents_size:           -1
% 15.18/2.49  bmc1_merge_next_fun:                    0
% 15.18/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.18/2.50  
% 15.18/2.50  ------ Instantiation
% 15.18/2.50  
% 15.18/2.50  inst_num_of_clauses:                    8144
% 15.18/2.50  inst_num_in_passive:                    3946
% 15.18/2.50  inst_num_in_active:                     872
% 15.18/2.50  inst_num_in_unprocessed:                3327
% 15.18/2.50  inst_num_of_loops:                      960
% 15.18/2.50  inst_num_of_learning_restarts:          0
% 15.18/2.50  inst_num_moves_active_passive:          88
% 15.18/2.50  inst_lit_activity:                      0
% 15.18/2.50  inst_lit_activity_moves:                0
% 15.18/2.50  inst_num_tautologies:                   0
% 15.18/2.50  inst_num_prop_implied:                  0
% 15.18/2.50  inst_num_existing_simplified:           0
% 15.18/2.50  inst_num_eq_res_simplified:             0
% 15.18/2.50  inst_num_child_elim:                    0
% 15.18/2.50  inst_num_of_dismatching_blockings:      1831
% 15.18/2.50  inst_num_of_non_proper_insts:           5665
% 15.18/2.50  inst_num_of_duplicates:                 0
% 15.18/2.50  inst_inst_num_from_inst_to_res:         0
% 15.18/2.50  inst_dismatching_checking_time:         0.
% 15.18/2.50  
% 15.18/2.50  ------ Resolution
% 15.18/2.50  
% 15.18/2.50  res_num_of_clauses:                     0
% 15.18/2.50  res_num_in_passive:                     0
% 15.18/2.50  res_num_in_active:                      0
% 15.18/2.50  res_num_of_loops:                       133
% 15.18/2.50  res_forward_subset_subsumed:            332
% 15.18/2.50  res_backward_subset_subsumed:           2
% 15.18/2.50  res_forward_subsumed:                   0
% 15.18/2.50  res_backward_subsumed:                  0
% 15.18/2.50  res_forward_subsumption_resolution:     0
% 15.18/2.50  res_backward_subsumption_resolution:    0
% 15.18/2.50  res_clause_to_clause_subsumption:       5956
% 15.18/2.50  res_orphan_elimination:                 0
% 15.18/2.50  res_tautology_del:                      77
% 15.18/2.50  res_num_eq_res_simplified:              0
% 15.18/2.50  res_num_sel_changes:                    0
% 15.18/2.50  res_moves_from_active_to_pass:          0
% 15.18/2.50  
% 15.18/2.50  ------ Superposition
% 15.18/2.50  
% 15.18/2.50  sup_time_total:                         0.
% 15.18/2.50  sup_time_generating:                    0.
% 15.18/2.50  sup_time_sim_full:                      0.
% 15.18/2.50  sup_time_sim_immed:                     0.
% 15.18/2.50  
% 15.18/2.50  sup_num_of_clauses:                     576
% 15.18/2.50  sup_num_in_active:                      169
% 15.18/2.50  sup_num_in_passive:                     407
% 15.18/2.50  sup_num_of_loops:                       190
% 15.18/2.50  sup_fw_superposition:                   1768
% 15.18/2.50  sup_bw_superposition:                   1246
% 15.18/2.50  sup_immediate_simplified:               867
% 15.18/2.50  sup_given_eliminated:                   0
% 15.18/2.50  comparisons_done:                       0
% 15.18/2.50  comparisons_avoided:                    0
% 15.18/2.50  
% 15.18/2.50  ------ Simplifications
% 15.18/2.50  
% 15.18/2.50  
% 15.18/2.50  sim_fw_subset_subsumed:                 12
% 15.18/2.50  sim_bw_subset_subsumed:                 11
% 15.18/2.50  sim_fw_subsumed:                        169
% 15.18/2.50  sim_bw_subsumed:                        19
% 15.18/2.50  sim_fw_subsumption_res:                 0
% 15.18/2.50  sim_bw_subsumption_res:                 0
% 15.18/2.50  sim_tautology_del:                      38
% 15.18/2.50  sim_eq_tautology_del:                   205
% 15.18/2.50  sim_eq_res_simp:                        2
% 15.18/2.50  sim_fw_demodulated:                     490
% 15.18/2.50  sim_bw_demodulated:                     7
% 15.18/2.50  sim_light_normalised:                   439
% 15.18/2.50  sim_joinable_taut:                      0
% 15.18/2.50  sim_joinable_simp:                      0
% 15.18/2.50  sim_ac_normalised:                      0
% 15.18/2.50  sim_smt_subsumption:                    0
% 15.18/2.50  
%------------------------------------------------------------------------------
