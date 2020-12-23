%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:19 EST 2020

% Result     : Theorem 31.83s
% Output     : CNFRefutation 31.83s
% Verified   : 
% Statistics : Number of formulae       :  392 (236311 expanded)
%              Number of clauses        :  294 (115823 expanded)
%              Number of leaves         :   28 (59730 expanded)
%              Depth                    :   39
%              Number of atoms          :  625 (237485 expanded)
%              Number of equality atoms :  492 (237273 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f24,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f109,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f25,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

fof(f26,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f111,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f26])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f112,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f27])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f28])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f112,f113])).

fof(f134,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f111,f133])).

fof(f135,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f110,f134])).

fof(f139,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f109,f135])).

fof(f166,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k4_enumset1(X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f100,f139])).

fof(f188,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k4_enumset1(X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f166])).

fof(f189,plain,(
    ! [X3] : r2_hidden(X3,k4_enumset1(X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f188])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f29])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f115,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f30])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f126,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f136,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f126,f135])).

fof(f140,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f107,f136,f113,f134])).

fof(f142,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f115,f140])).

fof(f171,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f114,f142])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f143,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f106,f136,f113,f139])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f103,f133,f133])).

fof(f36,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f70,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK9
        | k1_tarski(sK7) != sK8 )
      & ( k1_tarski(sK7) != sK9
        | k1_xboole_0 != sK8 )
      & ( k1_tarski(sK7) != sK9
        | k1_tarski(sK7) != sK8 )
      & k2_xboole_0(sK8,sK9) = k1_tarski(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ( k1_xboole_0 != sK9
      | k1_tarski(sK7) != sK8 )
    & ( k1_tarski(sK7) != sK9
      | k1_xboole_0 != sK8 )
    & ( k1_tarski(sK7) != sK9
      | k1_tarski(sK7) != sK8 )
    & k2_xboole_0(sK8,sK9) = k1_tarski(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f43,f70])).

fof(f129,plain,(
    k2_xboole_0(sK8,sK9) = k1_tarski(sK7) ),
    inference(cnf_transformation,[],[f71])).

fof(f181,plain,(
    k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,sK9)) ),
    inference(definition_unfolding,[],[f129,f136,f139])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f149,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f73,f136])).

fof(f184,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f149])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f137,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f98,f136])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X0,X0,X0,X0,X0,X0)))) = k4_enumset1(X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f122,f137,f139,f139])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f138,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f90,f137])).

fof(f162,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0)))))) ),
    inference(definition_unfolding,[],[f93,f136,f136,f138])).

fof(f15,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f163,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f95,f136,f136,f136])).

fof(f132,plain,
    ( k1_xboole_0 != sK9
    | k1_tarski(sK7) != sK8 ),
    inference(cnf_transformation,[],[f71])).

fof(f178,plain,
    ( k1_xboole_0 != sK9
    | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK8 ),
    inference(definition_unfolding,[],[f132,f139])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f67])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f175,plain,(
    ! [X0,X1] :
      ( k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f123,f139,f139])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f159,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f88,f138])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f89,f138])).

fof(f131,plain,
    ( k1_tarski(sK7) != sK9
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f71])).

fof(f179,plain,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9
    | k1_xboole_0 != sK8 ),
    inference(definition_unfolding,[],[f131,f139])).

fof(f130,plain,
    ( k1_tarski(sK7) != sK9
    | k1_tarski(sK7) != sK8 ),
    inference(cnf_transformation,[],[f71])).

fof(f180,plain,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9
    | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK8 ),
    inference(definition_unfolding,[],[f130,f139,f139])).

cnf(c_28,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f189])).

cnf(c_1150,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_33,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_0,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_2387,plain,
    ( k4_enumset1(X0,X1,X2,X3,X3,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_33,c_0])).

cnf(c_30,plain,
    ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_49,negated_conjecture,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,sK9)) ),
    inference(cnf_transformation,[],[f181])).

cnf(c_1867,plain,
    ( k3_tarski(k4_enumset1(sK9,sK9,sK9,sK8,sK8,sK8)) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(demodulation,[status(thm)],[c_30,c_49])).

cnf(c_11095,plain,
    ( k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,sK8)) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(demodulation,[status(thm)],[c_2387,c_1867])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f184])).

cnf(c_1162,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_38484,plain,
    ( r2_hidden(X0,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != iProver_top
    | r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_11095,c_1162])).

cnf(c_41335,plain,
    ( r2_hidden(sK7,sK8) = iProver_top
    | r2_hidden(sK7,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_38484])).

cnf(c_40,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k5_xboole_0(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X0,X0,X0,X0,X0,X0)))) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_24,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_478,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X0,X0,X0,X0,X0,X0))))) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(theory_normalisation,[status(thm)],[c_40,c_24,c_1])).

cnf(c_1142,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X1,X1,X1,X1,X1,X1))))) = k4_enumset1(X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_41748,plain,
    ( k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)
    | r2_hidden(sK7,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_41335,c_1142])).

cnf(c_11256,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_2387,c_30])).

cnf(c_21,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0)))))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_479,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))))))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_21,c_24,c_1])).

cnf(c_11484,plain,
    ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k5_xboole_0(sK9,k5_xboole_0(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,sK9)) ),
    inference(superposition,[status(thm)],[c_11095,c_479])).

cnf(c_25,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1693,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_25,c_24])).

cnf(c_22,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1499,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_22,c_1])).

cnf(c_1703,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1693,c_1499])).

cnf(c_11485,plain,
    ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,sK9)) ),
    inference(demodulation,[status(thm)],[c_11484,c_1703])).

cnf(c_27333,plain,
    ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))) = k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,sK8)) ),
    inference(demodulation,[status(thm)],[c_11256,c_11485])).

cnf(c_27336,plain,
    ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(light_normalisation,[status(thm)],[c_27333,c_11095])).

cnf(c_23,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f163])).

cnf(c_27755,plain,
    ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) ),
    inference(superposition,[status(thm)],[c_27336,c_23])).

cnf(c_27766,plain,
    ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(demodulation,[status(thm)],[c_27755,c_27336])).

cnf(c_41749,plain,
    ( k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)
    | r2_hidden(sK7,sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41748,c_27766])).

cnf(c_41750,plain,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = sK8
    | r2_hidden(sK7,sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_41749,c_22,c_25])).

cnf(c_46,negated_conjecture,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK8
    | k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f178])).

cnf(c_43,plain,
    ( ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))
    | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f175])).

cnf(c_1205,plain,
    ( ~ r1_tarski(sK9,k4_enumset1(X0,X0,X0,X0,X0,X0))
    | k4_enumset1(X0,X0,X0,X0,X0,X0) = sK9
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_1212,plain,
    ( ~ r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))
    | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = sK9
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_18,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f159])).

cnf(c_481,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_18,c_24,c_1])).

cnf(c_2834,plain,
    ( r1_tarski(sK9,k4_enumset1(X0,X0,X0,X0,X0,X0))
    | k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_2836,plain,
    ( r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))
    | k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f158])).

cnf(c_482,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_17,c_24,c_1])).

cnf(c_6095,plain,
    ( ~ r1_tarski(sK9,k4_enumset1(X0,X0,X0,X0,X0,X0))
    | k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_6096,plain,
    ( k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = k1_xboole_0
    | r1_tarski(sK9,k4_enumset1(X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6095])).

cnf(c_6098,plain,
    ( k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) = k1_xboole_0
    | r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6096])).

cnf(c_11481,plain,
    ( k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,sK8)) ),
    inference(superposition,[status(thm)],[c_11095,c_23])).

cnf(c_11486,plain,
    ( k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(demodulation,[status(thm)],[c_11481,c_11095])).

cnf(c_1153,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_1203,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_24,c_1])).

cnf(c_1201,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_24,c_1])).

cnf(c_4243,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_25,c_1201])).

cnf(c_4264,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_4243,c_22])).

cnf(c_5009,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_4264,c_24])).

cnf(c_5580,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1,c_5009])).

cnf(c_5916,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1203,c_5580])).

cnf(c_19238,plain,
    ( k5_xboole_0(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1153,c_5916])).

cnf(c_19263,plain,
    ( k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != k1_xboole_0
    | r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11486,c_19238])).

cnf(c_19288,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19263,c_25])).

cnf(c_19289,plain,
    ( r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19288])).

cnf(c_5612,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),X2),X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(superposition,[status(thm)],[c_5009,c_24])).

cnf(c_5615,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,X2)) = X1 ),
    inference(superposition,[status(thm)],[c_5009,c_4264])).

cnf(c_5636,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_5615,c_24])).

cnf(c_6168,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_5636])).

cnf(c_6607,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X3,k5_xboole_0(X0,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_24,c_6168])).

cnf(c_20539,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X4,X1))),k5_xboole_0(k5_xboole_0(X0,X2),X3)) = X4 ),
    inference(superposition,[status(thm)],[c_5612,c_6607])).

cnf(c_6137,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = X2 ),
    inference(superposition,[status(thm)],[c_24,c_5636])).

cnf(c_6149,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_1,c_5636])).

cnf(c_6478,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_6149,c_24])).

cnf(c_19519,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X4)),X2) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X1),X3)) ),
    inference(superposition,[status(thm)],[c_6137,c_6478])).

cnf(c_5587,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_24,c_5009])).

cnf(c_6010,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3)))) = k5_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_24,c_5587])).

cnf(c_19657,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X2,X4))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),X4) ),
    inference(superposition,[status(thm)],[c_6478,c_6010])).

cnf(c_15472,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X2,X4))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4))) ),
    inference(superposition,[status(thm)],[c_6010,c_6010])).

cnf(c_15487,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X2,X4))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4))) ),
    inference(light_normalisation,[status(thm)],[c_15472,c_24])).

cnf(c_19671,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))) ),
    inference(light_normalisation,[status(thm)],[c_19657,c_24,c_15487])).

cnf(c_19866,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X1))) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X4)) ),
    inference(demodulation,[status(thm)],[c_19519,c_19671])).

cnf(c_5625,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,X1)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5009,c_1203])).

cnf(c_5633,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X1)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_5625,c_24])).

cnf(c_13381,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X1))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_5633,c_1201])).

cnf(c_1202,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_24,c_1])).

cnf(c_5140,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_22,c_1202])).

cnf(c_6445,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_5140,c_6149])).

cnf(c_6536,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_6445,c_22])).

cnf(c_7363,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1,c_6536])).

cnf(c_15323,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)),X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X3,X4)) ),
    inference(superposition,[status(thm)],[c_7363,c_6010])).

cnf(c_5601,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(superposition,[status(thm)],[c_24,c_5009])).

cnf(c_12073,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X4)),X3),X4) ),
    inference(superposition,[status(thm)],[c_5601,c_6536])).

cnf(c_12146,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),X2) = k5_xboole_0(k5_xboole_0(X0,X1),X3) ),
    inference(demodulation,[status(thm)],[c_12073,c_7363])).

cnf(c_5594,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1,c_5009])).

cnf(c_5644,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_5594,c_24])).

cnf(c_12275,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))),X4) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),X4)) ),
    inference(superposition,[status(thm)],[c_5644,c_5612])).

cnf(c_7422,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = k5_xboole_0(X1,k5_xboole_0(X3,X2)) ),
    inference(superposition,[status(thm)],[c_6536,c_5580])).

cnf(c_12425,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X2,X1),X3)) ),
    inference(light_normalisation,[status(thm)],[c_12275,c_7422])).

cnf(c_13323,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),X1) = k5_xboole_0(X2,k5_xboole_0(X0,X3)) ),
    inference(superposition,[status(thm)],[c_4264,c_5633])).

cnf(c_5613,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(X0,X2),X3)) = k5_xboole_0(X1,X3) ),
    inference(superposition,[status(thm)],[c_5009,c_5009])).

cnf(c_5637,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X2),X3)) = k5_xboole_0(X1,X3) ),
    inference(light_normalisation,[status(thm)],[c_5613,c_24])).

cnf(c_13984,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X3,X4),X2)),X5)) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X1,X4)),X5) ),
    inference(superposition,[status(thm)],[c_5637,c_5637])).

cnf(c_7527,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(superposition,[status(thm)],[c_7363,c_24])).

cnf(c_14087,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X4)) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X4)) ),
    inference(demodulation,[status(thm)],[c_13984,c_7527,c_12425])).

cnf(c_5617,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5009,c_1202])).

cnf(c_5635,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_5617,c_24])).

cnf(c_13661,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(X2,k5_xboole_0(X0,X3)) ),
    inference(superposition,[status(thm)],[c_5635,c_4264])).

cnf(c_13717,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k5_xboole_0(X2,k5_xboole_0(X4,X5))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X1,X5)),k5_xboole_0(X0,X3)) ),
    inference(superposition,[status(thm)],[c_5635,c_5633])).

cnf(c_12328,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),X3),k5_xboole_0(X1,X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X2),X3)) ),
    inference(superposition,[status(thm)],[c_5612,c_1202])).

cnf(c_12390,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),k5_xboole_0(X1,X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X2),X3)) ),
    inference(light_normalisation,[status(thm)],[c_12328,c_24])).

cnf(c_12438,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k5_xboole_0(X2,X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X1),X3)) ),
    inference(demodulation,[status(thm)],[c_12425,c_12390])).

cnf(c_13729,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X3,X4))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X3,X2),X4)) ),
    inference(demodulation,[status(thm)],[c_13717,c_12425,c_12438])).

cnf(c_14088,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_14087,c_12425,c_13661,c_13729])).

cnf(c_15586,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_15323,c_12146,c_12425,c_13323,c_14088])).

cnf(c_19867,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X1))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X4))) ),
    inference(demodulation,[status(thm)],[c_19866,c_13381,c_15586])).

cnf(c_20942,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(k5_xboole_0(X2,X0),X1)) = X3 ),
    inference(light_normalisation,[status(thm)],[c_20539,c_24,c_19867])).

cnf(c_53523,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,X0),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22,c_20942])).

cnf(c_6324,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_24,c_5644])).

cnf(c_55438,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,X0),X1)) = k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,k5_xboole_0(X4,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_53523,c_6324])).

cnf(c_55573,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_55438,c_53523])).

cnf(c_5426,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_1203,c_4264])).

cnf(c_15942,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6137,c_5587])).

cnf(c_15318,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3) = k5_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_5636,c_6010])).

cnf(c_15991,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_15942,c_24,c_15318])).

cnf(c_43133,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_6324,c_15991])).

cnf(c_43598,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_43133])).

cnf(c_55574,plain,
    ( sP0_iProver_split = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_55573,c_22,c_5426,c_43598])).

cnf(c_47,negated_conjecture,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f179])).

cnf(c_59243,plain,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9
    | sP0_iProver_split != sK8 ),
    inference(demodulation,[status(thm)],[c_55574,c_47])).

cnf(c_48,negated_conjecture,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK8
    | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9 ),
    inference(cnf_transformation,[],[f180])).

cnf(c_1224,plain,
    ( ~ r1_tarski(sK8,k4_enumset1(X0,X0,X0,X0,X0,X0))
    | k4_enumset1(X0,X0,X0,X0,X0,X0) = sK8
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_1231,plain,
    ( ~ r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))
    | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = sK8
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_1390,plain,
    ( r1_tarski(sK8,k4_enumset1(X0,X0,X0,X0,X0,X0))
    | k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1392,plain,
    ( r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))
    | k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_2082,plain,
    ( ~ r1_tarski(sK8,k4_enumset1(X0,X0,X0,X0,X0,X0))
    | k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_2083,plain,
    ( k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = k1_xboole_0
    | r1_tarski(sK8,k4_enumset1(X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2082])).

cnf(c_2085,plain,
    ( k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) = k1_xboole_0
    | r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_27951,plain,
    ( k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != k1_xboole_0
    | r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27766,c_19238])).

cnf(c_27962,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_27951,c_25])).

cnf(c_27963,plain,
    ( r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_27962])).

cnf(c_60461,plain,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_59243,c_48,c_47,c_1231,c_1392,c_2085,c_27963])).

cnf(c_73934,plain,
    ( r2_hidden(sK7,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41750,c_48,c_47,c_46,c_1212,c_1231,c_1392,c_2085,c_2836,c_6098,c_19289,c_27963])).

cnf(c_73942,plain,
    ( k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(superposition,[status(thm)],[c_73934,c_1142])).

cnf(c_73943,plain,
    ( k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(light_normalisation,[status(thm)],[c_73942,c_11486])).

cnf(c_6629,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X3,X0)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_24,c_6168])).

cnf(c_6156,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X0,X3)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_24,c_5636])).

cnf(c_16451,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X0,k5_xboole_0(X3,X2))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5140,c_6156])).

cnf(c_15324,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)),X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X4,X3)) ),
    inference(superposition,[status(thm)],[c_6536,c_6010])).

cnf(c_15574,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(demodulation,[status(thm)],[c_15324,c_12146,c_12425,c_13323,c_14088])).

cnf(c_5939,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X3) ),
    inference(superposition,[status(thm)],[c_5009,c_5580])).

cnf(c_5968,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X3) ),
    inference(light_normalisation,[status(thm)],[c_5939,c_24])).

cnf(c_15356,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),k5_xboole_0(X4,k5_xboole_0(X1,X3))) = k5_xboole_0(X4,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5968,c_6010])).

cnf(c_15555,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k5_xboole_0(X4,k5_xboole_0(X2,X3))) = k5_xboole_0(X4,k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_15356,c_12425])).

cnf(c_15576,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X4,k5_xboole_0(X3,X2))) = k5_xboole_0(X4,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_15574,c_15555])).

cnf(c_16885,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X0,k5_xboole_0(X3,X2))) = X1 ),
    inference(demodulation,[status(thm)],[c_16451,c_22,c_15576])).

cnf(c_43888,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,X2)))))),k5_xboole_0(X0,k5_xboole_0(X4,X5))) = X1 ),
    inference(superposition,[status(thm)],[c_6629,c_16885])).

cnf(c_43927,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X5,X4))),X2) ),
    inference(superposition,[status(thm)],[c_16885,c_5968])).

cnf(c_20617,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X1,X3))),X2) ),
    inference(superposition,[status(thm)],[c_6607,c_5968])).

cnf(c_15389,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4)))) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,X4))) ),
    inference(superposition,[status(thm)],[c_5644,c_6010])).

cnf(c_19493,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_25,c_6478])).

cnf(c_20094,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X3,X1))),X4) ),
    inference(superposition,[status(thm)],[c_19493,c_5601])).

cnf(c_5174,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_24,c_5140])).

cnf(c_9080,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_5174])).

cnf(c_10354,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_9080,c_1203])).

cnf(c_10368,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,X3))) ),
    inference(superposition,[status(thm)],[c_9080,c_5587])).

cnf(c_16565,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4))),X5)),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X1,X4),k5_xboole_0(X0,X5)) ),
    inference(superposition,[status(thm)],[c_6156,c_5635])).

cnf(c_16573,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X0),X4) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,X2),X4)) ),
    inference(superposition,[status(thm)],[c_6156,c_5601])).

cnf(c_7510,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X0) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(superposition,[status(thm)],[c_1203,c_7363])).

cnf(c_16622,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
    inference(light_normalisation,[status(thm)],[c_16573,c_7510])).

cnf(c_16623,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
    inference(demodulation,[status(thm)],[c_16622,c_12425,c_15586])).

cnf(c_16629,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X3,X4)),k5_xboole_0(X5,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X5,X4)) ),
    inference(demodulation,[status(thm)],[c_16565,c_16623])).

cnf(c_16630,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X5,k5_xboole_0(X0,X3)))))) = k5_xboole_0(k5_xboole_0(X1,X4),k5_xboole_0(X5,X2)) ),
    inference(demodulation,[status(thm)],[c_16629,c_16623])).

cnf(c_16631,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X0,X3))))))) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X5,X2))) ),
    inference(demodulation,[status(thm)],[c_16630,c_14088,c_15586])).

cnf(c_6007,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0)))) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_1203,c_5587])).

cnf(c_11992,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,X0))))) = k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1202,c_5601])).

cnf(c_16632,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_16631,c_6007,c_11992])).

cnf(c_20128,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X3,X4))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X3,k5_xboole_0(X4,X2))) ),
    inference(demodulation,[status(thm)],[c_20094,c_10354,c_10368,c_16632,c_19671])).

cnf(c_20129,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X4,k5_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_20128,c_15586,c_16632])).

cnf(c_20763,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X4,X5)))) ),
    inference(demodulation,[status(thm)],[c_20617,c_15389,c_19671,c_20129])).

cnf(c_44148,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X3,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_43927,c_20763])).

cnf(c_6669,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,X0),X3)) = k5_xboole_0(X1,X3) ),
    inference(superposition,[status(thm)],[c_6168,c_24])).

cnf(c_43924,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X4)),X0),X5)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X4,X3))),X5) ),
    inference(superposition,[status(thm)],[c_16885,c_6669])).

cnf(c_44152,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X4)),X0),X5)) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X5,k5_xboole_0(X3,X4)))) ),
    inference(demodulation,[status(thm)],[c_43924,c_44148])).

cnf(c_13662,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,X3))) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_5635,c_1])).

cnf(c_36616,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X0),X3)) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_13662,c_6478])).

cnf(c_13918,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X2,X3))) = k5_xboole_0(X1,X3) ),
    inference(superposition,[status(thm)],[c_24,c_5637])).

cnf(c_39216,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X2)),X5)) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X1))),X5) ),
    inference(superposition,[status(thm)],[c_13918,c_5601])).

cnf(c_20619,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X1,X4))),X5)) = k5_xboole_0(X5,k5_xboole_0(X0,k5_xboole_0(X4,k5_xboole_0(X2,X3)))) ),
    inference(superposition,[status(thm)],[c_6607,c_5635])).

cnf(c_14954,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,X2)),X4)) = k5_xboole_0(X4,k5_xboole_0(X3,X0)) ),
    inference(superposition,[status(thm)],[c_5968,c_1202])).

cnf(c_13656,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X3),X4)) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X0,X2)),X4) ),
    inference(superposition,[status(thm)],[c_5635,c_24])).

cnf(c_12233,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_25,c_5612])).

cnf(c_12021,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(superposition,[status(thm)],[c_5580,c_5601])).

cnf(c_12494,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),X1)) = X2 ),
    inference(demodulation,[status(thm)],[c_12233,c_22,c_12021])).

cnf(c_12741,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(X1,X3),X4)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X2),X3),X4) ),
    inference(superposition,[status(thm)],[c_12494,c_5612])).

cnf(c_12814,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X3),X4)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X2),X3),X4) ),
    inference(light_normalisation,[status(thm)],[c_12741,c_24])).

cnf(c_13758,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X3),X4)) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X0),X4)) ),
    inference(demodulation,[status(thm)],[c_13656,c_12425,c_12814])).

cnf(c_14008,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
    inference(superposition,[status(thm)],[c_5637,c_5644])).

cnf(c_15038,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X3,k5_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_14954,c_12425,c_13758,c_14008])).

cnf(c_20759,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)) = k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_20619,c_13729,c_15038,c_19671])).

cnf(c_7348,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X0,X1)) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_24,c_6536])).

cnf(c_23700,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X5)))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X2,X1))),X3) ),
    inference(superposition,[status(thm)],[c_7348,c_5968])).

cnf(c_22151,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X5)))) = k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X1,k5_xboole_0(X2,X4))),X3) ),
    inference(superposition,[status(thm)],[c_6629,c_5968])).

cnf(c_18078,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X5)))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X4,X5)))) ),
    inference(superposition,[status(thm)],[c_6324,c_6010])).

cnf(c_22306,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X5)))) = k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X5,X1)))) ),
    inference(demodulation,[status(thm)],[c_22151,c_18078,c_19671,c_20129])).

cnf(c_23877,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4) = k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X1,X3)))) ),
    inference(light_normalisation,[status(thm)],[c_23700,c_22306])).

cnf(c_23585,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_6324,c_7348])).

cnf(c_22163,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_6629,c_5636])).

cnf(c_24029,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(light_normalisation,[status(thm)],[c_23585,c_22163])).

cnf(c_39325,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X5)))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X4,X5)))) ),
    inference(demodulation,[status(thm)],[c_39216,c_20759,c_23877,c_24029])).

cnf(c_12010,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3) ),
    inference(superposition,[status(thm)],[c_1203,c_5601])).

cnf(c_39326,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X3),X4)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_39325,c_11992,c_12010,c_20759])).

cnf(c_13949,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X2,X0)),X4)) = k5_xboole_0(X1,X4) ),
    inference(superposition,[status(thm)],[c_1202,c_5637])).

cnf(c_13597,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X3,X4)) = k5_xboole_0(X4,k5_xboole_0(X0,k5_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_1202,c_5635])).

cnf(c_14172,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
    inference(demodulation,[status(thm)],[c_13949,c_12425,c_13597])).

cnf(c_14173,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
    inference(light_normalisation,[status(thm)],[c_14172,c_24])).

cnf(c_39809,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X1),X4),X2) ),
    inference(superposition,[status(thm)],[c_5009,c_14173])).

cnf(c_39106,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_5580,c_13918])).

cnf(c_40192,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3))) ),
    inference(light_normalisation,[status(thm)],[c_39809,c_39106])).

cnf(c_44153,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,X3)),k5_xboole_0(X4,X5)))) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X4,X5)))) ),
    inference(demodulation,[status(thm)],[c_44152,c_36616,c_39326,c_40192])).

cnf(c_6045,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X2),X3))) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_5587,c_5009])).

cnf(c_13588,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_5635])).

cnf(c_36513,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X3,X0),X1)) ),
    inference(superposition,[status(thm)],[c_13662,c_13588])).

cnf(c_13351,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_5633,c_1])).

cnf(c_35756,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X3),X1)) ),
    inference(superposition,[status(thm)],[c_13351,c_13588])).

cnf(c_13865,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),X4) ),
    inference(superposition,[status(thm)],[c_5601,c_5637])).

cnf(c_14233,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),X4) ),
    inference(light_normalisation,[status(thm)],[c_13865,c_24])).

cnf(c_14234,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X3,X1),X4)) ),
    inference(demodulation,[status(thm)],[c_14233,c_12425])).

cnf(c_36173,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(X4,k5_xboole_0(X0,k5_xboole_0(X3,X1))) ),
    inference(demodulation,[status(thm)],[c_35756,c_14234,c_15586])).

cnf(c_36681,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,X3))) ),
    inference(light_normalisation,[status(thm)],[c_36513,c_36173])).

cnf(c_36371,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4))),X5))) = k5_xboole_0(k5_xboole_0(X4,X3),k5_xboole_0(X2,X5)) ),
    inference(superposition,[status(thm)],[c_6629,c_13662])).

cnf(c_36815,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),k5_xboole_0(X4,X5)))) = k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X2,X5)) ),
    inference(demodulation,[status(thm)],[c_36371,c_36681])).

cnf(c_36433,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X4)))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4))) ),
    inference(superposition,[status(thm)],[c_1201,c_13662])).

cnf(c_36816,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X2),k5_xboole_0(X3,X4)))) = k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X1,X4)) ),
    inference(demodulation,[status(thm)],[c_36815,c_36433,c_36681])).

cnf(c_36817,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))))) = k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X1,X4)) ),
    inference(demodulation,[status(thm)],[c_36816,c_36681])).

cnf(c_7370,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X0) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_24,c_6536])).

cnf(c_24230,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4)))),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X4,X2)))) ),
    inference(superposition,[status(thm)],[c_19493,c_7370])).

cnf(c_24517,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X3)) ),
    inference(demodulation,[status(thm)],[c_24230,c_7370])).

cnf(c_20096,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X1)),X0) ),
    inference(superposition,[status(thm)],[c_19493,c_5580])).

cnf(c_20127,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0))) ),
    inference(demodulation,[status(thm)],[c_20096,c_10368,c_19671])).

cnf(c_24518,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(light_normalisation,[status(thm)],[c_24517,c_20127])).

cnf(c_24133,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))))) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(superposition,[status(thm)],[c_6137,c_7370])).

cnf(c_15925,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_6137,c_6536])).

cnf(c_24634,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))))) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_24133,c_15586,c_15925])).

cnf(c_36818,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,X1))) ),
    inference(demodulation,[status(thm)],[c_36817,c_24518,c_24634])).

cnf(c_44154,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = k5_xboole_0(X0,k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_44153,c_6045,c_36681,c_36818])).

cnf(c_44246,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,X3)),k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X5,k5_xboole_0(X5,X2))),X4)))) = X1 ),
    inference(demodulation,[status(thm)],[c_43888,c_44148,c_44154])).

cnf(c_43901,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))),X5))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X4,X3)),k5_xboole_0(X1,X5)) ),
    inference(superposition,[status(thm)],[c_16885,c_13662])).

cnf(c_44200,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5)))))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X4,X5)),k5_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_43901,c_44148])).

cnf(c_16527,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X3,X4)),X5)) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,X4))),X5) ),
    inference(superposition,[status(thm)],[c_6156,c_5637])).

cnf(c_16721,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),k5_xboole_0(k5_xboole_0(X3,X4),X5))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X1,X5)))) ),
    inference(demodulation,[status(thm)],[c_16527,c_16623,c_16632])).

cnf(c_16722,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X3),k5_xboole_0(X4,X5))))) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_16721,c_16632])).

cnf(c_16723,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5)))))) = k5_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_16722,c_16632])).

cnf(c_44201,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)) = k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X3,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_44200,c_16723])).

cnf(c_44247,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X5,k5_xboole_0(X5,X4))),X0)))))) = X1 ),
    inference(demodulation,[status(thm)],[c_44246,c_44201])).

cnf(c_44248,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X5,k5_xboole_0(X0,k5_xboole_0(X4,X5))))))))) = X1 ),
    inference(demodulation,[status(thm)],[c_44247,c_44148])).

cnf(c_44249,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(X3,k5_xboole_0(X5,X0))))))))) = X1 ),
    inference(demodulation,[status(thm)],[c_44248,c_44154])).

cnf(c_43957,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X3,X2),X1) ),
    inference(superposition,[status(thm)],[c_16885,c_6536])).

cnf(c_44250,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X3,X4)),X0),X2))))) = X1 ),
    inference(demodulation,[status(thm)],[c_44249,c_43957,c_44154])).

cnf(c_7412,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_6536,c_24])).

cnf(c_10337,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_7412,c_9080])).

cnf(c_10415,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),X0))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_10337,c_9080])).

cnf(c_24303,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X3,X4))))) = k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_7370,c_1203])).

cnf(c_44251,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2))) = X0 ),
    inference(demodulation,[status(thm)],[c_44250,c_10415,c_24303])).

cnf(c_44252,plain,
    ( k5_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_44251,c_36681,c_43598])).

cnf(c_55325,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X4))))),k5_xboole_0(X4,X3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20942,c_53523])).

cnf(c_19498,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_24,c_6478])).

cnf(c_55347,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X1),X2),X4) ),
    inference(superposition,[status(thm)],[c_53523,c_19498])).

cnf(c_55845,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X1),X2),X4) ),
    inference(light_normalisation,[status(thm)],[c_55347,c_22])).

cnf(c_43985,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X3,X2),X1) ),
    inference(superposition,[status(thm)],[c_16885,c_5580])).

cnf(c_55846,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0))) ),
    inference(demodulation,[status(thm)],[c_55845,c_5916,c_36681,c_40192,c_43985])).

cnf(c_55931,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4))),k5_xboole_0(X3,X1))),k5_xboole_0(X4,k5_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_55325,c_55846])).

cnf(c_55932,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X3,X3))),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X4,X0),X4))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_55931,c_55846])).

cnf(c_55933,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),X2)),k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,X2),X4),k5_xboole_0(X0,X3)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_55932,c_55846])).

cnf(c_55934,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,X1)))),X4))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_55933,c_55846])).

cnf(c_55935,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,X0)))),X3))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_55934,c_25,c_55574])).

cnf(c_12110,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3))),X4)) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,X2),X4)) ),
    inference(superposition,[status(thm)],[c_5601,c_5009])).

cnf(c_12238,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(superposition,[status(thm)],[c_24,c_5612])).

cnf(c_20558,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X3,k5_xboole_0(X1,X0))) = X2 ),
    inference(superposition,[status(thm)],[c_1,c_6607])).

cnf(c_52482,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X4,k5_xboole_0(X1,X3))),X2) ),
    inference(superposition,[status(thm)],[c_20558,c_5968])).

cnf(c_52541,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3),X4) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X2,X4)) ),
    inference(superposition,[status(thm)],[c_20558,c_5601])).

cnf(c_20478,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = X3 ),
    inference(superposition,[status(thm)],[c_1,c_6607])).

cnf(c_48836,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_20478,c_5644])).

cnf(c_52678,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X0)),X3) ),
    inference(light_normalisation,[status(thm)],[c_52541,c_48836])).

cnf(c_45210,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X2))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X4)),X3) ),
    inference(superposition,[status(thm)],[c_19498,c_5580])).

cnf(c_43173,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X2))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X3,X4),X1)) ),
    inference(superposition,[status(thm)],[c_6010,c_15991])).

cnf(c_39911,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X2))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4))) ),
    inference(superposition,[status(thm)],[c_14173,c_5587])).

cnf(c_43571,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X2))) = k5_xboole_0(X0,k5_xboole_0(X4,k5_xboole_0(X3,X1))) ),
    inference(demodulation,[status(thm)],[c_43173,c_36681,c_39911])).

cnf(c_45335,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X3,X1))) ),
    inference(light_normalisation,[status(thm)],[c_45210,c_43571])).

cnf(c_52679,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,X0))) ),
    inference(demodulation,[status(thm)],[c_52678,c_24518,c_45335])).

cnf(c_52749,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(k5_xboole_0(X1,X3),k5_xboole_0(X4,k5_xboole_0(X2,X5))) ),
    inference(demodulation,[status(thm)],[c_52482,c_52679])).

cnf(c_52750,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X2,X4)))) ),
    inference(light_normalisation,[status(thm)],[c_52749,c_20763])).

cnf(c_55936,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_55935,c_1499,c_12110,c_12238,c_52750])).

cnf(c_55937,plain,
    ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_55936,c_1703])).

cnf(c_73944,plain,
    ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = sK9 ),
    inference(demodulation,[status(thm)],[c_73943,c_44252,c_55937])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73944,c_60461])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.83/4.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.83/4.51  
% 31.83/4.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.83/4.51  
% 31.83/4.51  ------  iProver source info
% 31.83/4.51  
% 31.83/4.51  git: date: 2020-06-30 10:37:57 +0100
% 31.83/4.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.83/4.51  git: non_committed_changes: false
% 31.83/4.51  git: last_make_outside_of_git: false
% 31.83/4.51  
% 31.83/4.51  ------ 
% 31.83/4.51  
% 31.83/4.51  ------ Input Options
% 31.83/4.51  
% 31.83/4.51  --out_options                           all
% 31.83/4.51  --tptp_safe_out                         true
% 31.83/4.51  --problem_path                          ""
% 31.83/4.51  --include_path                          ""
% 31.83/4.51  --clausifier                            res/vclausify_rel
% 31.83/4.51  --clausifier_options                    ""
% 31.83/4.51  --stdin                                 false
% 31.83/4.51  --stats_out                             all
% 31.83/4.51  
% 31.83/4.51  ------ General Options
% 31.83/4.51  
% 31.83/4.51  --fof                                   false
% 31.83/4.51  --time_out_real                         305.
% 31.83/4.51  --time_out_virtual                      -1.
% 31.83/4.51  --symbol_type_check                     false
% 31.83/4.51  --clausify_out                          false
% 31.83/4.51  --sig_cnt_out                           false
% 31.83/4.51  --trig_cnt_out                          false
% 31.83/4.51  --trig_cnt_out_tolerance                1.
% 31.83/4.51  --trig_cnt_out_sk_spl                   false
% 31.83/4.51  --abstr_cl_out                          false
% 31.83/4.51  
% 31.83/4.51  ------ Global Options
% 31.83/4.51  
% 31.83/4.51  --schedule                              default
% 31.83/4.51  --add_important_lit                     false
% 31.83/4.51  --prop_solver_per_cl                    1000
% 31.83/4.51  --min_unsat_core                        false
% 31.83/4.51  --soft_assumptions                      false
% 31.83/4.51  --soft_lemma_size                       3
% 31.83/4.51  --prop_impl_unit_size                   0
% 31.83/4.51  --prop_impl_unit                        []
% 31.83/4.51  --share_sel_clauses                     true
% 31.83/4.51  --reset_solvers                         false
% 31.83/4.51  --bc_imp_inh                            [conj_cone]
% 31.83/4.51  --conj_cone_tolerance                   3.
% 31.83/4.51  --extra_neg_conj                        none
% 31.83/4.51  --large_theory_mode                     true
% 31.83/4.51  --prolific_symb_bound                   200
% 31.83/4.51  --lt_threshold                          2000
% 31.83/4.51  --clause_weak_htbl                      true
% 31.83/4.51  --gc_record_bc_elim                     false
% 31.83/4.51  
% 31.83/4.51  ------ Preprocessing Options
% 31.83/4.51  
% 31.83/4.51  --preprocessing_flag                    true
% 31.83/4.51  --time_out_prep_mult                    0.1
% 31.83/4.51  --splitting_mode                        input
% 31.83/4.51  --splitting_grd                         true
% 31.83/4.51  --splitting_cvd                         false
% 31.83/4.51  --splitting_cvd_svl                     false
% 31.83/4.51  --splitting_nvd                         32
% 31.83/4.51  --sub_typing                            true
% 31.83/4.51  --prep_gs_sim                           true
% 31.83/4.51  --prep_unflatten                        true
% 31.83/4.51  --prep_res_sim                          true
% 31.83/4.51  --prep_upred                            true
% 31.83/4.51  --prep_sem_filter                       exhaustive
% 31.83/4.51  --prep_sem_filter_out                   false
% 31.83/4.51  --pred_elim                             true
% 31.83/4.51  --res_sim_input                         true
% 31.83/4.51  --eq_ax_congr_red                       true
% 31.83/4.51  --pure_diseq_elim                       true
% 31.83/4.51  --brand_transform                       false
% 31.83/4.51  --non_eq_to_eq                          false
% 31.83/4.51  --prep_def_merge                        true
% 31.83/4.51  --prep_def_merge_prop_impl              false
% 31.83/4.51  --prep_def_merge_mbd                    true
% 31.83/4.51  --prep_def_merge_tr_red                 false
% 31.83/4.51  --prep_def_merge_tr_cl                  false
% 31.83/4.51  --smt_preprocessing                     true
% 31.83/4.51  --smt_ac_axioms                         fast
% 31.83/4.51  --preprocessed_out                      false
% 31.83/4.51  --preprocessed_stats                    false
% 31.83/4.51  
% 31.83/4.51  ------ Abstraction refinement Options
% 31.83/4.51  
% 31.83/4.51  --abstr_ref                             []
% 31.83/4.51  --abstr_ref_prep                        false
% 31.83/4.51  --abstr_ref_until_sat                   false
% 31.83/4.51  --abstr_ref_sig_restrict                funpre
% 31.83/4.51  --abstr_ref_af_restrict_to_split_sk     false
% 31.83/4.51  --abstr_ref_under                       []
% 31.83/4.51  
% 31.83/4.51  ------ SAT Options
% 31.83/4.51  
% 31.83/4.51  --sat_mode                              false
% 31.83/4.51  --sat_fm_restart_options                ""
% 31.83/4.51  --sat_gr_def                            false
% 31.83/4.51  --sat_epr_types                         true
% 31.83/4.51  --sat_non_cyclic_types                  false
% 31.83/4.51  --sat_finite_models                     false
% 31.83/4.51  --sat_fm_lemmas                         false
% 31.83/4.51  --sat_fm_prep                           false
% 31.83/4.51  --sat_fm_uc_incr                        true
% 31.83/4.51  --sat_out_model                         small
% 31.83/4.51  --sat_out_clauses                       false
% 31.83/4.51  
% 31.83/4.51  ------ QBF Options
% 31.83/4.51  
% 31.83/4.51  --qbf_mode                              false
% 31.83/4.51  --qbf_elim_univ                         false
% 31.83/4.51  --qbf_dom_inst                          none
% 31.83/4.51  --qbf_dom_pre_inst                      false
% 31.83/4.51  --qbf_sk_in                             false
% 31.83/4.51  --qbf_pred_elim                         true
% 31.83/4.51  --qbf_split                             512
% 31.83/4.51  
% 31.83/4.51  ------ BMC1 Options
% 31.83/4.51  
% 31.83/4.51  --bmc1_incremental                      false
% 31.83/4.51  --bmc1_axioms                           reachable_all
% 31.83/4.51  --bmc1_min_bound                        0
% 31.83/4.51  --bmc1_max_bound                        -1
% 31.83/4.51  --bmc1_max_bound_default                -1
% 31.83/4.51  --bmc1_symbol_reachability              true
% 31.83/4.51  --bmc1_property_lemmas                  false
% 31.83/4.51  --bmc1_k_induction                      false
% 31.83/4.51  --bmc1_non_equiv_states                 false
% 31.83/4.51  --bmc1_deadlock                         false
% 31.83/4.51  --bmc1_ucm                              false
% 31.83/4.51  --bmc1_add_unsat_core                   none
% 31.83/4.51  --bmc1_unsat_core_children              false
% 31.83/4.51  --bmc1_unsat_core_extrapolate_axioms    false
% 31.83/4.51  --bmc1_out_stat                         full
% 31.83/4.51  --bmc1_ground_init                      false
% 31.83/4.51  --bmc1_pre_inst_next_state              false
% 31.83/4.51  --bmc1_pre_inst_state                   false
% 31.83/4.51  --bmc1_pre_inst_reach_state             false
% 31.83/4.51  --bmc1_out_unsat_core                   false
% 31.83/4.51  --bmc1_aig_witness_out                  false
% 31.83/4.51  --bmc1_verbose                          false
% 31.83/4.51  --bmc1_dump_clauses_tptp                false
% 31.83/4.51  --bmc1_dump_unsat_core_tptp             false
% 31.83/4.51  --bmc1_dump_file                        -
% 31.83/4.51  --bmc1_ucm_expand_uc_limit              128
% 31.83/4.51  --bmc1_ucm_n_expand_iterations          6
% 31.83/4.51  --bmc1_ucm_extend_mode                  1
% 31.83/4.51  --bmc1_ucm_init_mode                    2
% 31.83/4.51  --bmc1_ucm_cone_mode                    none
% 31.83/4.51  --bmc1_ucm_reduced_relation_type        0
% 31.83/4.51  --bmc1_ucm_relax_model                  4
% 31.83/4.51  --bmc1_ucm_full_tr_after_sat            true
% 31.83/4.51  --bmc1_ucm_expand_neg_assumptions       false
% 31.83/4.51  --bmc1_ucm_layered_model                none
% 31.83/4.51  --bmc1_ucm_max_lemma_size               10
% 31.83/4.51  
% 31.83/4.51  ------ AIG Options
% 31.83/4.51  
% 31.83/4.51  --aig_mode                              false
% 31.83/4.51  
% 31.83/4.51  ------ Instantiation Options
% 31.83/4.51  
% 31.83/4.51  --instantiation_flag                    true
% 31.83/4.51  --inst_sos_flag                         true
% 31.83/4.51  --inst_sos_phase                        true
% 31.83/4.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.83/4.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.83/4.51  --inst_lit_sel_side                     num_symb
% 31.83/4.51  --inst_solver_per_active                1400
% 31.83/4.51  --inst_solver_calls_frac                1.
% 31.83/4.51  --inst_passive_queue_type               priority_queues
% 31.83/4.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.83/4.51  --inst_passive_queues_freq              [25;2]
% 31.83/4.51  --inst_dismatching                      true
% 31.83/4.51  --inst_eager_unprocessed_to_passive     true
% 31.83/4.51  --inst_prop_sim_given                   true
% 31.83/4.51  --inst_prop_sim_new                     false
% 31.83/4.51  --inst_subs_new                         false
% 31.83/4.51  --inst_eq_res_simp                      false
% 31.83/4.51  --inst_subs_given                       false
% 31.83/4.51  --inst_orphan_elimination               true
% 31.83/4.51  --inst_learning_loop_flag               true
% 31.83/4.51  --inst_learning_start                   3000
% 31.83/4.51  --inst_learning_factor                  2
% 31.83/4.51  --inst_start_prop_sim_after_learn       3
% 31.83/4.51  --inst_sel_renew                        solver
% 31.83/4.51  --inst_lit_activity_flag                true
% 31.83/4.51  --inst_restr_to_given                   false
% 31.83/4.51  --inst_activity_threshold               500
% 31.83/4.51  --inst_out_proof                        true
% 31.83/4.51  
% 31.83/4.51  ------ Resolution Options
% 31.83/4.51  
% 31.83/4.51  --resolution_flag                       true
% 31.83/4.51  --res_lit_sel                           adaptive
% 31.83/4.51  --res_lit_sel_side                      none
% 31.83/4.51  --res_ordering                          kbo
% 31.83/4.51  --res_to_prop_solver                    active
% 31.83/4.51  --res_prop_simpl_new                    false
% 31.83/4.51  --res_prop_simpl_given                  true
% 31.83/4.51  --res_passive_queue_type                priority_queues
% 31.83/4.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.83/4.51  --res_passive_queues_freq               [15;5]
% 31.83/4.51  --res_forward_subs                      full
% 31.83/4.51  --res_backward_subs                     full
% 31.83/4.51  --res_forward_subs_resolution           true
% 31.83/4.51  --res_backward_subs_resolution          true
% 31.83/4.51  --res_orphan_elimination                true
% 31.83/4.51  --res_time_limit                        2.
% 31.83/4.51  --res_out_proof                         true
% 31.83/4.51  
% 31.83/4.51  ------ Superposition Options
% 31.83/4.51  
% 31.83/4.51  --superposition_flag                    true
% 31.83/4.51  --sup_passive_queue_type                priority_queues
% 31.83/4.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.83/4.51  --sup_passive_queues_freq               [8;1;4]
% 31.83/4.51  --demod_completeness_check              fast
% 31.83/4.51  --demod_use_ground                      true
% 31.83/4.51  --sup_to_prop_solver                    passive
% 31.83/4.51  --sup_prop_simpl_new                    true
% 31.83/4.51  --sup_prop_simpl_given                  true
% 31.83/4.51  --sup_fun_splitting                     true
% 31.83/4.51  --sup_smt_interval                      50000
% 31.83/4.51  
% 31.83/4.51  ------ Superposition Simplification Setup
% 31.83/4.51  
% 31.83/4.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.83/4.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.83/4.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.83/4.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.83/4.51  --sup_full_triv                         [TrivRules;PropSubs]
% 31.83/4.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.83/4.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.83/4.51  --sup_immed_triv                        [TrivRules]
% 31.83/4.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.83/4.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.83/4.51  --sup_immed_bw_main                     []
% 31.83/4.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.83/4.51  --sup_input_triv                        [Unflattening;TrivRules]
% 31.83/4.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.83/4.51  --sup_input_bw                          []
% 31.83/4.51  
% 31.83/4.51  ------ Combination Options
% 31.83/4.51  
% 31.83/4.51  --comb_res_mult                         3
% 31.83/4.51  --comb_sup_mult                         2
% 31.83/4.51  --comb_inst_mult                        10
% 31.83/4.51  
% 31.83/4.51  ------ Debug Options
% 31.83/4.51  
% 31.83/4.51  --dbg_backtrace                         false
% 31.83/4.51  --dbg_dump_prop_clauses                 false
% 31.83/4.51  --dbg_dump_prop_clauses_file            -
% 31.83/4.51  --dbg_out_stat                          false
% 31.83/4.51  ------ Parsing...
% 31.83/4.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.83/4.51  
% 31.83/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.83/4.51  
% 31.83/4.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.83/4.51  
% 31.83/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.83/4.51  ------ Proving...
% 31.83/4.51  ------ Problem Properties 
% 31.83/4.51  
% 31.83/4.51  
% 31.83/4.51  clauses                                 50
% 31.83/4.51  conjectures                             4
% 31.83/4.51  EPR                                     0
% 31.83/4.51  Horn                                    40
% 31.83/4.51  unary                                   19
% 31.83/4.51  binary                                  16
% 31.83/4.51  lits                                    99
% 31.83/4.51  lits eq                                 46
% 31.83/4.51  fd_pure                                 0
% 31.83/4.51  fd_pseudo                               0
% 31.83/4.51  fd_cond                                 2
% 31.83/4.51  fd_pseudo_cond                          13
% 31.83/4.51  AC symbols                              1
% 31.83/4.51  
% 31.83/4.51  ------ Schedule dynamic 5 is on 
% 31.83/4.51  
% 31.83/4.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.83/4.51  
% 31.83/4.51  
% 31.83/4.51  ------ 
% 31.83/4.51  Current options:
% 31.83/4.51  ------ 
% 31.83/4.51  
% 31.83/4.51  ------ Input Options
% 31.83/4.51  
% 31.83/4.51  --out_options                           all
% 31.83/4.51  --tptp_safe_out                         true
% 31.83/4.51  --problem_path                          ""
% 31.83/4.51  --include_path                          ""
% 31.83/4.51  --clausifier                            res/vclausify_rel
% 31.83/4.51  --clausifier_options                    ""
% 31.83/4.51  --stdin                                 false
% 31.83/4.51  --stats_out                             all
% 31.83/4.51  
% 31.83/4.51  ------ General Options
% 31.83/4.51  
% 31.83/4.51  --fof                                   false
% 31.83/4.51  --time_out_real                         305.
% 31.83/4.51  --time_out_virtual                      -1.
% 31.83/4.51  --symbol_type_check                     false
% 31.83/4.51  --clausify_out                          false
% 31.83/4.51  --sig_cnt_out                           false
% 31.83/4.51  --trig_cnt_out                          false
% 31.83/4.51  --trig_cnt_out_tolerance                1.
% 31.83/4.51  --trig_cnt_out_sk_spl                   false
% 31.83/4.51  --abstr_cl_out                          false
% 31.83/4.51  
% 31.83/4.51  ------ Global Options
% 31.83/4.51  
% 31.83/4.51  --schedule                              default
% 31.83/4.51  --add_important_lit                     false
% 31.83/4.51  --prop_solver_per_cl                    1000
% 31.83/4.51  --min_unsat_core                        false
% 31.83/4.51  --soft_assumptions                      false
% 31.83/4.51  --soft_lemma_size                       3
% 31.83/4.51  --prop_impl_unit_size                   0
% 31.83/4.51  --prop_impl_unit                        []
% 31.83/4.51  --share_sel_clauses                     true
% 31.83/4.51  --reset_solvers                         false
% 31.83/4.51  --bc_imp_inh                            [conj_cone]
% 31.83/4.51  --conj_cone_tolerance                   3.
% 31.83/4.51  --extra_neg_conj                        none
% 31.83/4.51  --large_theory_mode                     true
% 31.83/4.51  --prolific_symb_bound                   200
% 31.83/4.51  --lt_threshold                          2000
% 31.83/4.51  --clause_weak_htbl                      true
% 31.83/4.51  --gc_record_bc_elim                     false
% 31.83/4.51  
% 31.83/4.51  ------ Preprocessing Options
% 31.83/4.51  
% 31.83/4.51  --preprocessing_flag                    true
% 31.83/4.51  --time_out_prep_mult                    0.1
% 31.83/4.51  --splitting_mode                        input
% 31.83/4.51  --splitting_grd                         true
% 31.83/4.51  --splitting_cvd                         false
% 31.83/4.51  --splitting_cvd_svl                     false
% 31.83/4.51  --splitting_nvd                         32
% 31.83/4.51  --sub_typing                            true
% 31.83/4.51  --prep_gs_sim                           true
% 31.83/4.51  --prep_unflatten                        true
% 31.83/4.51  --prep_res_sim                          true
% 31.83/4.51  --prep_upred                            true
% 31.83/4.51  --prep_sem_filter                       exhaustive
% 31.83/4.51  --prep_sem_filter_out                   false
% 31.83/4.51  --pred_elim                             true
% 31.83/4.51  --res_sim_input                         true
% 31.83/4.51  --eq_ax_congr_red                       true
% 31.83/4.51  --pure_diseq_elim                       true
% 31.83/4.51  --brand_transform                       false
% 31.83/4.51  --non_eq_to_eq                          false
% 31.83/4.51  --prep_def_merge                        true
% 31.83/4.51  --prep_def_merge_prop_impl              false
% 31.83/4.51  --prep_def_merge_mbd                    true
% 31.83/4.51  --prep_def_merge_tr_red                 false
% 31.83/4.51  --prep_def_merge_tr_cl                  false
% 31.83/4.51  --smt_preprocessing                     true
% 31.83/4.51  --smt_ac_axioms                         fast
% 31.83/4.51  --preprocessed_out                      false
% 31.83/4.51  --preprocessed_stats                    false
% 31.83/4.51  
% 31.83/4.51  ------ Abstraction refinement Options
% 31.83/4.51  
% 31.83/4.51  --abstr_ref                             []
% 31.83/4.51  --abstr_ref_prep                        false
% 31.83/4.51  --abstr_ref_until_sat                   false
% 31.83/4.51  --abstr_ref_sig_restrict                funpre
% 31.83/4.51  --abstr_ref_af_restrict_to_split_sk     false
% 31.83/4.51  --abstr_ref_under                       []
% 31.83/4.51  
% 31.83/4.51  ------ SAT Options
% 31.83/4.51  
% 31.83/4.51  --sat_mode                              false
% 31.83/4.51  --sat_fm_restart_options                ""
% 31.83/4.51  --sat_gr_def                            false
% 31.83/4.51  --sat_epr_types                         true
% 31.83/4.51  --sat_non_cyclic_types                  false
% 31.83/4.51  --sat_finite_models                     false
% 31.83/4.51  --sat_fm_lemmas                         false
% 31.83/4.51  --sat_fm_prep                           false
% 31.83/4.51  --sat_fm_uc_incr                        true
% 31.83/4.51  --sat_out_model                         small
% 31.83/4.51  --sat_out_clauses                       false
% 31.83/4.51  
% 31.83/4.51  ------ QBF Options
% 31.83/4.51  
% 31.83/4.51  --qbf_mode                              false
% 31.83/4.51  --qbf_elim_univ                         false
% 31.83/4.51  --qbf_dom_inst                          none
% 31.83/4.51  --qbf_dom_pre_inst                      false
% 31.83/4.51  --qbf_sk_in                             false
% 31.83/4.51  --qbf_pred_elim                         true
% 31.83/4.51  --qbf_split                             512
% 31.83/4.51  
% 31.83/4.51  ------ BMC1 Options
% 31.83/4.51  
% 31.83/4.51  --bmc1_incremental                      false
% 31.83/4.51  --bmc1_axioms                           reachable_all
% 31.83/4.51  --bmc1_min_bound                        0
% 31.83/4.51  --bmc1_max_bound                        -1
% 31.83/4.51  --bmc1_max_bound_default                -1
% 31.83/4.51  --bmc1_symbol_reachability              true
% 31.83/4.51  --bmc1_property_lemmas                  false
% 31.83/4.51  --bmc1_k_induction                      false
% 31.83/4.51  --bmc1_non_equiv_states                 false
% 31.83/4.51  --bmc1_deadlock                         false
% 31.83/4.51  --bmc1_ucm                              false
% 31.83/4.51  --bmc1_add_unsat_core                   none
% 31.83/4.51  --bmc1_unsat_core_children              false
% 31.83/4.51  --bmc1_unsat_core_extrapolate_axioms    false
% 31.83/4.51  --bmc1_out_stat                         full
% 31.83/4.51  --bmc1_ground_init                      false
% 31.83/4.51  --bmc1_pre_inst_next_state              false
% 31.83/4.51  --bmc1_pre_inst_state                   false
% 31.83/4.51  --bmc1_pre_inst_reach_state             false
% 31.83/4.51  --bmc1_out_unsat_core                   false
% 31.83/4.51  --bmc1_aig_witness_out                  false
% 31.83/4.51  --bmc1_verbose                          false
% 31.83/4.51  --bmc1_dump_clauses_tptp                false
% 31.83/4.51  --bmc1_dump_unsat_core_tptp             false
% 31.83/4.51  --bmc1_dump_file                        -
% 31.83/4.51  --bmc1_ucm_expand_uc_limit              128
% 31.83/4.51  --bmc1_ucm_n_expand_iterations          6
% 31.83/4.51  --bmc1_ucm_extend_mode                  1
% 31.83/4.51  --bmc1_ucm_init_mode                    2
% 31.83/4.51  --bmc1_ucm_cone_mode                    none
% 31.83/4.51  --bmc1_ucm_reduced_relation_type        0
% 31.83/4.51  --bmc1_ucm_relax_model                  4
% 31.83/4.51  --bmc1_ucm_full_tr_after_sat            true
% 31.83/4.51  --bmc1_ucm_expand_neg_assumptions       false
% 31.83/4.51  --bmc1_ucm_layered_model                none
% 31.83/4.51  --bmc1_ucm_max_lemma_size               10
% 31.83/4.51  
% 31.83/4.51  ------ AIG Options
% 31.83/4.51  
% 31.83/4.51  --aig_mode                              false
% 31.83/4.51  
% 31.83/4.51  ------ Instantiation Options
% 31.83/4.51  
% 31.83/4.51  --instantiation_flag                    true
% 31.83/4.51  --inst_sos_flag                         true
% 31.83/4.51  --inst_sos_phase                        true
% 31.83/4.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.83/4.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.83/4.51  --inst_lit_sel_side                     none
% 31.83/4.51  --inst_solver_per_active                1400
% 31.83/4.51  --inst_solver_calls_frac                1.
% 31.83/4.51  --inst_passive_queue_type               priority_queues
% 31.83/4.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.83/4.51  --inst_passive_queues_freq              [25;2]
% 31.83/4.51  --inst_dismatching                      true
% 31.83/4.51  --inst_eager_unprocessed_to_passive     true
% 31.83/4.51  --inst_prop_sim_given                   true
% 31.83/4.51  --inst_prop_sim_new                     false
% 31.83/4.51  --inst_subs_new                         false
% 31.83/4.51  --inst_eq_res_simp                      false
% 31.83/4.51  --inst_subs_given                       false
% 31.83/4.51  --inst_orphan_elimination               true
% 31.83/4.51  --inst_learning_loop_flag               true
% 31.83/4.51  --inst_learning_start                   3000
% 31.83/4.51  --inst_learning_factor                  2
% 31.83/4.51  --inst_start_prop_sim_after_learn       3
% 31.83/4.51  --inst_sel_renew                        solver
% 31.83/4.51  --inst_lit_activity_flag                true
% 31.83/4.51  --inst_restr_to_given                   false
% 31.83/4.51  --inst_activity_threshold               500
% 31.83/4.51  --inst_out_proof                        true
% 31.83/4.51  
% 31.83/4.51  ------ Resolution Options
% 31.83/4.51  
% 31.83/4.51  --resolution_flag                       false
% 31.83/4.51  --res_lit_sel                           adaptive
% 31.83/4.51  --res_lit_sel_side                      none
% 31.83/4.51  --res_ordering                          kbo
% 31.83/4.51  --res_to_prop_solver                    active
% 31.83/4.51  --res_prop_simpl_new                    false
% 31.83/4.51  --res_prop_simpl_given                  true
% 31.83/4.51  --res_passive_queue_type                priority_queues
% 31.83/4.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.83/4.51  --res_passive_queues_freq               [15;5]
% 31.83/4.51  --res_forward_subs                      full
% 31.83/4.51  --res_backward_subs                     full
% 31.83/4.51  --res_forward_subs_resolution           true
% 31.83/4.51  --res_backward_subs_resolution          true
% 31.83/4.51  --res_orphan_elimination                true
% 31.83/4.51  --res_time_limit                        2.
% 31.83/4.51  --res_out_proof                         true
% 31.83/4.51  
% 31.83/4.51  ------ Superposition Options
% 31.83/4.51  
% 31.83/4.51  --superposition_flag                    true
% 31.83/4.51  --sup_passive_queue_type                priority_queues
% 31.83/4.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.83/4.51  --sup_passive_queues_freq               [8;1;4]
% 31.83/4.51  --demod_completeness_check              fast
% 31.83/4.51  --demod_use_ground                      true
% 31.83/4.51  --sup_to_prop_solver                    passive
% 31.83/4.51  --sup_prop_simpl_new                    true
% 31.83/4.51  --sup_prop_simpl_given                  true
% 31.83/4.51  --sup_fun_splitting                     true
% 31.83/4.51  --sup_smt_interval                      50000
% 31.83/4.51  
% 31.83/4.51  ------ Superposition Simplification Setup
% 31.83/4.51  
% 31.83/4.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.83/4.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.83/4.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.83/4.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.83/4.51  --sup_full_triv                         [TrivRules;PropSubs]
% 31.83/4.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.83/4.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.83/4.51  --sup_immed_triv                        [TrivRules]
% 31.83/4.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.83/4.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.83/4.51  --sup_immed_bw_main                     []
% 31.83/4.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.83/4.51  --sup_input_triv                        [Unflattening;TrivRules]
% 31.83/4.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.83/4.51  --sup_input_bw                          []
% 31.83/4.51  
% 31.83/4.51  ------ Combination Options
% 31.83/4.51  
% 31.83/4.51  --comb_res_mult                         3
% 31.83/4.51  --comb_sup_mult                         2
% 31.83/4.51  --comb_inst_mult                        10
% 31.83/4.51  
% 31.83/4.51  ------ Debug Options
% 31.83/4.51  
% 31.83/4.51  --dbg_backtrace                         false
% 31.83/4.51  --dbg_dump_prop_clauses                 false
% 31.83/4.51  --dbg_dump_prop_clauses_file            -
% 31.83/4.51  --dbg_out_stat                          false
% 31.83/4.51  
% 31.83/4.51  
% 31.83/4.51  
% 31.83/4.51  
% 31.83/4.51  ------ Proving...
% 31.83/4.51  
% 31.83/4.51  
% 31.83/4.51  % SZS status Theorem for theBenchmark.p
% 31.83/4.51  
% 31.83/4.51  % SZS output start CNFRefutation for theBenchmark.p
% 31.83/4.51  
% 31.83/4.51  fof(f17,axiom,(
% 31.83/4.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f57,plain,(
% 31.83/4.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 31.83/4.51    inference(nnf_transformation,[],[f17])).
% 31.83/4.51  
% 31.83/4.51  fof(f58,plain,(
% 31.83/4.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 31.83/4.51    inference(rectify,[],[f57])).
% 31.83/4.51  
% 31.83/4.51  fof(f59,plain,(
% 31.83/4.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 31.83/4.51    introduced(choice_axiom,[])).
% 31.83/4.51  
% 31.83/4.51  fof(f60,plain,(
% 31.83/4.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 31.83/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).
% 31.83/4.51  
% 31.83/4.51  fof(f100,plain,(
% 31.83/4.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 31.83/4.51    inference(cnf_transformation,[],[f60])).
% 31.83/4.51  
% 31.83/4.51  fof(f24,axiom,(
% 31.83/4.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f109,plain,(
% 31.83/4.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f24])).
% 31.83/4.51  
% 31.83/4.51  fof(f25,axiom,(
% 31.83/4.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f110,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f25])).
% 31.83/4.51  
% 31.83/4.51  fof(f26,axiom,(
% 31.83/4.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f111,plain,(
% 31.83/4.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f26])).
% 31.83/4.51  
% 31.83/4.51  fof(f27,axiom,(
% 31.83/4.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f112,plain,(
% 31.83/4.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f27])).
% 31.83/4.51  
% 31.83/4.51  fof(f28,axiom,(
% 31.83/4.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f113,plain,(
% 31.83/4.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f28])).
% 31.83/4.51  
% 31.83/4.51  fof(f133,plain,(
% 31.83/4.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 31.83/4.51    inference(definition_unfolding,[],[f112,f113])).
% 31.83/4.51  
% 31.83/4.51  fof(f134,plain,(
% 31.83/4.51    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 31.83/4.51    inference(definition_unfolding,[],[f111,f133])).
% 31.83/4.51  
% 31.83/4.51  fof(f135,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 31.83/4.51    inference(definition_unfolding,[],[f110,f134])).
% 31.83/4.51  
% 31.83/4.51  fof(f139,plain,(
% 31.83/4.51    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 31.83/4.51    inference(definition_unfolding,[],[f109,f135])).
% 31.83/4.51  
% 31.83/4.51  fof(f166,plain,(
% 31.83/4.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k4_enumset1(X0,X0,X0,X0,X0,X0) != X1) )),
% 31.83/4.51    inference(definition_unfolding,[],[f100,f139])).
% 31.83/4.51  
% 31.83/4.51  fof(f188,plain,(
% 31.83/4.51    ( ! [X3,X1] : (r2_hidden(X3,X1) | k4_enumset1(X3,X3,X3,X3,X3,X3) != X1) )),
% 31.83/4.51    inference(equality_resolution,[],[f166])).
% 31.83/4.51  
% 31.83/4.51  fof(f189,plain,(
% 31.83/4.51    ( ! [X3] : (r2_hidden(X3,k4_enumset1(X3,X3,X3,X3,X3,X3))) )),
% 31.83/4.51    inference(equality_resolution,[],[f188])).
% 31.83/4.51  
% 31.83/4.51  fof(f29,axiom,(
% 31.83/4.51    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f114,plain,(
% 31.83/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f29])).
% 31.83/4.51  
% 31.83/4.51  fof(f30,axiom,(
% 31.83/4.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f115,plain,(
% 31.83/4.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f30])).
% 31.83/4.51  
% 31.83/4.51  fof(f22,axiom,(
% 31.83/4.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f107,plain,(
% 31.83/4.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f22])).
% 31.83/4.51  
% 31.83/4.51  fof(f34,axiom,(
% 31.83/4.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f126,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 31.83/4.51    inference(cnf_transformation,[],[f34])).
% 31.83/4.51  
% 31.83/4.51  fof(f136,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 31.83/4.51    inference(definition_unfolding,[],[f126,f135])).
% 31.83/4.51  
% 31.83/4.51  fof(f140,plain,(
% 31.83/4.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X6,X7)))) )),
% 31.83/4.51    inference(definition_unfolding,[],[f107,f136,f113,f134])).
% 31.83/4.51  
% 31.83/4.51  fof(f142,plain,(
% 31.83/4.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X5,X6)))) )),
% 31.83/4.51    inference(definition_unfolding,[],[f115,f140])).
% 31.83/4.51  
% 31.83/4.51  fof(f171,plain,(
% 31.83/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X4,X5)))) )),
% 31.83/4.51    inference(definition_unfolding,[],[f114,f142])).
% 31.83/4.51  
% 31.83/4.51  fof(f21,axiom,(
% 31.83/4.51    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f106,plain,(
% 31.83/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f21])).
% 31.83/4.51  
% 31.83/4.51  fof(f143,plain,(
% 31.83/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)))) )),
% 31.83/4.51    inference(definition_unfolding,[],[f106,f136,f113,f139])).
% 31.83/4.51  
% 31.83/4.51  fof(f18,axiom,(
% 31.83/4.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f103,plain,(
% 31.83/4.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f18])).
% 31.83/4.51  
% 31.83/4.51  fof(f168,plain,(
% 31.83/4.51    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0)) )),
% 31.83/4.51    inference(definition_unfolding,[],[f103,f133,f133])).
% 31.83/4.51  
% 31.83/4.51  fof(f36,conjecture,(
% 31.83/4.51    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f37,negated_conjecture,(
% 31.83/4.51    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 31.83/4.51    inference(negated_conjecture,[],[f36])).
% 31.83/4.51  
% 31.83/4.51  fof(f43,plain,(
% 31.83/4.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 31.83/4.51    inference(ennf_transformation,[],[f37])).
% 31.83/4.51  
% 31.83/4.51  fof(f70,plain,(
% 31.83/4.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK9 | k1_tarski(sK7) != sK8) & (k1_tarski(sK7) != sK9 | k1_xboole_0 != sK8) & (k1_tarski(sK7) != sK9 | k1_tarski(sK7) != sK8) & k2_xboole_0(sK8,sK9) = k1_tarski(sK7))),
% 31.83/4.51    introduced(choice_axiom,[])).
% 31.83/4.51  
% 31.83/4.51  fof(f71,plain,(
% 31.83/4.51    (k1_xboole_0 != sK9 | k1_tarski(sK7) != sK8) & (k1_tarski(sK7) != sK9 | k1_xboole_0 != sK8) & (k1_tarski(sK7) != sK9 | k1_tarski(sK7) != sK8) & k2_xboole_0(sK8,sK9) = k1_tarski(sK7)),
% 31.83/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f43,f70])).
% 31.83/4.51  
% 31.83/4.51  fof(f129,plain,(
% 31.83/4.51    k2_xboole_0(sK8,sK9) = k1_tarski(sK7)),
% 31.83/4.51    inference(cnf_transformation,[],[f71])).
% 31.83/4.51  
% 31.83/4.51  fof(f181,plain,(
% 31.83/4.51    k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,sK9))),
% 31.83/4.51    inference(definition_unfolding,[],[f129,f136,f139])).
% 31.83/4.51  
% 31.83/4.51  fof(f2,axiom,(
% 31.83/4.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f44,plain,(
% 31.83/4.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 31.83/4.51    inference(nnf_transformation,[],[f2])).
% 31.83/4.51  
% 31.83/4.51  fof(f45,plain,(
% 31.83/4.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 31.83/4.51    inference(flattening,[],[f44])).
% 31.83/4.51  
% 31.83/4.51  fof(f46,plain,(
% 31.83/4.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 31.83/4.51    inference(rectify,[],[f45])).
% 31.83/4.51  
% 31.83/4.51  fof(f47,plain,(
% 31.83/4.51    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 31.83/4.51    introduced(choice_axiom,[])).
% 31.83/4.51  
% 31.83/4.51  fof(f48,plain,(
% 31.83/4.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 31.83/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 31.83/4.51  
% 31.83/4.51  fof(f73,plain,(
% 31.83/4.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 31.83/4.51    inference(cnf_transformation,[],[f48])).
% 31.83/4.51  
% 31.83/4.51  fof(f149,plain,(
% 31.83/4.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) != X2) )),
% 31.83/4.51    inference(definition_unfolding,[],[f73,f136])).
% 31.83/4.51  
% 31.83/4.51  fof(f184,plain,(
% 31.83/4.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 31.83/4.51    inference(equality_resolution,[],[f149])).
% 31.83/4.51  
% 31.83/4.51  fof(f32,axiom,(
% 31.83/4.51    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f42,plain,(
% 31.83/4.51    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 31.83/4.51    inference(ennf_transformation,[],[f32])).
% 31.83/4.51  
% 31.83/4.51  fof(f122,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f42])).
% 31.83/4.51  
% 31.83/4.51  fof(f16,axiom,(
% 31.83/4.51    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f98,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f16])).
% 31.83/4.51  
% 31.83/4.51  fof(f137,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 31.83/4.51    inference(definition_unfolding,[],[f98,f136])).
% 31.83/4.51  
% 31.83/4.51  fof(f172,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X0,X0,X0,X0,X0,X0)))) = k4_enumset1(X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 31.83/4.51    inference(definition_unfolding,[],[f122,f137,f139,f139])).
% 31.83/4.51  
% 31.83/4.51  fof(f14,axiom,(
% 31.83/4.51    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f96,plain,(
% 31.83/4.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f14])).
% 31.83/4.51  
% 31.83/4.51  fof(f1,axiom,(
% 31.83/4.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f72,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f1])).
% 31.83/4.51  
% 31.83/4.51  fof(f11,axiom,(
% 31.83/4.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f93,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 31.83/4.51    inference(cnf_transformation,[],[f11])).
% 31.83/4.51  
% 31.83/4.51  fof(f8,axiom,(
% 31.83/4.51    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f90,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f8])).
% 31.83/4.51  
% 31.83/4.51  fof(f138,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 31.83/4.51    inference(definition_unfolding,[],[f90,f137])).
% 31.83/4.51  
% 31.83/4.51  fof(f162,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))))))) )),
% 31.83/4.51    inference(definition_unfolding,[],[f93,f136,f136,f138])).
% 31.83/4.51  
% 31.83/4.51  fof(f15,axiom,(
% 31.83/4.51    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f97,plain,(
% 31.83/4.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 31.83/4.51    inference(cnf_transformation,[],[f15])).
% 31.83/4.51  
% 31.83/4.51  fof(f12,axiom,(
% 31.83/4.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f94,plain,(
% 31.83/4.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.83/4.51    inference(cnf_transformation,[],[f12])).
% 31.83/4.51  
% 31.83/4.51  fof(f13,axiom,(
% 31.83/4.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f95,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 31.83/4.51    inference(cnf_transformation,[],[f13])).
% 31.83/4.51  
% 31.83/4.51  fof(f163,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) )),
% 31.83/4.51    inference(definition_unfolding,[],[f95,f136,f136,f136])).
% 31.83/4.51  
% 31.83/4.51  fof(f132,plain,(
% 31.83/4.51    k1_xboole_0 != sK9 | k1_tarski(sK7) != sK8),
% 31.83/4.51    inference(cnf_transformation,[],[f71])).
% 31.83/4.51  
% 31.83/4.51  fof(f178,plain,(
% 31.83/4.51    k1_xboole_0 != sK9 | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK8),
% 31.83/4.51    inference(definition_unfolding,[],[f132,f139])).
% 31.83/4.51  
% 31.83/4.51  fof(f33,axiom,(
% 31.83/4.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f67,plain,(
% 31.83/4.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 31.83/4.51    inference(nnf_transformation,[],[f33])).
% 31.83/4.51  
% 31.83/4.51  fof(f68,plain,(
% 31.83/4.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 31.83/4.51    inference(flattening,[],[f67])).
% 31.83/4.51  
% 31.83/4.51  fof(f123,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 31.83/4.51    inference(cnf_transformation,[],[f68])).
% 31.83/4.51  
% 31.83/4.51  fof(f175,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 31.83/4.51    inference(definition_unfolding,[],[f123,f139,f139])).
% 31.83/4.51  
% 31.83/4.51  fof(f7,axiom,(
% 31.83/4.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 31.83/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.51  
% 31.83/4.51  fof(f56,plain,(
% 31.83/4.51    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 31.83/4.51    inference(nnf_transformation,[],[f7])).
% 31.83/4.51  
% 31.83/4.51  fof(f88,plain,(
% 31.83/4.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f56])).
% 31.83/4.51  
% 31.83/4.51  fof(f159,plain,(
% 31.83/4.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) != k1_xboole_0) )),
% 31.83/4.51    inference(definition_unfolding,[],[f88,f138])).
% 31.83/4.51  
% 31.83/4.51  fof(f89,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 31.83/4.51    inference(cnf_transformation,[],[f56])).
% 31.83/4.51  
% 31.83/4.51  fof(f158,plain,(
% 31.83/4.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 31.83/4.51    inference(definition_unfolding,[],[f89,f138])).
% 31.83/4.51  
% 31.83/4.51  fof(f131,plain,(
% 31.83/4.51    k1_tarski(sK7) != sK9 | k1_xboole_0 != sK8),
% 31.83/4.51    inference(cnf_transformation,[],[f71])).
% 31.83/4.51  
% 31.83/4.51  fof(f179,plain,(
% 31.83/4.51    k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9 | k1_xboole_0 != sK8),
% 31.83/4.51    inference(definition_unfolding,[],[f131,f139])).
% 31.83/4.51  
% 31.83/4.51  fof(f130,plain,(
% 31.83/4.51    k1_tarski(sK7) != sK9 | k1_tarski(sK7) != sK8),
% 31.83/4.51    inference(cnf_transformation,[],[f71])).
% 31.83/4.51  
% 31.83/4.51  fof(f180,plain,(
% 31.83/4.51    k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9 | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK8),
% 31.83/4.51    inference(definition_unfolding,[],[f130,f139,f139])).
% 31.83/4.51  
% 31.83/4.51  cnf(c_28,plain,
% 31.83/4.51      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
% 31.83/4.51      inference(cnf_transformation,[],[f189]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1150,plain,
% 31.83/4.51      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 31.83/4.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_33,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 31.83/4.51      inference(cnf_transformation,[],[f171]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_0,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 31.83/4.51      inference(cnf_transformation,[],[f143]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_2387,plain,
% 31.83/4.51      ( k4_enumset1(X0,X1,X2,X3,X3,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_33,c_0]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_30,plain,
% 31.83/4.51      ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
% 31.83/4.51      inference(cnf_transformation,[],[f168]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_49,negated_conjecture,
% 31.83/4.51      ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,sK9)) ),
% 31.83/4.51      inference(cnf_transformation,[],[f181]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1867,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK9,sK9,sK9,sK8,sK8,sK8)) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_30,c_49]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_11095,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,sK8)) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_2387,c_1867]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_7,plain,
% 31.83/4.51      ( r2_hidden(X0,X1)
% 31.83/4.51      | r2_hidden(X0,X2)
% 31.83/4.51      | ~ r2_hidden(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
% 31.83/4.51      inference(cnf_transformation,[],[f184]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1162,plain,
% 31.83/4.51      ( r2_hidden(X0,X1) = iProver_top
% 31.83/4.51      | r2_hidden(X0,X2) = iProver_top
% 31.83/4.51      | r2_hidden(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 31.83/4.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_38484,plain,
% 31.83/4.51      ( r2_hidden(X0,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != iProver_top
% 31.83/4.51      | r2_hidden(X0,sK8) = iProver_top
% 31.83/4.51      | r2_hidden(X0,sK9) = iProver_top ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_11095,c_1162]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_41335,plain,
% 31.83/4.51      ( r2_hidden(sK7,sK8) = iProver_top
% 31.83/4.51      | r2_hidden(sK7,sK9) = iProver_top ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1150,c_38484]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_40,plain,
% 31.83/4.51      ( ~ r2_hidden(X0,X1)
% 31.83/4.51      | k5_xboole_0(k5_xboole_0(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X0,X0,X0,X0,X0,X0)))) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
% 31.83/4.51      inference(cnf_transformation,[],[f172]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_24,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 31.83/4.51      inference(cnf_transformation,[],[f96]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1,plain,
% 31.83/4.51      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 31.83/4.51      inference(cnf_transformation,[],[f72]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_478,plain,
% 31.83/4.51      ( ~ r2_hidden(X0,X1)
% 31.83/4.51      | k5_xboole_0(X1,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X0,X0,X0,X0,X0,X0))))) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
% 31.83/4.51      inference(theory_normalisation,[status(thm)],[c_40,c_24,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1142,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X1,X1,X1,X1,X1,X1))))) = k4_enumset1(X1,X1,X1,X1,X1,X1)
% 31.83/4.51      | r2_hidden(X1,X0) != iProver_top ),
% 31.83/4.51      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_41748,plain,
% 31.83/4.51      ( k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)
% 31.83/4.51      | r2_hidden(sK7,sK9) = iProver_top ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_41335,c_1142]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_11256,plain,
% 31.83/4.51      ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_2387,c_30]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_21,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0)))))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 31.83/4.51      inference(cnf_transformation,[],[f162]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_479,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))))))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 31.83/4.51      inference(theory_normalisation,[status(thm)],[c_21,c_24,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_11484,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k5_xboole_0(sK9,k5_xboole_0(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,sK9)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_11095,c_479]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_25,plain,
% 31.83/4.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.83/4.51      inference(cnf_transformation,[],[f97]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1693,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_25,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_22,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.83/4.51      inference(cnf_transformation,[],[f94]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1499,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_22,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1703,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_1693,c_1499]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_11485,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,sK9)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_11484,c_1703]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_27333,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))) = k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,sK8)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_11256,c_11485]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_27336,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_27333,c_11095]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_23,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 31.83/4.51      inference(cnf_transformation,[],[f163]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_27755,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k5_xboole_0(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))) = k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_27336,c_23]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_27766,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_27755,c_27336]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_41749,plain,
% 31.83/4.51      ( k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)
% 31.83/4.51      | r2_hidden(sK7,sK9) = iProver_top ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_41748,c_27766]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_41750,plain,
% 31.83/4.51      ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = sK8
% 31.83/4.51      | r2_hidden(sK7,sK9) = iProver_top ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_41749,c_22,c_25]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_46,negated_conjecture,
% 31.83/4.51      ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK8
% 31.83/4.51      | k1_xboole_0 != sK9 ),
% 31.83/4.51      inference(cnf_transformation,[],[f178]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43,plain,
% 31.83/4.51      ( ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))
% 31.83/4.51      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
% 31.83/4.51      | k1_xboole_0 = X0 ),
% 31.83/4.51      inference(cnf_transformation,[],[f175]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1205,plain,
% 31.83/4.51      ( ~ r1_tarski(sK9,k4_enumset1(X0,X0,X0,X0,X0,X0))
% 31.83/4.51      | k4_enumset1(X0,X0,X0,X0,X0,X0) = sK9
% 31.83/4.51      | k1_xboole_0 = sK9 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_43]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1212,plain,
% 31.83/4.51      ( ~ r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))
% 31.83/4.51      | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = sK9
% 31.83/4.51      | k1_xboole_0 = sK9 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_1205]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_18,plain,
% 31.83/4.51      ( r1_tarski(X0,X1)
% 31.83/4.51      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
% 31.83/4.51      inference(cnf_transformation,[],[f159]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_481,plain,
% 31.83/4.51      ( r1_tarski(X0,X1)
% 31.83/4.51      | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) != k1_xboole_0 ),
% 31.83/4.51      inference(theory_normalisation,[status(thm)],[c_18,c_24,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_2834,plain,
% 31.83/4.51      ( r1_tarski(sK9,k4_enumset1(X0,X0,X0,X0,X0,X0))
% 31.83/4.51      | k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) != k1_xboole_0 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_481]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_2836,plain,
% 31.83/4.51      ( r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))
% 31.83/4.51      | k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) != k1_xboole_0 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_2834]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_17,plain,
% 31.83/4.51      ( ~ r1_tarski(X0,X1)
% 31.83/4.51      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
% 31.83/4.51      inference(cnf_transformation,[],[f158]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_482,plain,
% 31.83/4.51      ( ~ r1_tarski(X0,X1)
% 31.83/4.51      | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
% 31.83/4.51      inference(theory_normalisation,[status(thm)],[c_17,c_24,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6095,plain,
% 31.83/4.51      ( ~ r1_tarski(sK9,k4_enumset1(X0,X0,X0,X0,X0,X0))
% 31.83/4.51      | k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = k1_xboole_0 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_482]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6096,plain,
% 31.83/4.51      ( k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = k1_xboole_0
% 31.83/4.51      | r1_tarski(sK9,k4_enumset1(X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 31.83/4.51      inference(predicate_to_equality,[status(thm)],[c_6095]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6098,plain,
% 31.83/4.51      ( k5_xboole_0(sK9,k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) = k1_xboole_0
% 31.83/4.51      | r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != iProver_top ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_6096]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_11481,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,sK8)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_11095,c_23]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_11486,plain,
% 31.83/4.51      ( k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_11481,c_11095]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1153,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) != k1_xboole_0
% 31.83/4.51      | r1_tarski(X0,X1) = iProver_top ),
% 31.83/4.51      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1203,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1201,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_4243,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_25,c_1201]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_4264,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_4243,c_22]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5009,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_4264,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5580,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1,c_5009]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5916,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1203,c_5580]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19238,plain,
% 31.83/4.51      ( k5_xboole_0(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X1) != k1_xboole_0
% 31.83/4.51      | r1_tarski(X0,X1) = iProver_top ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_1153,c_5916]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19263,plain,
% 31.83/4.51      ( k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != k1_xboole_0
% 31.83/4.51      | r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_11486,c_19238]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19288,plain,
% 31.83/4.51      ( k1_xboole_0 != k1_xboole_0
% 31.83/4.51      | r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_19263,c_25]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19289,plain,
% 31.83/4.51      ( r1_tarski(sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
% 31.83/4.51      inference(equality_resolution_simp,[status(thm)],[c_19288]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5612,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),X2),X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5009,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5615,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,X2)) = X1 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5009,c_4264]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5636,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_5615,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6168,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1,c_5636]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6607,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X3,k5_xboole_0(X0,X1))) = X2 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_6168]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20539,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X4,X1))),k5_xboole_0(k5_xboole_0(X0,X2),X3)) = X4 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5612,c_6607]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6137,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = X2 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_5636]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6149,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1,c_5636]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6478,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = k5_xboole_0(X2,X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6149,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19519,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X4)),X2) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X1),X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6137,c_6478]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5587,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_5009]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6010,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3)))) = k5_xboole_0(X2,X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_5587]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19657,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X2,X4))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),X4) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6478,c_6010]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15472,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X2,X4))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6010,c_6010]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15487,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X2,X4))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_15472,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19671,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_19657,c_24,c_15487]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19866,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X1))) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X4)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_19519,c_19671]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5625,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,X1)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5009,c_1203]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5633,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X1)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_5625,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13381,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X1))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X0,X2))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5633,c_1201]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1202,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5140,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_22,c_1202]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6445,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,X1) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5140,c_6149]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6536,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_6445,c_22]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_7363,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X1,X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1,c_6536]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15323,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)),X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X3,X4)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_7363,c_6010]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5601,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_5009]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12073,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X4)),X3),X4) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5601,c_6536]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12146,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),X2) = k5_xboole_0(k5_xboole_0(X0,X1),X3) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_12073,c_7363]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5594,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1,c_5009]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5644,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_5594,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12275,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))),X4) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),X4)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5644,c_5612]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_7422,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = k5_xboole_0(X1,k5_xboole_0(X3,X2)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6536,c_5580]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12425,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X2,X1),X3)) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_12275,c_7422]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13323,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),X1) = k5_xboole_0(X2,k5_xboole_0(X0,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_4264,c_5633]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5613,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(X0,X2),X3)) = k5_xboole_0(X1,X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5009,c_5009]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5637,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X2),X3)) = k5_xboole_0(X1,X3) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_5613,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13984,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X3,X4),X2)),X5)) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X1,X4)),X5) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5637,c_5637]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_7527,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_7363,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_14087,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X4)) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X4)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_13984,c_7527,c_12425]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5617,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5009,c_1202]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5635,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_5617,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13661,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(X2,k5_xboole_0(X0,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5635,c_4264]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13717,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k5_xboole_0(X2,k5_xboole_0(X4,X5))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X1,X5)),k5_xboole_0(X0,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5635,c_5633]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12328,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),X3),k5_xboole_0(X1,X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X2),X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5612,c_1202]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12390,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),k5_xboole_0(X1,X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X2),X3)) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_12328,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12438,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k5_xboole_0(X2,X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X1),X3)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_12425,c_12390]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13729,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X3,X4))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X3,X2),X4)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_13717,c_12425,c_12438]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_14088,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X2),X3)) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_14087,c_12425,c_13661,c_13729]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15586,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_15323,c_12146,c_12425,c_13323,c_14088]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19867,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X1))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X4))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_19866,c_13381,c_15586]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20942,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(k5_xboole_0(X2,X0),X1)) = X3 ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_20539,c_24,c_19867]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_53523,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,X0),X1)) = k1_xboole_0 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_22,c_20942]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6324,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_5644]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55438,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,X0),X1)) = k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,k5_xboole_0(X4,k1_xboole_0))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_53523,c_6324]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55573,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_55438,c_53523]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5426,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1203,c_4264]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15942,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6137,c_5587]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15318,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3) = k5_xboole_0(k5_xboole_0(X0,X2),X1) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5636,c_6010]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15991,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_15942,c_24,c_15318]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43133,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6324,c_15991]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43598,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = sP0_iProver_split ),
% 31.83/4.51      inference(splitting,
% 31.83/4.51                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 31.83/4.51                [c_43133]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55574,plain,
% 31.83/4.51      ( sP0_iProver_split = k1_xboole_0 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_55573,c_22,c_5426,c_43598]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_47,negated_conjecture,
% 31.83/4.51      ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9
% 31.83/4.51      | k1_xboole_0 != sK8 ),
% 31.83/4.51      inference(cnf_transformation,[],[f179]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_59243,plain,
% 31.83/4.51      ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9
% 31.83/4.51      | sP0_iProver_split != sK8 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_55574,c_47]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_48,negated_conjecture,
% 31.83/4.51      ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK8
% 31.83/4.51      | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9 ),
% 31.83/4.51      inference(cnf_transformation,[],[f180]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1224,plain,
% 31.83/4.51      ( ~ r1_tarski(sK8,k4_enumset1(X0,X0,X0,X0,X0,X0))
% 31.83/4.51      | k4_enumset1(X0,X0,X0,X0,X0,X0) = sK8
% 31.83/4.51      | k1_xboole_0 = sK8 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_43]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1231,plain,
% 31.83/4.51      ( ~ r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))
% 31.83/4.51      | k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = sK8
% 31.83/4.51      | k1_xboole_0 = sK8 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_1224]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1390,plain,
% 31.83/4.51      ( r1_tarski(sK8,k4_enumset1(X0,X0,X0,X0,X0,X0))
% 31.83/4.51      | k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) != k1_xboole_0 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_481]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_1392,plain,
% 31.83/4.51      ( r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))
% 31.83/4.51      | k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) != k1_xboole_0 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_1390]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_2082,plain,
% 31.83/4.51      ( ~ r1_tarski(sK8,k4_enumset1(X0,X0,X0,X0,X0,X0))
% 31.83/4.51      | k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = k1_xboole_0 ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_482]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_2083,plain,
% 31.83/4.51      ( k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = k1_xboole_0
% 31.83/4.51      | r1_tarski(sK8,k4_enumset1(X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 31.83/4.51      inference(predicate_to_equality,[status(thm)],[c_2082]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_2085,plain,
% 31.83/4.51      ( k5_xboole_0(sK8,k5_xboole_0(sK8,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK8,sK8,sK8,sK8,sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)))))) = k1_xboole_0
% 31.83/4.51      | r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != iProver_top ),
% 31.83/4.51      inference(instantiation,[status(thm)],[c_2083]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_27951,plain,
% 31.83/4.51      ( k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) != k1_xboole_0
% 31.83/4.51      | r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_27766,c_19238]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_27962,plain,
% 31.83/4.51      ( k1_xboole_0 != k1_xboole_0
% 31.83/4.51      | r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_27951,c_25]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_27963,plain,
% 31.83/4.51      ( r1_tarski(sK8,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
% 31.83/4.51      inference(equality_resolution_simp,[status(thm)],[c_27962]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_60461,plain,
% 31.83/4.51      ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) != sK9 ),
% 31.83/4.51      inference(global_propositional_subsumption,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_59243,c_48,c_47,c_1231,c_1392,c_2085,c_27963]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_73934,plain,
% 31.83/4.51      ( r2_hidden(sK7,sK9) = iProver_top ),
% 31.83/4.51      inference(global_propositional_subsumption,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_41750,c_48,c_47,c_46,c_1212,c_1231,c_1392,c_2085,
% 31.83/4.51                 c_2836,c_6098,c_19289,c_27963]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_73942,plain,
% 31.83/4.51      ( k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k3_tarski(k4_enumset1(sK9,sK9,sK9,sK9,sK9,k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_73934,c_1142]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_73943,plain,
% 31.83/4.51      ( k5_xboole_0(sK9,k5_xboole_0(k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7),k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7))) = k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_73942,c_11486]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6629,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X3,X0)) = k5_xboole_0(X1,X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_6168]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6156,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X0,X3)) = k5_xboole_0(X1,X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_5636]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16451,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X0,k5_xboole_0(X3,X2))) = k5_xboole_0(X1,k1_xboole_0) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5140,c_6156]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15324,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)),X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X4,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6536,c_6010]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15574,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_15324,c_12146,c_12425,c_13323,c_14088]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5939,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5009,c_5580]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5968,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X3) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_5939,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15356,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),k5_xboole_0(X4,k5_xboole_0(X1,X3))) = k5_xboole_0(X4,k5_xboole_0(X0,X2)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5968,c_6010]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15555,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k5_xboole_0(X4,k5_xboole_0(X2,X3))) = k5_xboole_0(X4,k5_xboole_0(X0,X1)) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_15356,c_12425]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15576,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X4,k5_xboole_0(X3,X2))) = k5_xboole_0(X4,k5_xboole_0(X0,X1)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_15574,c_15555]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16885,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X0,k5_xboole_0(X3,X2))) = X1 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_16451,c_22,c_15576]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43888,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,X2)))))),k5_xboole_0(X0,k5_xboole_0(X4,X5))) = X1 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6629,c_16885]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43927,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X5,X4))),X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_16885,c_5968]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20617,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X1,X3))),X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6607,c_5968]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15389,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4)))) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,X4))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5644,c_6010]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19493,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_25,c_6478]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20094,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X3,X1))),X4) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_19493,c_5601]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_5174,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_5140]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_9080,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1,c_5174]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_10354,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X0,X2))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_9080,c_1203]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_10368,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,X3))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_9080,c_5587]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16565,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4))),X5)),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X1,X4),k5_xboole_0(X0,X5)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6156,c_5635]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16573,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X0),X4) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,X2),X4)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6156,c_5601]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_7510,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X0) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1203,c_7363]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16622,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_16573,c_7510]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16623,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_16622,c_12425,c_15586]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16629,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X3,X4)),k5_xboole_0(X5,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X5,X4)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_16565,c_16623]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16630,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X5,k5_xboole_0(X0,X3)))))) = k5_xboole_0(k5_xboole_0(X1,X4),k5_xboole_0(X5,X2)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_16629,c_16623]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16631,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X0,X3))))))) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X5,X2))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_16630,c_14088,c_15586]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6007,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0)))) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1203,c_5587]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_11992,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,X0))))) = k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X2,X1)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1202,c_5601]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16632,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X1,X2))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_16631,c_6007,c_11992]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20128,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X3,X4))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X3,k5_xboole_0(X4,X2))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_20094,c_10354,c_10368,c_16632,c_19671]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20129,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X4,k5_xboole_0(X2,X3)))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_20128,c_15586,c_16632]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20763,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X4,X5)))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_20617,c_15389,c_19671,c_20129]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44148,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X3,X2)))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_43927,c_20763]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6669,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,X0),X3)) = k5_xboole_0(X1,X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6168,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43924,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X4)),X0),X5)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X4,X3))),X5) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_16885,c_6669]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44152,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X4)),X0),X5)) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X5,k5_xboole_0(X3,X4)))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_43924,c_44148]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13662,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,X3))) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5635,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36616,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X0),X3)) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_13662,c_6478]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13918,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X2,X3))) = k5_xboole_0(X1,X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_5637]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_39216,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X2)),X5)) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X1))),X5) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_13918,c_5601]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20619,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X1,X4))),X5)) = k5_xboole_0(X5,k5_xboole_0(X0,k5_xboole_0(X4,k5_xboole_0(X2,X3)))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6607,c_5635]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_14954,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,X2)),X4)) = k5_xboole_0(X4,k5_xboole_0(X3,X0)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5968,c_1202]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13656,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X3),X4)) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X0,X2)),X4) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5635,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12233,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(X2,k1_xboole_0) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_25,c_5612]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12021,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5580,c_5601]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12494,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),X1)) = X2 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_12233,c_22,c_12021]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12741,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(X1,X3),X4)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X2),X3),X4) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_12494,c_5612]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12814,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X3),X4)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X2),X3),X4) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_12741,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13758,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X3),X4)) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X0),X4)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_13656,c_12425,c_12814]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_14008,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5637,c_5644]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15038,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X3,k5_xboole_0(X2,X0)) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_14954,c_12425,c_13758,c_14008]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20759,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)) = k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X0,X1)))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_20619,c_13729,c_15038,c_19671]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_7348,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X0,X1)) = k5_xboole_0(X3,X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_6536]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_23700,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X5)))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X2,X1))),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_7348,c_5968]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_22151,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X5)))) = k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X1,k5_xboole_0(X2,X4))),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6629,c_5968]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_18078,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X5)))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X4,X5)))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6324,c_6010]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_22306,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X4,X5)))) = k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X5,X1)))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_22151,c_18078,c_19671,c_20129]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_23877,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4) = k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X1,X3)))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_23700,c_22306]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_23585,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X1,X2)),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6324,c_7348]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_22163,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6629,c_5636]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_24029,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_23585,c_22163]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_39325,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X5)))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X4,X5)))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_39216,c_20759,c_23877,c_24029]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12010,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1203,c_5601]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_39326,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X3),X4)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X2,X3)))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_39325,c_11992,c_12010,c_20759]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13949,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X2,X0)),X4)) = k5_xboole_0(X1,X4) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1202,c_5637]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13597,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X3,X4)) = k5_xboole_0(X4,k5_xboole_0(X0,k5_xboole_0(X2,X1))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1202,c_5635]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_14172,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_13949,c_12425,c_13597]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_14173,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_14172,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_39809,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X1),X4),X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5009,c_14173]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_39106,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X3,X2))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5580,c_13918]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_40192,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_39809,c_39106]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44153,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,X3)),k5_xboole_0(X4,X5)))) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X4,X5)))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_44152,c_36616,c_39326,c_40192]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_6045,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X2),X3))) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5587,c_5009]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13588,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,X1)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1,c_5635]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36513,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X3,X0),X1)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_13662,c_13588]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13351,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5633,c_1]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_35756,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X0,X3),X1)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_13351,c_13588]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_13865,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),X4) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5601,c_5637]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_14233,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),X4) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_13865,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_14234,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X3,X1),X4)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_14233,c_12425]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36173,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X2),X4)) = k5_xboole_0(X4,k5_xboole_0(X0,k5_xboole_0(X3,X1))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_35756,c_14234,c_15586]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36681,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,X3))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_36513,c_36173]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36371,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4))),X5))) = k5_xboole_0(k5_xboole_0(X4,X3),k5_xboole_0(X2,X5)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6629,c_13662]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36815,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),k5_xboole_0(X4,X5)))) = k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X2,X5)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_36371,c_36681]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36433,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X4)))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1201,c_13662]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36816,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X2),k5_xboole_0(X3,X4)))) = k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X1,X4)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_36815,c_36433,c_36681]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36817,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))))) = k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X1,X4)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_36816,c_36681]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_7370,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X0) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_6536]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_24230,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4)))),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X4,X2)))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_19493,c_7370]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_24517,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X3)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_24230,c_7370]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20096,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X1)),X0) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_19493,c_5580]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20127,plain,
% 31.83/4.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_20096,c_10368,c_19671]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_24518,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_24517,c_20127]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_24133,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))))) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6137,c_7370]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_15925,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6137,c_6536]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_24634,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))))) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_24133,c_15586,c_15925]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_36818,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,X1))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_36817,c_24518,c_24634]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44154,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = k5_xboole_0(X0,k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_44153,c_6045,c_36681,c_36818]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44246,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,X3)),k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X5,k5_xboole_0(X5,X2))),X4)))) = X1 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_43888,c_44148,c_44154]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43901,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,X4))),X5))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X4,X3)),k5_xboole_0(X1,X5)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_16885,c_13662]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44200,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5)))))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X4,X5)),k5_xboole_0(X1,X3)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_43901,c_44148]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16527,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X3,X4)),X5)) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,X4))),X5) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6156,c_5637]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16721,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),k5_xboole_0(k5_xboole_0(X3,X4),X5))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X1,X5)))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_16527,c_16623,c_16632]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16722,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X3),k5_xboole_0(X4,X5))))) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X1,X2)))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_16721,c_16632]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_16723,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5)))))) = k5_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X1,X2)))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_16722,c_16632]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44201,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)) = k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X3,X0)))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_44200,c_16723]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44247,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X5,k5_xboole_0(X5,X4))),X0)))))) = X1 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_44246,c_44201]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44248,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X5,k5_xboole_0(X0,k5_xboole_0(X4,X5))))))))) = X1 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_44247,c_44148]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44249,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(X3,k5_xboole_0(X5,X0))))))))) = X1 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_44248,c_44154]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43957,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X3,X2),X1) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_16885,c_6536]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44250,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X3,X4)),X0),X2))))) = X1 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_44249,c_43957,c_44154]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_7412,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X0)) = k5_xboole_0(X2,X1) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6536,c_24]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_10337,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_7412,c_9080]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_10415,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),X0))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_10337,c_9080]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_24303,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X3,X4))))) = k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X2,X3))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_7370,c_1203]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44251,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2))) = X0 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_44250,c_10415,c_24303]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_44252,plain,
% 31.83/4.51      ( k5_xboole_0(X0,sP0_iProver_split) = X0 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_44251,c_36681,c_43598]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55325,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X4))))),k5_xboole_0(X4,X3)) = k1_xboole_0 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_20942,c_53523]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_19498,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_6478]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55347,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X1),X2),X4) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_53523,c_19498]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55845,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X1),X2),X4) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_55347,c_22]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43985,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X3,X2),X1) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_16885,c_5580]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55846,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0))) ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_55845,c_5916,c_36681,c_40192,c_43985]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55931,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4))),k5_xboole_0(X3,X1))),k5_xboole_0(X4,k5_xboole_0(X0,X2))) = k1_xboole_0 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_55325,c_55846]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55932,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X3,X3))),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X4,X0),X4))) = k1_xboole_0 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_55931,c_55846]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55933,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),X2)),k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,X2),X4),k5_xboole_0(X0,X3)))) = k1_xboole_0 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_55932,c_55846]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55934,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,X1)))),X4))) = k1_xboole_0 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_55933,c_55846]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55935,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,X0)))),X3))) = sP0_iProver_split ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_55934,c_25,c_55574]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12110,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3))),X4)) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,X2),X4)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_5601,c_5009]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_12238,plain,
% 31.83/4.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_24,c_5612]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20558,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X3,k5_xboole_0(X1,X0))) = X2 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1,c_6607]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_52482,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X4,k5_xboole_0(X1,X3))),X2) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_20558,c_5968]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_52541,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3),X4) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X2,X4)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_20558,c_5601]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_20478,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = X3 ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_1,c_6607]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_48836,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X3) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_20478,c_5644]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_52678,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X0)),X3) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_52541,c_48836]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_45210,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X2))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X4)),X3) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_19498,c_5580]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43173,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X2))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X3,X4),X1)) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_6010,c_15991]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_39911,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X2))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4))) ),
% 31.83/4.51      inference(superposition,[status(thm)],[c_14173,c_5587]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_43571,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,k5_xboole_0(X4,X2))) = k5_xboole_0(X0,k5_xboole_0(X4,k5_xboole_0(X3,X1))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_43173,c_36681,c_39911]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_45335,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X3,X1))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_45210,c_43571]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_52679,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,X0))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_52678,c_24518,c_45335]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_52749,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X5))))) = k5_xboole_0(k5_xboole_0(X1,X3),k5_xboole_0(X4,k5_xboole_0(X2,X5))) ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_52482,c_52679]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_52750,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X2,X4)))) ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_52749,c_20763]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55936,plain,
% 31.83/4.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = sP0_iProver_split ),
% 31.83/4.51      inference(demodulation,
% 31.83/4.51                [status(thm)],
% 31.83/4.51                [c_55935,c_1499,c_12110,c_12238,c_52750]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_55937,plain,
% 31.83/4.51      ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
% 31.83/4.51      inference(light_normalisation,[status(thm)],[c_55936,c_1703]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(c_73944,plain,
% 31.83/4.51      ( k4_enumset1(sK7,sK7,sK7,sK7,sK7,sK7) = sK9 ),
% 31.83/4.51      inference(demodulation,[status(thm)],[c_73943,c_44252,c_55937]) ).
% 31.83/4.51  
% 31.83/4.51  cnf(contradiction,plain,
% 31.83/4.51      ( $false ),
% 31.83/4.51      inference(minisat,[status(thm)],[c_73944,c_60461]) ).
% 31.83/4.51  
% 31.83/4.51  
% 31.83/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.83/4.51  
% 31.83/4.51  ------                               Statistics
% 31.83/4.51  
% 31.83/4.51  ------ General
% 31.83/4.51  
% 31.83/4.51  abstr_ref_over_cycles:                  0
% 31.83/4.51  abstr_ref_under_cycles:                 0
% 31.83/4.51  gc_basic_clause_elim:                   0
% 31.83/4.51  forced_gc_time:                         0
% 31.83/4.51  parsing_time:                           0.011
% 31.83/4.51  unif_index_cands_time:                  0.
% 31.83/4.51  unif_index_add_time:                    0.
% 31.83/4.51  orderings_time:                         0.
% 31.83/4.51  out_proof_time:                         0.033
% 31.83/4.51  total_time:                             3.889
% 31.83/4.51  num_of_symbols:                         48
% 31.83/4.51  num_of_terms:                           175157
% 31.83/4.51  
% 31.83/4.51  ------ Preprocessing
% 31.83/4.51  
% 31.83/4.51  num_of_splits:                          0
% 31.83/4.51  num_of_split_atoms:                     1
% 31.83/4.51  num_of_reused_defs:                     0
% 31.83/4.51  num_eq_ax_congr_red:                    30
% 31.83/4.51  num_of_sem_filtered_clauses:            1
% 31.83/4.51  num_of_subtypes:                        0
% 31.83/4.51  monotx_restored_types:                  0
% 31.83/4.51  sat_num_of_epr_types:                   0
% 31.83/4.51  sat_num_of_non_cyclic_types:            0
% 31.83/4.51  sat_guarded_non_collapsed_types:        0
% 31.83/4.51  num_pure_diseq_elim:                    0
% 31.83/4.51  simp_replaced_by:                       0
% 31.83/4.51  res_preprocessed:                       165
% 31.83/4.51  prep_upred:                             0
% 31.83/4.51  prep_unflattend:                        8
% 31.83/4.51  smt_new_axioms:                         0
% 31.83/4.51  pred_elim_cands:                        2
% 31.83/4.51  pred_elim:                              0
% 31.83/4.51  pred_elim_cl:                           0
% 31.83/4.51  pred_elim_cycles:                       1
% 31.83/4.51  merged_defs:                            6
% 31.83/4.51  merged_defs_ncl:                        0
% 31.83/4.51  bin_hyper_res:                          6
% 31.83/4.51  prep_cycles:                            3
% 31.83/4.51  pred_elim_time:                         0.001
% 31.83/4.51  splitting_time:                         0.
% 31.83/4.51  sem_filter_time:                        0.
% 31.83/4.51  monotx_time:                            0.
% 31.83/4.51  subtype_inf_time:                       0.
% 31.83/4.51  
% 31.83/4.51  ------ Problem properties
% 31.83/4.51  
% 31.83/4.51  clauses:                                50
% 31.83/4.51  conjectures:                            4
% 31.83/4.51  epr:                                    0
% 31.83/4.51  horn:                                   40
% 31.83/4.51  ground:                                 4
% 31.83/4.51  unary:                                  19
% 31.83/4.51  binary:                                 16
% 31.83/4.51  lits:                                   99
% 31.83/4.51  lits_eq:                                46
% 31.83/4.51  fd_pure:                                0
% 31.83/4.51  fd_pseudo:                              0
% 31.83/4.51  fd_cond:                                2
% 31.83/4.51  fd_pseudo_cond:                         13
% 31.83/4.51  ac_symbols:                             1
% 31.83/4.51  
% 31.83/4.51  ------ Propositional Solver
% 31.83/4.51  
% 31.83/4.51  prop_solver_calls:                      31
% 31.83/4.51  prop_fast_solver_calls:                 1426
% 31.83/4.51  smt_solver_calls:                       0
% 31.83/4.51  smt_fast_solver_calls:                  0
% 31.83/4.51  prop_num_of_clauses:                    23016
% 31.83/4.51  prop_preprocess_simplified:             36338
% 31.83/4.51  prop_fo_subsumed:                       7
% 31.83/4.51  prop_solver_time:                       0.
% 31.83/4.51  smt_solver_time:                        0.
% 31.83/4.51  smt_fast_solver_time:                   0.
% 31.83/4.51  prop_fast_solver_time:                  0.
% 31.83/4.51  prop_unsat_core_time:                   0.001
% 31.83/4.51  
% 31.83/4.51  ------ QBF
% 31.83/4.51  
% 31.83/4.51  qbf_q_res:                              0
% 31.83/4.51  qbf_num_tautologies:                    0
% 31.83/4.51  qbf_prep_cycles:                        0
% 31.83/4.51  
% 31.83/4.51  ------ BMC1
% 31.83/4.51  
% 31.83/4.51  bmc1_current_bound:                     -1
% 31.83/4.51  bmc1_last_solved_bound:                 -1
% 31.83/4.51  bmc1_unsat_core_size:                   -1
% 31.83/4.51  bmc1_unsat_core_parents_size:           -1
% 31.83/4.51  bmc1_merge_next_fun:                    0
% 31.83/4.51  bmc1_unsat_core_clauses_time:           0.
% 31.83/4.51  
% 31.83/4.51  ------ Instantiation
% 31.83/4.51  
% 31.83/4.51  inst_num_of_clauses:                    4496
% 31.83/4.51  inst_num_in_passive:                    3157
% 31.83/4.51  inst_num_in_active:                     967
% 31.83/4.51  inst_num_in_unprocessed:                375
% 31.83/4.51  inst_num_of_loops:                      1660
% 31.83/4.51  inst_num_of_learning_restarts:          0
% 31.83/4.51  inst_num_moves_active_passive:          690
% 31.83/4.51  inst_lit_activity:                      0
% 31.83/4.51  inst_lit_activity_moves:                1
% 31.83/4.51  inst_num_tautologies:                   0
% 31.83/4.51  inst_num_prop_implied:                  0
% 31.83/4.51  inst_num_existing_simplified:           0
% 31.83/4.51  inst_num_eq_res_simplified:             0
% 31.83/4.51  inst_num_child_elim:                    0
% 31.83/4.51  inst_num_of_dismatching_blockings:      4528
% 31.83/4.51  inst_num_of_non_proper_insts:           4256
% 31.83/4.51  inst_num_of_duplicates:                 0
% 31.83/4.51  inst_inst_num_from_inst_to_res:         0
% 31.83/4.51  inst_dismatching_checking_time:         0.
% 31.83/4.51  
% 31.83/4.51  ------ Resolution
% 31.83/4.51  
% 31.83/4.51  res_num_of_clauses:                     0
% 31.83/4.51  res_num_in_passive:                     0
% 31.83/4.51  res_num_in_active:                      0
% 31.83/4.51  res_num_of_loops:                       168
% 31.83/4.51  res_forward_subset_subsumed:            306
% 31.83/4.51  res_backward_subset_subsumed:           6
% 31.83/4.51  res_forward_subsumed:                   0
% 31.83/4.51  res_backward_subsumed:                  0
% 31.83/4.51  res_forward_subsumption_resolution:     0
% 31.83/4.51  res_backward_subsumption_resolution:    0
% 31.83/4.51  res_clause_to_clause_subsumption:       164403
% 31.83/4.51  res_orphan_elimination:                 0
% 31.83/4.51  res_tautology_del:                      267
% 31.83/4.51  res_num_eq_res_simplified:              0
% 31.83/4.51  res_num_sel_changes:                    0
% 31.83/4.51  res_moves_from_active_to_pass:          0
% 31.83/4.51  
% 31.83/4.51  ------ Superposition
% 31.83/4.51  
% 31.83/4.51  sup_time_total:                         0.
% 31.83/4.51  sup_time_generating:                    0.
% 31.83/4.51  sup_time_sim_full:                      0.
% 31.83/4.51  sup_time_sim_immed:                     0.
% 31.83/4.51  
% 31.83/4.51  sup_num_of_clauses:                     4451
% 31.83/4.51  sup_num_in_active:                      205
% 31.83/4.51  sup_num_in_passive:                     4246
% 31.83/4.51  sup_num_of_loops:                       330
% 31.83/4.51  sup_fw_superposition:                   10394
% 31.83/4.51  sup_bw_superposition:                   8267
% 31.83/4.51  sup_immediate_simplified:               11748
% 31.83/4.51  sup_given_eliminated:                   9
% 31.83/4.51  comparisons_done:                       0
% 31.83/4.51  comparisons_avoided:                    7
% 31.83/4.51  
% 31.83/4.51  ------ Simplifications
% 31.83/4.51  
% 31.83/4.51  
% 31.83/4.51  sim_fw_subset_subsumed:                 34
% 31.83/4.51  sim_bw_subset_subsumed:                 10
% 31.83/4.51  sim_fw_subsumed:                        418
% 31.83/4.51  sim_bw_subsumed:                        9
% 31.83/4.51  sim_fw_subsumption_res:                 0
% 31.83/4.51  sim_bw_subsumption_res:                 0
% 31.83/4.51  sim_tautology_del:                      216
% 31.83/4.51  sim_eq_tautology_del:                   1445
% 31.83/4.51  sim_eq_res_simp:                        85
% 31.83/4.51  sim_fw_demodulated:                     13339
% 31.83/4.51  sim_bw_demodulated:                     280
% 31.83/4.51  sim_light_normalised:                   2918
% 31.83/4.51  sim_joinable_taut:                      725
% 31.83/4.51  sim_joinable_simp:                      0
% 31.83/4.51  sim_ac_normalised:                      0
% 31.83/4.51  sim_smt_subsumption:                    0
% 31.83/4.51  
%------------------------------------------------------------------------------
