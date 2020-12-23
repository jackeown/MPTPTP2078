%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:36 EST 2020

% Result     : Theorem 12.00s
% Output     : CNFRefutation 12.00s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 301 expanded)
%              Number of clauses        :   57 (  85 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   21
%              Number of atoms          :  451 (1620 expanded)
%              Number of equality atoms :  214 ( 801 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f101,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f102,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f101])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f68])).

fof(f99,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f85])).

fof(f100,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f99])).

fof(f13,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_setfam_1(X0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f42])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f105,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f103,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f104,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f103])).

fof(f15,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f44])).

fof(f78,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f79])).

fof(f93,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f78,f80])).

cnf(c_492,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1347,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_37577,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | X0 != sK4
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_37579,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_37577])).

cnf(c_491,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1342,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK3(X3,X2))
    | X2 != X0
    | sK3(X3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_17071,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_17073,plain,
    ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | ~ r1_tarski(sK4,sK4)
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_17071])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1066,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1059,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1823,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X0) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_1059])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1060,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2783,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_1060])).

cnf(c_8551,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_2783])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1051,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1052,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_26,plain,
    ( ~ r2_hidden(k1_xboole_0,X0)
    | k1_setfam_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1043,plain,
    ( k1_setfam_1(X0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1581,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1052,c_1043])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1044,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1841,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_1044])).

cnf(c_3813,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1051,c_1841])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1058,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3832,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_1058])).

cnf(c_9216,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8551,c_3832])).

cnf(c_9600,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9216,c_1059])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1067,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8546,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1067])).

cnf(c_8908,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8546,c_3832])).

cnf(c_9195,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8908,c_1060])).

cnf(c_9619,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9600,c_9195])).

cnf(c_9621,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9619])).

cnf(c_9623,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9621])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,sK3(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6192,plain,
    ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_28,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4945,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))
    | sK3(k2_enumset1(X1,X1,X2,X3),X0) = X1
    | sK3(k2_enumset1(X1,X1,X2,X3),X0) = X2
    | sK3(k2_enumset1(X1,X1,X2,X3),X0) = X3
    | k1_xboole_0 = k2_enumset1(X1,X1,X2,X3) ),
    inference(resolution,[status(thm)],[c_19,c_28])).

cnf(c_4947,plain,
    ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_4945])).

cnf(c_1322,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1266,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1268,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_72,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_59,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_56,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_29,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37579,c_17073,c_9623,c_6192,c_4947,c_1322,c_1268,c_72,c_59,c_56,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 12.00/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/1.99  
% 12.00/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.00/1.99  
% 12.00/1.99  ------  iProver source info
% 12.00/1.99  
% 12.00/1.99  git: date: 2020-06-30 10:37:57 +0100
% 12.00/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.00/1.99  git: non_committed_changes: false
% 12.00/1.99  git: last_make_outside_of_git: false
% 12.00/1.99  
% 12.00/1.99  ------ 
% 12.00/1.99  ------ Parsing...
% 12.00/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.00/1.99  
% 12.00/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 12.00/1.99  
% 12.00/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.00/1.99  
% 12.00/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.00/1.99  ------ Proving...
% 12.00/1.99  ------ Problem Properties 
% 12.00/1.99  
% 12.00/1.99  
% 12.00/1.99  clauses                                 29
% 12.00/1.99  conjectures                             1
% 12.00/1.99  EPR                                     3
% 12.00/1.99  Horn                                    20
% 12.00/1.99  unary                                   7
% 12.00/1.99  binary                                  9
% 12.00/1.99  lits                                    68
% 12.00/1.99  lits eq                                 23
% 12.00/1.99  fd_pure                                 0
% 12.00/1.99  fd_pseudo                               0
% 12.00/1.99  fd_cond                                 2
% 12.00/1.99  fd_pseudo_cond                          9
% 12.00/1.99  AC symbols                              0
% 12.00/1.99  
% 12.00/1.99  ------ Input Options Time Limit: Unbounded
% 12.00/1.99  
% 12.00/1.99  
% 12.00/1.99  ------ 
% 12.00/1.99  Current options:
% 12.00/1.99  ------ 
% 12.00/1.99  
% 12.00/1.99  
% 12.00/1.99  
% 12.00/1.99  
% 12.00/1.99  ------ Proving...
% 12.00/1.99  
% 12.00/1.99  
% 12.00/1.99  % SZS status Theorem for theBenchmark.p
% 12.00/1.99  
% 12.00/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 12.00/1.99  
% 12.00/1.99  fof(f1,axiom,(
% 12.00/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f17,plain,(
% 12.00/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.00/1.99    inference(ennf_transformation,[],[f1])).
% 12.00/1.99  
% 12.00/1.99  fof(f25,plain,(
% 12.00/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.00/1.99    inference(nnf_transformation,[],[f17])).
% 12.00/1.99  
% 12.00/1.99  fof(f26,plain,(
% 12.00/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.00/1.99    inference(rectify,[],[f25])).
% 12.00/1.99  
% 12.00/1.99  fof(f27,plain,(
% 12.00/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 12.00/1.99    introduced(choice_axiom,[])).
% 12.00/1.99  
% 12.00/1.99  fof(f28,plain,(
% 12.00/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.00/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 12.00/1.99  
% 12.00/1.99  fof(f47,plain,(
% 12.00/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f28])).
% 12.00/1.99  
% 12.00/1.99  fof(f2,axiom,(
% 12.00/1.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f29,plain,(
% 12.00/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.00/1.99    inference(nnf_transformation,[],[f2])).
% 12.00/1.99  
% 12.00/1.99  fof(f30,plain,(
% 12.00/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.00/1.99    inference(flattening,[],[f29])).
% 12.00/1.99  
% 12.00/1.99  fof(f31,plain,(
% 12.00/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.00/1.99    inference(rectify,[],[f30])).
% 12.00/1.99  
% 12.00/1.99  fof(f32,plain,(
% 12.00/1.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 12.00/1.99    introduced(choice_axiom,[])).
% 12.00/1.99  
% 12.00/1.99  fof(f33,plain,(
% 12.00/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.00/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 12.00/1.99  
% 12.00/1.99  fof(f49,plain,(
% 12.00/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 12.00/1.99    inference(cnf_transformation,[],[f33])).
% 12.00/1.99  
% 12.00/1.99  fof(f96,plain,(
% 12.00/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 12.00/1.99    inference(equality_resolution,[],[f49])).
% 12.00/1.99  
% 12.00/1.99  fof(f50,plain,(
% 12.00/1.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 12.00/1.99    inference(cnf_transformation,[],[f33])).
% 12.00/1.99  
% 12.00/1.99  fof(f95,plain,(
% 12.00/1.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 12.00/1.99    inference(equality_resolution,[],[f50])).
% 12.00/1.99  
% 12.00/1.99  fof(f4,axiom,(
% 12.00/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f18,plain,(
% 12.00/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 12.00/1.99    inference(ennf_transformation,[],[f4])).
% 12.00/1.99  
% 12.00/1.99  fof(f36,plain,(
% 12.00/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 12.00/1.99    inference(nnf_transformation,[],[f18])).
% 12.00/1.99  
% 12.00/1.99  fof(f37,plain,(
% 12.00/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 12.00/1.99    inference(flattening,[],[f36])).
% 12.00/1.99  
% 12.00/1.99  fof(f38,plain,(
% 12.00/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 12.00/1.99    inference(rectify,[],[f37])).
% 12.00/1.99  
% 12.00/1.99  fof(f39,plain,(
% 12.00/1.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 12.00/1.99    introduced(choice_axiom,[])).
% 12.00/1.99  
% 12.00/1.99  fof(f40,plain,(
% 12.00/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 12.00/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 12.00/1.99  
% 12.00/1.99  fof(f60,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 12.00/1.99    inference(cnf_transformation,[],[f40])).
% 12.00/1.99  
% 12.00/1.99  fof(f7,axiom,(
% 12.00/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f68,plain,(
% 12.00/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f7])).
% 12.00/1.99  
% 12.00/1.99  fof(f86,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 12.00/1.99    inference(definition_unfolding,[],[f60,f68])).
% 12.00/1.99  
% 12.00/1.99  fof(f101,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 12.00/1.99    inference(equality_resolution,[],[f86])).
% 12.00/1.99  
% 12.00/1.99  fof(f102,plain,(
% 12.00/1.99    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 12.00/1.99    inference(equality_resolution,[],[f101])).
% 12.00/1.99  
% 12.00/1.99  fof(f61,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 12.00/1.99    inference(cnf_transformation,[],[f40])).
% 12.00/1.99  
% 12.00/1.99  fof(f85,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 12.00/1.99    inference(definition_unfolding,[],[f61,f68])).
% 12.00/1.99  
% 12.00/1.99  fof(f99,plain,(
% 12.00/1.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 12.00/1.99    inference(equality_resolution,[],[f85])).
% 12.00/1.99  
% 12.00/1.99  fof(f100,plain,(
% 12.00/1.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 12.00/1.99    inference(equality_resolution,[],[f99])).
% 12.00/1.99  
% 12.00/1.99  fof(f13,axiom,(
% 12.00/1.99    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_setfam_1(X0) = k1_xboole_0)),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f21,plain,(
% 12.00/1.99    ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0))),
% 12.00/1.99    inference(ennf_transformation,[],[f13])).
% 12.00/1.99  
% 12.00/1.99  fof(f75,plain,(
% 12.00/1.99    ( ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f21])).
% 12.00/1.99  
% 12.00/1.99  fof(f12,axiom,(
% 12.00/1.99    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f20,plain,(
% 12.00/1.99    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 12.00/1.99    inference(ennf_transformation,[],[f12])).
% 12.00/1.99  
% 12.00/1.99  fof(f74,plain,(
% 12.00/1.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f20])).
% 12.00/1.99  
% 12.00/1.99  fof(f3,axiom,(
% 12.00/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f34,plain,(
% 12.00/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.00/1.99    inference(nnf_transformation,[],[f3])).
% 12.00/1.99  
% 12.00/1.99  fof(f35,plain,(
% 12.00/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.00/1.99    inference(flattening,[],[f34])).
% 12.00/1.99  
% 12.00/1.99  fof(f57,plain,(
% 12.00/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f35])).
% 12.00/1.99  
% 12.00/1.99  fof(f48,plain,(
% 12.00/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f28])).
% 12.00/1.99  
% 12.00/1.99  fof(f14,axiom,(
% 12.00/1.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f22,plain,(
% 12.00/1.99    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 12.00/1.99    inference(ennf_transformation,[],[f14])).
% 12.00/1.99  
% 12.00/1.99  fof(f23,plain,(
% 12.00/1.99    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 12.00/1.99    inference(flattening,[],[f22])).
% 12.00/1.99  
% 12.00/1.99  fof(f42,plain,(
% 12.00/1.99    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 12.00/1.99    introduced(choice_axiom,[])).
% 12.00/1.99  
% 12.00/1.99  fof(f43,plain,(
% 12.00/1.99    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 12.00/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f42])).
% 12.00/1.99  
% 12.00/1.99  fof(f77,plain,(
% 12.00/1.99    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 12.00/1.99    inference(cnf_transformation,[],[f43])).
% 12.00/1.99  
% 12.00/1.99  fof(f58,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 12.00/1.99    inference(cnf_transformation,[],[f40])).
% 12.00/1.99  
% 12.00/1.99  fof(f88,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 12.00/1.99    inference(definition_unfolding,[],[f58,f68])).
% 12.00/1.99  
% 12.00/1.99  fof(f105,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 12.00/1.99    inference(equality_resolution,[],[f88])).
% 12.00/1.99  
% 12.00/1.99  fof(f76,plain,(
% 12.00/1.99    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f43])).
% 12.00/1.99  
% 12.00/1.99  fof(f55,plain,(
% 12.00/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 12.00/1.99    inference(cnf_transformation,[],[f35])).
% 12.00/1.99  
% 12.00/1.99  fof(f98,plain,(
% 12.00/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.00/1.99    inference(equality_resolution,[],[f55])).
% 12.00/1.99  
% 12.00/1.99  fof(f59,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 12.00/1.99    inference(cnf_transformation,[],[f40])).
% 12.00/1.99  
% 12.00/1.99  fof(f87,plain,(
% 12.00/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 12.00/1.99    inference(definition_unfolding,[],[f59,f68])).
% 12.00/1.99  
% 12.00/1.99  fof(f103,plain,(
% 12.00/1.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 12.00/1.99    inference(equality_resolution,[],[f87])).
% 12.00/1.99  
% 12.00/1.99  fof(f104,plain,(
% 12.00/1.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 12.00/1.99    inference(equality_resolution,[],[f103])).
% 12.00/1.99  
% 12.00/1.99  fof(f15,conjecture,(
% 12.00/1.99    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f16,negated_conjecture,(
% 12.00/1.99    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 12.00/1.99    inference(negated_conjecture,[],[f15])).
% 12.00/1.99  
% 12.00/1.99  fof(f24,plain,(
% 12.00/1.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 12.00/1.99    inference(ennf_transformation,[],[f16])).
% 12.00/1.99  
% 12.00/1.99  fof(f44,plain,(
% 12.00/1.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 12.00/1.99    introduced(choice_axiom,[])).
% 12.00/1.99  
% 12.00/1.99  fof(f45,plain,(
% 12.00/1.99    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 12.00/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f44])).
% 12.00/1.99  
% 12.00/1.99  fof(f78,plain,(
% 12.00/1.99    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 12.00/1.99    inference(cnf_transformation,[],[f45])).
% 12.00/1.99  
% 12.00/1.99  fof(f5,axiom,(
% 12.00/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f66,plain,(
% 12.00/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f5])).
% 12.00/1.99  
% 12.00/1.99  fof(f6,axiom,(
% 12.00/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f67,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f6])).
% 12.00/1.99  
% 12.00/1.99  fof(f79,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 12.00/1.99    inference(definition_unfolding,[],[f67,f68])).
% 12.00/1.99  
% 12.00/1.99  fof(f80,plain,(
% 12.00/1.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 12.00/1.99    inference(definition_unfolding,[],[f66,f79])).
% 12.00/1.99  
% 12.00/1.99  fof(f93,plain,(
% 12.00/1.99    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 12.00/1.99    inference(definition_unfolding,[],[f78,f80])).
% 12.00/1.99  
% 12.00/1.99  cnf(c_492,plain,
% 12.00/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.00/1.99      theory(equality) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1347,plain,
% 12.00/1.99      ( r2_hidden(X0,X1)
% 12.00/1.99      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 12.00/1.99      | X0 != X2
% 12.00/1.99      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_492]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_37577,plain,
% 12.00/1.99      ( r2_hidden(X0,k1_xboole_0)
% 12.00/1.99      | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 12.00/1.99      | X0 != sK4
% 12.00/1.99      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_1347]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_37579,plain,
% 12.00/1.99      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 12.00/1.99      | r2_hidden(sK4,k1_xboole_0)
% 12.00/1.99      | sK4 != sK4
% 12.00/1.99      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_37577]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_491,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.00/1.99      theory(equality) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1342,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,X1)
% 12.00/1.99      | r1_tarski(X2,sK3(X3,X2))
% 12.00/1.99      | X2 != X0
% 12.00/1.99      | sK3(X3,X2) != X1 ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_491]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_17071,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,X1)
% 12.00/1.99      | r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 12.00/1.99      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != X1
% 12.00/1.99      | sK4 != X0 ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_1342]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_17073,plain,
% 12.00/1.99      ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 12.00/1.99      | ~ r1_tarski(sK4,sK4)
% 12.00/1.99      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
% 12.00/1.99      | sK4 != sK4 ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_17071]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1,plain,
% 12.00/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f47]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1066,plain,
% 12.00/1.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 12.00/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_8,plain,
% 12.00/1.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 12.00/1.99      inference(cnf_transformation,[],[f96]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1059,plain,
% 12.00/1.99      ( r2_hidden(X0,X1) = iProver_top
% 12.00/1.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1823,plain,
% 12.00/1.99      ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X0) = iProver_top
% 12.00/1.99      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1066,c_1059]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7,plain,
% 12.00/1.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 12.00/1.99      inference(cnf_transformation,[],[f95]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1060,plain,
% 12.00/1.99      ( r2_hidden(X0,X1) != iProver_top
% 12.00/1.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_2783,plain,
% 12.00/1.99      ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X1) != iProver_top
% 12.00/1.99      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1066,c_1060]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_8551,plain,
% 12.00/1.99      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1823,c_2783]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_17,plain,
% 12.00/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 12.00/1.99      inference(cnf_transformation,[],[f102]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1051,plain,
% 12.00/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16,plain,
% 12.00/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 12.00/1.99      inference(cnf_transformation,[],[f100]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1052,plain,
% 12.00/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_26,plain,
% 12.00/1.99      ( ~ r2_hidden(k1_xboole_0,X0) | k1_setfam_1(X0) = k1_xboole_0 ),
% 12.00/1.99      inference(cnf_transformation,[],[f75]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1043,plain,
% 12.00/1.99      ( k1_setfam_1(X0) = k1_xboole_0
% 12.00/1.99      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1581,plain,
% 12.00/1.99      ( k1_setfam_1(k2_enumset1(X0,X0,X1,k1_xboole_0)) = k1_xboole_0 ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1052,c_1043]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_25,plain,
% 12.00/1.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 12.00/1.99      inference(cnf_transformation,[],[f74]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1044,plain,
% 12.00/1.99      ( r2_hidden(X0,X1) != iProver_top
% 12.00/1.99      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1841,plain,
% 12.00/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,k1_xboole_0)) != iProver_top
% 12.00/1.99      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1581,c_1044]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_3813,plain,
% 12.00/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1051,c_1841]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 12.00/1.99      inference(cnf_transformation,[],[f57]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1058,plain,
% 12.00/1.99      ( X0 = X1
% 12.00/1.99      | r1_tarski(X1,X0) != iProver_top
% 12.00/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_3832,plain,
% 12.00/1.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_3813,c_1058]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9216,plain,
% 12.00/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_8551,c_3832]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9600,plain,
% 12.00/1.99      ( r2_hidden(X0,X1) = iProver_top
% 12.00/1.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_9216,c_1059]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_0,plain,
% 12.00/1.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f48]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1067,plain,
% 12.00/1.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 12.00/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_8546,plain,
% 12.00/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1823,c_1067]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_8908,plain,
% 12.00/1.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_8546,c_3832]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9195,plain,
% 12.00/1.99      ( r2_hidden(X0,X1) != iProver_top
% 12.00/1.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_8908,c_1060]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9619,plain,
% 12.00/1.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 12.00/1.99      inference(global_propositional_subsumption,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_9600,c_9195]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9621,plain,
% 12.00/1.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 12.00/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_9619]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9623,plain,
% 12.00/1.99      ( ~ r2_hidden(sK4,k1_xboole_0) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_9621]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_27,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,sK3(X1,X0))
% 12.00/1.99      | r1_tarski(X0,k1_setfam_1(X1))
% 12.00/1.99      | k1_xboole_0 = X1 ),
% 12.00/1.99      inference(cnf_transformation,[],[f77]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_6192,plain,
% 12.00/1.99      ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 12.00/1.99      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 12.00/1.99      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_27]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_19,plain,
% 12.00/1.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 12.00/1.99      | X0 = X1
% 12.00/1.99      | X0 = X2
% 12.00/1.99      | X0 = X3 ),
% 12.00/1.99      inference(cnf_transformation,[],[f105]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_28,plain,
% 12.00/1.99      ( r2_hidden(sK3(X0,X1),X0)
% 12.00/1.99      | r1_tarski(X1,k1_setfam_1(X0))
% 12.00/1.99      | k1_xboole_0 = X0 ),
% 12.00/1.99      inference(cnf_transformation,[],[f76]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_4945,plain,
% 12.00/1.99      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))
% 12.00/1.99      | sK3(k2_enumset1(X1,X1,X2,X3),X0) = X1
% 12.00/1.99      | sK3(k2_enumset1(X1,X1,X2,X3),X0) = X2
% 12.00/1.99      | sK3(k2_enumset1(X1,X1,X2,X3),X0) = X3
% 12.00/1.99      | k1_xboole_0 = k2_enumset1(X1,X1,X2,X3) ),
% 12.00/1.99      inference(resolution,[status(thm)],[c_19,c_28]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_4947,plain,
% 12.00/1.99      ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 12.00/1.99      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
% 12.00/1.99      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_4945]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1322,plain,
% 12.00/1.99      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 12.00/1.99      | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 12.00/1.99      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1266,plain,
% 12.00/1.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 12.00/1.99      | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_25]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1268,plain,
% 12.00/1.99      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 12.00/1.99      | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_1266]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_11,plain,
% 12.00/1.99      ( r1_tarski(X0,X0) ),
% 12.00/1.99      inference(cnf_transformation,[],[f98]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_72,plain,
% 12.00/1.99      ( r1_tarski(sK4,sK4) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_18,plain,
% 12.00/1.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 12.00/1.99      inference(cnf_transformation,[],[f104]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_59,plain,
% 12.00/1.99      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_56,plain,
% 12.00/1.99      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_19]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_29,negated_conjecture,
% 12.00/1.99      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 12.00/1.99      inference(cnf_transformation,[],[f93]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(contradiction,plain,
% 12.00/1.99      ( $false ),
% 12.00/1.99      inference(minisat,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_37579,c_17073,c_9623,c_6192,c_4947,c_1322,c_1268,c_72,
% 12.00/1.99                 c_59,c_56,c_29]) ).
% 12.00/1.99  
% 12.00/1.99  
% 12.00/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 12.00/1.99  
% 12.00/1.99  ------                               Statistics
% 12.00/1.99  
% 12.00/1.99  ------ Selected
% 12.00/1.99  
% 12.00/1.99  total_time:                             1.493
% 12.00/1.99  
%------------------------------------------------------------------------------
