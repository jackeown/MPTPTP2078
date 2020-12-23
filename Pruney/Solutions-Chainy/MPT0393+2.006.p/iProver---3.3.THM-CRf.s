%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:34 EST 2020

% Result     : Theorem 11.14s
% Output     : CNFRefutation 11.14s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 633 expanded)
%              Number of clauses        :   71 ( 178 expanded)
%              Number of leaves         :   20 ( 125 expanded)
%              Depth                    :   24
%              Number of atoms          :  522 (3214 expanded)
%              Number of equality atoms :  267 (1419 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f43])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f81])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f111,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f104,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f105,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f104])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f102,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f103,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f102])).

fof(f12,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_setfam_1(X0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f109,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f93])).

fof(f110,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f109])).

fof(f14,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f45])).

fof(f80,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(definition_unfolding,[],[f80,f82])).

cnf(c_494,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1271,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_44406,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | X0 != sK5
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_44408,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k1_xboole_0)
    | sK5 != sK5
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_44406])).

cnf(c_29,plain,
    ( r2_hidden(sK4(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1781,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_29,c_23])).

cnf(c_493,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_29083,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK4(k2_enumset1(X1,X1,X1,X1),X3))
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | X2 != X0
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_1781,c_493])).

cnf(c_29104,plain,
    ( X0 != X1
    | k1_xboole_0 = k2_enumset1(X2,X2,X2,X2)
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,sK4(k2_enumset1(X2,X2,X2,X2),X3)) = iProver_top
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X2,X2,X2,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29083])).

cnf(c_29106,plain,
    ( sK5 != sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5)
    | r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) = iProver_top
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29104])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_993,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_986,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2363,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X0) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_986])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_994,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7575,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2363,c_994])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_978,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_979,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_27,plain,
    ( ~ r2_hidden(k1_xboole_0,X0)
    | k1_setfam_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_969,plain,
    ( k1_setfam_1(X0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1421,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_979,c_969])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_970,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1750,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_970])).

cnf(c_3353,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_1750])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_985,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3621,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3353,c_985])).

cnf(c_7631,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7575,c_3621])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_989,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_990,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4746,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_990])).

cnf(c_7043,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK1(X0,X0,k4_xboole_0(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4746,c_986])).

cnf(c_8617,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X1)
    | r2_hidden(sK1(X0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7631,c_7043])).

cnf(c_8631,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0
    | r2_hidden(sK1(X0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8617,c_7631])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_987,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7044,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK1(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4746,c_987])).

cnf(c_8618,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X1)
    | r2_hidden(sK1(X0,X0,k1_xboole_0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7631,c_7044])).

cnf(c_8626,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0
    | r2_hidden(sK1(X0,X0,k1_xboole_0),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8618,c_7631])).

cnf(c_8634,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8631,c_8626])).

cnf(c_8676,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8634,c_986])).

cnf(c_8621,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7631,c_987])).

cnf(c_9110,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8676,c_8621])).

cnf(c_9112,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9110])).

cnf(c_9114,plain,
    ( ~ r2_hidden(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9112])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,sK4(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1712,plain,
    ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1713,plain,
    ( k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5)
    | r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) != iProver_top
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1712])).

cnf(c_1259,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
    | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1260,plain,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) != iProver_top
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1259])).

cnf(c_1200,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1201,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1200])).

cnf(c_1203,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1201])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_71,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_73,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_50,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_52,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_51,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_48,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_30,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f96])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44408,c_29106,c_9114,c_1713,c_1260,c_1203,c_73,c_52,c_51,c_48,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.14/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.14/1.98  
% 11.14/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.14/1.98  
% 11.14/1.98  ------  iProver source info
% 11.14/1.98  
% 11.14/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.14/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.14/1.98  git: non_committed_changes: false
% 11.14/1.98  git: last_make_outside_of_git: false
% 11.14/1.98  
% 11.14/1.98  ------ 
% 11.14/1.98  ------ Parsing...
% 11.14/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.14/1.98  
% 11.14/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.14/1.98  
% 11.14/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.14/1.98  
% 11.14/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.14/1.98  ------ Proving...
% 11.14/1.98  ------ Problem Properties 
% 11.14/1.98  
% 11.14/1.98  
% 11.14/1.98  clauses                                 30
% 11.14/1.98  conjectures                             1
% 11.14/1.98  EPR                                     3
% 11.14/1.98  Horn                                    20
% 11.14/1.98  unary                                   8
% 11.14/1.98  binary                                  7
% 11.14/1.98  lits                                    71
% 11.14/1.98  lits eq                                 27
% 11.14/1.98  fd_pure                                 0
% 11.14/1.98  fd_pseudo                               0
% 11.14/1.98  fd_cond                                 2
% 11.14/1.98  fd_pseudo_cond                          10
% 11.14/1.98  AC symbols                              0
% 11.14/1.98  
% 11.14/1.98  ------ Input Options Time Limit: Unbounded
% 11.14/1.98  
% 11.14/1.98  
% 11.14/1.98  ------ 
% 11.14/1.98  Current options:
% 11.14/1.98  ------ 
% 11.14/1.98  
% 11.14/1.98  
% 11.14/1.98  
% 11.14/1.98  
% 11.14/1.98  ------ Proving...
% 11.14/1.98  
% 11.14/1.98  
% 11.14/1.98  % SZS status Theorem for theBenchmark.p
% 11.14/1.98  
% 11.14/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.14/1.98  
% 11.14/1.98  fof(f13,axiom,(
% 11.14/1.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f20,plain,(
% 11.14/1.98    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.14/1.98    inference(ennf_transformation,[],[f13])).
% 11.14/1.98  
% 11.14/1.98  fof(f21,plain,(
% 11.14/1.98    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.14/1.98    inference(flattening,[],[f20])).
% 11.14/1.98  
% 11.14/1.98  fof(f43,plain,(
% 11.14/1.98    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 11.14/1.98    introduced(choice_axiom,[])).
% 11.14/1.98  
% 11.14/1.98  fof(f44,plain,(
% 11.14/1.98    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 11.14/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f43])).
% 11.14/1.98  
% 11.14/1.98  fof(f78,plain,(
% 11.14/1.98    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK4(X0,X1),X0)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f44])).
% 11.14/1.98  
% 11.14/1.98  fof(f5,axiom,(
% 11.14/1.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f39,plain,(
% 11.14/1.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.14/1.98    inference(nnf_transformation,[],[f5])).
% 11.14/1.98  
% 11.14/1.98  fof(f40,plain,(
% 11.14/1.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.14/1.98    inference(rectify,[],[f39])).
% 11.14/1.98  
% 11.14/1.98  fof(f41,plain,(
% 11.14/1.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 11.14/1.98    introduced(choice_axiom,[])).
% 11.14/1.98  
% 11.14/1.98  fof(f42,plain,(
% 11.14/1.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.14/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 11.14/1.98  
% 11.14/1.98  fof(f67,plain,(
% 11.14/1.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.14/1.98    inference(cnf_transformation,[],[f42])).
% 11.14/1.98  
% 11.14/1.98  fof(f6,axiom,(
% 11.14/1.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f71,plain,(
% 11.14/1.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f6])).
% 11.14/1.98  
% 11.14/1.98  fof(f7,axiom,(
% 11.14/1.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f72,plain,(
% 11.14/1.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f7])).
% 11.14/1.98  
% 11.14/1.98  fof(f8,axiom,(
% 11.14/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f73,plain,(
% 11.14/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f8])).
% 11.14/1.98  
% 11.14/1.98  fof(f81,plain,(
% 11.14/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.14/1.98    inference(definition_unfolding,[],[f72,f73])).
% 11.14/1.98  
% 11.14/1.98  fof(f82,plain,(
% 11.14/1.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.14/1.98    inference(definition_unfolding,[],[f71,f81])).
% 11.14/1.98  
% 11.14/1.98  fof(f94,plain,(
% 11.14/1.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.14/1.98    inference(definition_unfolding,[],[f67,f82])).
% 11.14/1.98  
% 11.14/1.98  fof(f111,plain,(
% 11.14/1.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 11.14/1.98    inference(equality_resolution,[],[f94])).
% 11.14/1.98  
% 11.14/1.98  fof(f1,axiom,(
% 11.14/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f16,plain,(
% 11.14/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.14/1.98    inference(ennf_transformation,[],[f1])).
% 11.14/1.98  
% 11.14/1.98  fof(f23,plain,(
% 11.14/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.14/1.98    inference(nnf_transformation,[],[f16])).
% 11.14/1.98  
% 11.14/1.98  fof(f24,plain,(
% 11.14/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.14/1.98    inference(rectify,[],[f23])).
% 11.14/1.98  
% 11.14/1.98  fof(f25,plain,(
% 11.14/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.14/1.98    introduced(choice_axiom,[])).
% 11.14/1.98  
% 11.14/1.98  fof(f26,plain,(
% 11.14/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.14/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 11.14/1.98  
% 11.14/1.98  fof(f48,plain,(
% 11.14/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f26])).
% 11.14/1.98  
% 11.14/1.98  fof(f2,axiom,(
% 11.14/1.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f27,plain,(
% 11.14/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.14/1.98    inference(nnf_transformation,[],[f2])).
% 11.14/1.98  
% 11.14/1.98  fof(f28,plain,(
% 11.14/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.14/1.98    inference(flattening,[],[f27])).
% 11.14/1.98  
% 11.14/1.98  fof(f29,plain,(
% 11.14/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.14/1.98    inference(rectify,[],[f28])).
% 11.14/1.98  
% 11.14/1.98  fof(f30,plain,(
% 11.14/1.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.14/1.98    introduced(choice_axiom,[])).
% 11.14/1.98  
% 11.14/1.98  fof(f31,plain,(
% 11.14/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.14/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 11.14/1.98  
% 11.14/1.98  fof(f50,plain,(
% 11.14/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.14/1.98    inference(cnf_transformation,[],[f31])).
% 11.14/1.98  
% 11.14/1.98  fof(f99,plain,(
% 11.14/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 11.14/1.98    inference(equality_resolution,[],[f50])).
% 11.14/1.98  
% 11.14/1.98  fof(f49,plain,(
% 11.14/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f26])).
% 11.14/1.98  
% 11.14/1.98  fof(f4,axiom,(
% 11.14/1.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f17,plain,(
% 11.14/1.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.14/1.98    inference(ennf_transformation,[],[f4])).
% 11.14/1.98  
% 11.14/1.98  fof(f34,plain,(
% 11.14/1.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.14/1.98    inference(nnf_transformation,[],[f17])).
% 11.14/1.98  
% 11.14/1.98  fof(f35,plain,(
% 11.14/1.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.14/1.98    inference(flattening,[],[f34])).
% 11.14/1.98  
% 11.14/1.98  fof(f36,plain,(
% 11.14/1.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.14/1.98    inference(rectify,[],[f35])).
% 11.14/1.98  
% 11.14/1.98  fof(f37,plain,(
% 11.14/1.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 11.14/1.98    introduced(choice_axiom,[])).
% 11.14/1.98  
% 11.14/1.98  fof(f38,plain,(
% 11.14/1.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.14/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 11.14/1.98  
% 11.14/1.98  fof(f61,plain,(
% 11.14/1.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.14/1.98    inference(cnf_transformation,[],[f38])).
% 11.14/1.98  
% 11.14/1.98  fof(f88,plain,(
% 11.14/1.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 11.14/1.98    inference(definition_unfolding,[],[f61,f73])).
% 11.14/1.98  
% 11.14/1.98  fof(f104,plain,(
% 11.14/1.98    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 11.14/1.98    inference(equality_resolution,[],[f88])).
% 11.14/1.98  
% 11.14/1.98  fof(f105,plain,(
% 11.14/1.98    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 11.14/1.98    inference(equality_resolution,[],[f104])).
% 11.14/1.98  
% 11.14/1.98  fof(f62,plain,(
% 11.14/1.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.14/1.98    inference(cnf_transformation,[],[f38])).
% 11.14/1.98  
% 11.14/1.98  fof(f87,plain,(
% 11.14/1.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 11.14/1.98    inference(definition_unfolding,[],[f62,f73])).
% 11.14/1.98  
% 11.14/1.98  fof(f102,plain,(
% 11.14/1.98    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 11.14/1.98    inference(equality_resolution,[],[f87])).
% 11.14/1.98  
% 11.14/1.98  fof(f103,plain,(
% 11.14/1.98    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 11.14/1.98    inference(equality_resolution,[],[f102])).
% 11.14/1.98  
% 11.14/1.98  fof(f12,axiom,(
% 11.14/1.98    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_setfam_1(X0) = k1_xboole_0)),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f19,plain,(
% 11.14/1.98    ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0))),
% 11.14/1.98    inference(ennf_transformation,[],[f12])).
% 11.14/1.98  
% 11.14/1.98  fof(f77,plain,(
% 11.14/1.98    ( ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f19])).
% 11.14/1.98  
% 11.14/1.98  fof(f11,axiom,(
% 11.14/1.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f18,plain,(
% 11.14/1.98    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 11.14/1.98    inference(ennf_transformation,[],[f11])).
% 11.14/1.98  
% 11.14/1.98  fof(f76,plain,(
% 11.14/1.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f18])).
% 11.14/1.98  
% 11.14/1.98  fof(f3,axiom,(
% 11.14/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f32,plain,(
% 11.14/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.14/1.98    inference(nnf_transformation,[],[f3])).
% 11.14/1.98  
% 11.14/1.98  fof(f33,plain,(
% 11.14/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.14/1.98    inference(flattening,[],[f32])).
% 11.14/1.98  
% 11.14/1.98  fof(f58,plain,(
% 11.14/1.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f33])).
% 11.14/1.98  
% 11.14/1.98  fof(f53,plain,(
% 11.14/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f31])).
% 11.14/1.98  
% 11.14/1.98  fof(f54,plain,(
% 11.14/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.14/1.98    inference(cnf_transformation,[],[f31])).
% 11.14/1.98  
% 11.14/1.98  fof(f51,plain,(
% 11.14/1.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.14/1.98    inference(cnf_transformation,[],[f31])).
% 11.14/1.98  
% 11.14/1.98  fof(f98,plain,(
% 11.14/1.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 11.14/1.98    inference(equality_resolution,[],[f51])).
% 11.14/1.98  
% 11.14/1.98  fof(f79,plain,(
% 11.14/1.98    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK4(X0,X1))) )),
% 11.14/1.98    inference(cnf_transformation,[],[f44])).
% 11.14/1.98  
% 11.14/1.98  fof(f56,plain,(
% 11.14/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.14/1.98    inference(cnf_transformation,[],[f33])).
% 11.14/1.98  
% 11.14/1.98  fof(f101,plain,(
% 11.14/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.14/1.98    inference(equality_resolution,[],[f56])).
% 11.14/1.98  
% 11.14/1.98  fof(f68,plain,(
% 11.14/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.14/1.98    inference(cnf_transformation,[],[f42])).
% 11.14/1.98  
% 11.14/1.98  fof(f93,plain,(
% 11.14/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.14/1.98    inference(definition_unfolding,[],[f68,f82])).
% 11.14/1.98  
% 11.14/1.98  fof(f109,plain,(
% 11.14/1.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 11.14/1.98    inference(equality_resolution,[],[f93])).
% 11.14/1.98  
% 11.14/1.98  fof(f110,plain,(
% 11.14/1.98    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 11.14/1.98    inference(equality_resolution,[],[f109])).
% 11.14/1.98  
% 11.14/1.98  fof(f14,conjecture,(
% 11.14/1.98    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 11.14/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.98  
% 11.14/1.98  fof(f15,negated_conjecture,(
% 11.14/1.98    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 11.14/1.98    inference(negated_conjecture,[],[f14])).
% 11.14/1.98  
% 11.14/1.98  fof(f22,plain,(
% 11.14/1.98    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 11.14/1.98    inference(ennf_transformation,[],[f15])).
% 11.14/1.98  
% 11.14/1.98  fof(f45,plain,(
% 11.14/1.98    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK5)) != sK5),
% 11.14/1.98    introduced(choice_axiom,[])).
% 11.14/1.98  
% 11.14/1.98  fof(f46,plain,(
% 11.14/1.98    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 11.14/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f45])).
% 11.14/1.98  
% 11.14/1.98  fof(f80,plain,(
% 11.14/1.98    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 11.14/1.98    inference(cnf_transformation,[],[f46])).
% 11.14/1.98  
% 11.14/1.98  fof(f96,plain,(
% 11.14/1.98    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5),
% 11.14/1.98    inference(definition_unfolding,[],[f80,f82])).
% 11.14/1.98  
% 11.14/1.98  cnf(c_494,plain,
% 11.14/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.14/1.98      theory(equality) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1271,plain,
% 11.14/1.98      ( r2_hidden(X0,X1)
% 11.14/1.98      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 11.14/1.98      | X0 != X2
% 11.14/1.98      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_494]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_44406,plain,
% 11.14/1.98      ( r2_hidden(X0,k1_xboole_0)
% 11.14/1.98      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 11.14/1.98      | X0 != sK5
% 11.14/1.98      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_1271]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_44408,plain,
% 11.14/1.98      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 11.14/1.98      | r2_hidden(sK5,k1_xboole_0)
% 11.14/1.98      | sK5 != sK5
% 11.14/1.98      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_44406]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_29,plain,
% 11.14/1.98      ( r2_hidden(sK4(X0,X1),X0)
% 11.14/1.98      | r1_tarski(X1,k1_setfam_1(X0))
% 11.14/1.98      | k1_xboole_0 = X0 ),
% 11.14/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_23,plain,
% 11.14/1.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 11.14/1.98      inference(cnf_transformation,[],[f111]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1781,plain,
% 11.14/1.98      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 11.14/1.98      | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 11.14/1.98      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 11.14/1.98      inference(resolution,[status(thm)],[c_29,c_23]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_493,plain,
% 11.14/1.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.14/1.98      theory(equality) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_29083,plain,
% 11.14/1.98      ( ~ r1_tarski(X0,X1)
% 11.14/1.98      | r1_tarski(X2,sK4(k2_enumset1(X1,X1,X1,X1),X3))
% 11.14/1.98      | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 11.14/1.98      | X2 != X0
% 11.14/1.98      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 11.14/1.98      inference(resolution,[status(thm)],[c_1781,c_493]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_29104,plain,
% 11.14/1.98      ( X0 != X1
% 11.14/1.98      | k1_xboole_0 = k2_enumset1(X2,X2,X2,X2)
% 11.14/1.98      | r1_tarski(X1,X2) != iProver_top
% 11.14/1.98      | r1_tarski(X0,sK4(k2_enumset1(X2,X2,X2,X2),X3)) = iProver_top
% 11.14/1.98      | r1_tarski(X3,k1_setfam_1(k2_enumset1(X2,X2,X2,X2))) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_29083]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_29106,plain,
% 11.14/1.98      ( sK5 != sK5
% 11.14/1.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5)
% 11.14/1.98      | r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) = iProver_top
% 11.14/1.98      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
% 11.14/1.98      | r1_tarski(sK5,sK5) != iProver_top ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_29104]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1,plain,
% 11.14/1.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.14/1.98      inference(cnf_transformation,[],[f48]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_993,plain,
% 11.14/1.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.14/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_8,plain,
% 11.14/1.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 11.14/1.98      inference(cnf_transformation,[],[f99]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_986,plain,
% 11.14/1.98      ( r2_hidden(X0,X1) = iProver_top
% 11.14/1.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_2363,plain,
% 11.14/1.98      ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X0) = iProver_top
% 11.14/1.98      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_993,c_986]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_0,plain,
% 11.14/1.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.14/1.98      inference(cnf_transformation,[],[f49]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_994,plain,
% 11.14/1.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.14/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_7575,plain,
% 11.14/1.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_2363,c_994]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_17,plain,
% 11.14/1.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 11.14/1.98      inference(cnf_transformation,[],[f105]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_978,plain,
% 11.14/1.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_16,plain,
% 11.14/1.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 11.14/1.98      inference(cnf_transformation,[],[f103]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_979,plain,
% 11.14/1.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_27,plain,
% 11.14/1.98      ( ~ r2_hidden(k1_xboole_0,X0) | k1_setfam_1(X0) = k1_xboole_0 ),
% 11.14/1.98      inference(cnf_transformation,[],[f77]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_969,plain,
% 11.14/1.98      ( k1_setfam_1(X0) = k1_xboole_0
% 11.14/1.98      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1421,plain,
% 11.14/1.98      ( k1_setfam_1(k2_enumset1(X0,X0,X1,k1_xboole_0)) = k1_xboole_0 ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_979,c_969]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_26,plain,
% 11.14/1.98      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 11.14/1.98      inference(cnf_transformation,[],[f76]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_970,plain,
% 11.14/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.14/1.98      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1750,plain,
% 11.14/1.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,k1_xboole_0)) != iProver_top
% 11.14/1.98      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_1421,c_970]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_3353,plain,
% 11.14/1.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_978,c_1750]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_9,plain,
% 11.14/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.14/1.98      inference(cnf_transformation,[],[f58]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_985,plain,
% 11.14/1.98      ( X0 = X1
% 11.14/1.98      | r1_tarski(X1,X0) != iProver_top
% 11.14/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_3621,plain,
% 11.14/1.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_3353,c_985]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_7631,plain,
% 11.14/1.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_7575,c_3621]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_5,plain,
% 11.14/1.98      ( r2_hidden(sK1(X0,X1,X2),X0)
% 11.14/1.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.14/1.98      | k4_xboole_0(X0,X1) = X2 ),
% 11.14/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_989,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X1) = X2
% 11.14/1.98      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 11.14/1.98      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_4,plain,
% 11.14/1.98      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 11.14/1.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.14/1.98      | k4_xboole_0(X0,X1) = X2 ),
% 11.14/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_990,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X1) = X2
% 11.14/1.98      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 11.14/1.98      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_4746,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X0) = X1
% 11.14/1.98      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_989,c_990]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_7043,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
% 11.14/1.98      | r2_hidden(sK1(X0,X0,k4_xboole_0(X1,X2)),X1) = iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_4746,c_986]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_8617,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X1)
% 11.14/1.98      | r2_hidden(sK1(X0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_7631,c_7043]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_8631,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X0) = k1_xboole_0
% 11.14/1.98      | r2_hidden(sK1(X0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 11.14/1.98      inference(demodulation,[status(thm)],[c_8617,c_7631]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_7,plain,
% 11.14/1.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 11.14/1.98      inference(cnf_transformation,[],[f98]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_987,plain,
% 11.14/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.14/1.98      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_7044,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
% 11.14/1.98      | r2_hidden(sK1(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_4746,c_987]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_8618,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X1)
% 11.14/1.98      | r2_hidden(sK1(X0,X0,k1_xboole_0),X1) != iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_7631,c_7044]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_8626,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X0) = k1_xboole_0
% 11.14/1.98      | r2_hidden(sK1(X0,X0,k1_xboole_0),X1) != iProver_top ),
% 11.14/1.98      inference(demodulation,[status(thm)],[c_8618,c_7631]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_8634,plain,
% 11.14/1.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.14/1.98      inference(forward_subsumption_resolution,
% 11.14/1.98                [status(thm)],
% 11.14/1.98                [c_8631,c_8626]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_8676,plain,
% 11.14/1.98      ( r2_hidden(X0,X1) = iProver_top
% 11.14/1.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_8634,c_986]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_8621,plain,
% 11.14/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.14/1.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.14/1.98      inference(superposition,[status(thm)],[c_7631,c_987]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_9110,plain,
% 11.14/1.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.14/1.98      inference(global_propositional_subsumption,
% 11.14/1.98                [status(thm)],
% 11.14/1.98                [c_8676,c_8621]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_9112,plain,
% 11.14/1.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 11.14/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_9110]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_9114,plain,
% 11.14/1.98      ( ~ r2_hidden(sK5,k1_xboole_0) ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_9112]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_28,plain,
% 11.14/1.98      ( ~ r1_tarski(X0,sK4(X1,X0))
% 11.14/1.98      | r1_tarski(X0,k1_setfam_1(X1))
% 11.14/1.98      | k1_xboole_0 = X1 ),
% 11.14/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1712,plain,
% 11.14/1.98      ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 11.14/1.98      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 11.14/1.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_28]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1713,plain,
% 11.14/1.98      ( k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5)
% 11.14/1.98      | r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) != iProver_top
% 11.14/1.98      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_1712]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1259,plain,
% 11.14/1.98      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
% 11.14/1.98      | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 11.14/1.98      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_9]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1260,plain,
% 11.14/1.98      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 11.14/1.98      | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) != iProver_top
% 11.14/1.98      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) != iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_1259]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1200,plain,
% 11.14/1.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 11.14/1.98      | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_26]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1201,plain,
% 11.14/1.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) != iProver_top
% 11.14/1.98      | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_1200]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_1203,plain,
% 11.14/1.98      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 11.14/1.98      | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) = iProver_top ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_1201]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_11,plain,
% 11.14/1.98      ( r1_tarski(X0,X0) ),
% 11.14/1.98      inference(cnf_transformation,[],[f101]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_71,plain,
% 11.14/1.98      ( r1_tarski(X0,X0) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_73,plain,
% 11.14/1.98      ( r1_tarski(sK5,sK5) = iProver_top ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_71]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_22,plain,
% 11.14/1.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 11.14/1.98      inference(cnf_transformation,[],[f110]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_50,plain,
% 11.14/1.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 11.14/1.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_52,plain,
% 11.14/1.98      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_50]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_51,plain,
% 11.14/1.98      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_22]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_48,plain,
% 11.14/1.98      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 11.14/1.98      inference(instantiation,[status(thm)],[c_23]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(c_30,negated_conjecture,
% 11.14/1.98      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 11.14/1.98      inference(cnf_transformation,[],[f96]) ).
% 11.14/1.98  
% 11.14/1.98  cnf(contradiction,plain,
% 11.14/1.98      ( $false ),
% 11.14/1.98      inference(minisat,
% 11.14/1.98                [status(thm)],
% 11.14/1.98                [c_44408,c_29106,c_9114,c_1713,c_1260,c_1203,c_73,c_52,
% 11.14/1.98                 c_51,c_48,c_30]) ).
% 11.14/1.98  
% 11.14/1.98  
% 11.14/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.14/1.98  
% 11.14/1.98  ------                               Statistics
% 11.14/1.98  
% 11.14/1.98  ------ Selected
% 11.14/1.98  
% 11.14/1.98  total_time:                             1.218
% 11.14/1.98  
%------------------------------------------------------------------------------
