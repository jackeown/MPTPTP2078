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
% DateTime   : Thu Dec  3 11:41:35 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 145 expanded)
%              Number of clauses        :   33 (  34 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  388 ( 541 expanded)
%              Number of equality atoms :  189 ( 278 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f39])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f74])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f104,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f95,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f96,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f95])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f102,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f86])).

fof(f103,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f102])).

fof(f13,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f41])).

fof(f73,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f73,f75])).

cnf(c_347,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_24391,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_24393,plain,
    ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | ~ r1_tarski(sK4,sK4)
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_24391])).

cnf(c_26,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_24344,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_26,c_22])).

cnf(c_24346,plain,
    ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_24344])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,sK3(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_24204,plain,
    ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_346,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_21768,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_23921,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | X0 != sK4
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_21768])).

cnf(c_23923,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_23921])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6543,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6548,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7726,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_6548])).

cnf(c_7938,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6543,c_7726])).

cnf(c_7954,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7938])).

cnf(c_7956,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7954])).

cnf(c_24,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6861,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1880,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_69,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_21,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_44,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_41,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_27,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f89])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24393,c_24346,c_24204,c_23923,c_7956,c_6861,c_1880,c_69,c_44,c_41,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.91/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/1.53  
% 7.91/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.53  
% 7.91/1.53  ------  iProver source info
% 7.91/1.53  
% 7.91/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.53  git: non_committed_changes: false
% 7.91/1.53  git: last_make_outside_of_git: false
% 7.91/1.53  
% 7.91/1.53  ------ 
% 7.91/1.53  ------ Parsing...
% 7.91/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  ------ Proving...
% 7.91/1.53  ------ Problem Properties 
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  clauses                                 27
% 7.91/1.53  conjectures                             1
% 7.91/1.53  EPR                                     2
% 7.91/1.53  Horn                                    18
% 7.91/1.53  unary                                   8
% 7.91/1.53  binary                                  5
% 7.91/1.53  lits                                    64
% 7.91/1.53  lits eq                                 27
% 7.91/1.53  fd_pure                                 0
% 7.91/1.53  fd_pseudo                               0
% 7.91/1.53  fd_cond                                 2
% 7.91/1.53  fd_pseudo_cond                          10
% 7.91/1.53  AC symbols                              0
% 7.91/1.53  
% 7.91/1.53  ------ Input Options Time Limit: Unbounded
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing...
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.91/1.53  Current options:
% 7.91/1.53  ------ 
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing...
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing...
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.53  
% 7.91/1.53  ------ Proving...
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  % SZS status Theorem for theBenchmark.p
% 7.91/1.53  
% 7.91/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.91/1.53  
% 7.91/1.53  fof(f12,axiom,(
% 7.91/1.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f20,plain,(
% 7.91/1.53    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 7.91/1.53    inference(ennf_transformation,[],[f12])).
% 7.91/1.53  
% 7.91/1.53  fof(f21,plain,(
% 7.91/1.53    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 7.91/1.53    inference(flattening,[],[f20])).
% 7.91/1.53  
% 7.91/1.53  fof(f39,plain,(
% 7.91/1.53    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 7.91/1.53    introduced(choice_axiom,[])).
% 7.91/1.53  
% 7.91/1.53  fof(f40,plain,(
% 7.91/1.53    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 7.91/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f39])).
% 7.91/1.53  
% 7.91/1.53  fof(f71,plain,(
% 7.91/1.53    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f40])).
% 7.91/1.53  
% 7.91/1.53  fof(f6,axiom,(
% 7.91/1.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f35,plain,(
% 7.91/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.91/1.53    inference(nnf_transformation,[],[f6])).
% 7.91/1.53  
% 7.91/1.53  fof(f36,plain,(
% 7.91/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.91/1.53    inference(rectify,[],[f35])).
% 7.91/1.53  
% 7.91/1.53  fof(f37,plain,(
% 7.91/1.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.91/1.53    introduced(choice_axiom,[])).
% 7.91/1.53  
% 7.91/1.53  fof(f38,plain,(
% 7.91/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.91/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 7.91/1.53  
% 7.91/1.53  fof(f62,plain,(
% 7.91/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.91/1.53    inference(cnf_transformation,[],[f38])).
% 7.91/1.53  
% 7.91/1.53  fof(f7,axiom,(
% 7.91/1.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f66,plain,(
% 7.91/1.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f7])).
% 7.91/1.53  
% 7.91/1.53  fof(f8,axiom,(
% 7.91/1.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f67,plain,(
% 7.91/1.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f8])).
% 7.91/1.53  
% 7.91/1.53  fof(f9,axiom,(
% 7.91/1.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f68,plain,(
% 7.91/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f9])).
% 7.91/1.53  
% 7.91/1.53  fof(f74,plain,(
% 7.91/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.91/1.53    inference(definition_unfolding,[],[f67,f68])).
% 7.91/1.53  
% 7.91/1.53  fof(f75,plain,(
% 7.91/1.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.91/1.53    inference(definition_unfolding,[],[f66,f74])).
% 7.91/1.53  
% 7.91/1.53  fof(f87,plain,(
% 7.91/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.91/1.53    inference(definition_unfolding,[],[f62,f75])).
% 7.91/1.53  
% 7.91/1.53  fof(f104,plain,(
% 7.91/1.53    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.91/1.53    inference(equality_resolution,[],[f87])).
% 7.91/1.53  
% 7.91/1.53  fof(f72,plain,(
% 7.91/1.53    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 7.91/1.53    inference(cnf_transformation,[],[f40])).
% 7.91/1.53  
% 7.91/1.53  fof(f5,axiom,(
% 7.91/1.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f17,plain,(
% 7.91/1.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.91/1.53    inference(ennf_transformation,[],[f5])).
% 7.91/1.53  
% 7.91/1.53  fof(f30,plain,(
% 7.91/1.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.91/1.53    inference(nnf_transformation,[],[f17])).
% 7.91/1.53  
% 7.91/1.53  fof(f31,plain,(
% 7.91/1.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.91/1.53    inference(flattening,[],[f30])).
% 7.91/1.53  
% 7.91/1.53  fof(f32,plain,(
% 7.91/1.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.91/1.53    inference(rectify,[],[f31])).
% 7.91/1.53  
% 7.91/1.53  fof(f33,plain,(
% 7.91/1.53    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.91/1.53    introduced(choice_axiom,[])).
% 7.91/1.53  
% 7.91/1.53  fof(f34,plain,(
% 7.91/1.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.91/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 7.91/1.53  
% 7.91/1.53  fof(f57,plain,(
% 7.91/1.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.91/1.53    inference(cnf_transformation,[],[f34])).
% 7.91/1.53  
% 7.91/1.53  fof(f80,plain,(
% 7.91/1.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.91/1.53    inference(definition_unfolding,[],[f57,f68])).
% 7.91/1.53  
% 7.91/1.53  fof(f95,plain,(
% 7.91/1.53    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 7.91/1.53    inference(equality_resolution,[],[f80])).
% 7.91/1.53  
% 7.91/1.53  fof(f96,plain,(
% 7.91/1.53    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 7.91/1.53    inference(equality_resolution,[],[f95])).
% 7.91/1.53  
% 7.91/1.53  fof(f3,axiom,(
% 7.91/1.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f52,plain,(
% 7.91/1.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.91/1.53    inference(cnf_transformation,[],[f3])).
% 7.91/1.53  
% 7.91/1.53  fof(f1,axiom,(
% 7.91/1.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f23,plain,(
% 7.91/1.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.91/1.53    inference(nnf_transformation,[],[f1])).
% 7.91/1.53  
% 7.91/1.53  fof(f24,plain,(
% 7.91/1.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.91/1.53    inference(flattening,[],[f23])).
% 7.91/1.53  
% 7.91/1.53  fof(f25,plain,(
% 7.91/1.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.91/1.53    inference(rectify,[],[f24])).
% 7.91/1.53  
% 7.91/1.53  fof(f26,plain,(
% 7.91/1.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.91/1.53    introduced(choice_axiom,[])).
% 7.91/1.53  
% 7.91/1.53  fof(f27,plain,(
% 7.91/1.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.91/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 7.91/1.53  
% 7.91/1.53  fof(f44,plain,(
% 7.91/1.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.91/1.53    inference(cnf_transformation,[],[f27])).
% 7.91/1.53  
% 7.91/1.53  fof(f91,plain,(
% 7.91/1.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.91/1.53    inference(equality_resolution,[],[f44])).
% 7.91/1.53  
% 7.91/1.53  fof(f11,axiom,(
% 7.91/1.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f19,plain,(
% 7.91/1.53    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 7.91/1.53    inference(ennf_transformation,[],[f11])).
% 7.91/1.53  
% 7.91/1.53  fof(f70,plain,(
% 7.91/1.53    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f19])).
% 7.91/1.53  
% 7.91/1.53  fof(f2,axiom,(
% 7.91/1.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f28,plain,(
% 7.91/1.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.91/1.53    inference(nnf_transformation,[],[f2])).
% 7.91/1.53  
% 7.91/1.53  fof(f29,plain,(
% 7.91/1.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.91/1.53    inference(flattening,[],[f28])).
% 7.91/1.53  
% 7.91/1.53  fof(f51,plain,(
% 7.91/1.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f29])).
% 7.91/1.53  
% 7.91/1.53  fof(f49,plain,(
% 7.91/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.91/1.53    inference(cnf_transformation,[],[f29])).
% 7.91/1.53  
% 7.91/1.53  fof(f94,plain,(
% 7.91/1.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.91/1.53    inference(equality_resolution,[],[f49])).
% 7.91/1.53  
% 7.91/1.53  fof(f63,plain,(
% 7.91/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.91/1.53    inference(cnf_transformation,[],[f38])).
% 7.91/1.53  
% 7.91/1.53  fof(f86,plain,(
% 7.91/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.91/1.53    inference(definition_unfolding,[],[f63,f75])).
% 7.91/1.53  
% 7.91/1.53  fof(f102,plain,(
% 7.91/1.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 7.91/1.53    inference(equality_resolution,[],[f86])).
% 7.91/1.53  
% 7.91/1.53  fof(f103,plain,(
% 7.91/1.53    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 7.91/1.53    inference(equality_resolution,[],[f102])).
% 7.91/1.53  
% 7.91/1.53  fof(f13,conjecture,(
% 7.91/1.53    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.91/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f14,negated_conjecture,(
% 7.91/1.53    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.91/1.53    inference(negated_conjecture,[],[f13])).
% 7.91/1.53  
% 7.91/1.53  fof(f22,plain,(
% 7.91/1.53    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 7.91/1.53    inference(ennf_transformation,[],[f14])).
% 7.91/1.53  
% 7.91/1.53  fof(f41,plain,(
% 7.91/1.53    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 7.91/1.53    introduced(choice_axiom,[])).
% 7.91/1.53  
% 7.91/1.53  fof(f42,plain,(
% 7.91/1.53    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 7.91/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f41])).
% 7.91/1.53  
% 7.91/1.53  fof(f73,plain,(
% 7.91/1.53    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 7.91/1.53    inference(cnf_transformation,[],[f42])).
% 7.91/1.53  
% 7.91/1.53  fof(f89,plain,(
% 7.91/1.53    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 7.91/1.53    inference(definition_unfolding,[],[f73,f75])).
% 7.91/1.53  
% 7.91/1.53  cnf(c_347,plain,
% 7.91/1.53      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.91/1.53      theory(equality) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_24391,plain,
% 7.91/1.53      ( ~ r1_tarski(X0,X1)
% 7.91/1.53      | r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 7.91/1.53      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != X1
% 7.91/1.53      | sK4 != X0 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_347]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_24393,plain,
% 7.91/1.53      ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 7.91/1.53      | ~ r1_tarski(sK4,sK4)
% 7.91/1.53      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
% 7.91/1.53      | sK4 != sK4 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_24391]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_26,plain,
% 7.91/1.53      ( r1_tarski(X0,k1_setfam_1(X1))
% 7.91/1.53      | r2_hidden(sK3(X1,X0),X1)
% 7.91/1.53      | k1_xboole_0 = X1 ),
% 7.91/1.53      inference(cnf_transformation,[],[f71]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_22,plain,
% 7.91/1.53      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.91/1.53      inference(cnf_transformation,[],[f104]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_24344,plain,
% 7.91/1.53      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 7.91/1.53      | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 7.91/1.53      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 7.91/1.53      inference(resolution,[status(thm)],[c_26,c_22]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_24346,plain,
% 7.91/1.53      ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 7.91/1.53      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
% 7.91/1.53      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_24344]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_25,plain,
% 7.91/1.53      ( ~ r1_tarski(X0,sK3(X1,X0))
% 7.91/1.53      | r1_tarski(X0,k1_setfam_1(X1))
% 7.91/1.53      | k1_xboole_0 = X1 ),
% 7.91/1.53      inference(cnf_transformation,[],[f72]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_24204,plain,
% 7.91/1.53      ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 7.91/1.53      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 7.91/1.53      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_25]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_346,plain,
% 7.91/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.91/1.53      theory(equality) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_21768,plain,
% 7.91/1.53      ( r2_hidden(X0,X1)
% 7.91/1.53      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 7.91/1.53      | X0 != X2
% 7.91/1.53      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_346]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_23921,plain,
% 7.91/1.53      ( r2_hidden(X0,k1_xboole_0)
% 7.91/1.53      | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.91/1.53      | X0 != sK4
% 7.91/1.53      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_21768]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_23923,plain,
% 7.91/1.53      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.91/1.53      | r2_hidden(sK4,k1_xboole_0)
% 7.91/1.53      | sK4 != sK4
% 7.91/1.53      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_23921]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_15,plain,
% 7.91/1.53      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 7.91/1.53      inference(cnf_transformation,[],[f96]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_6543,plain,
% 7.91/1.53      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_9,plain,
% 7.91/1.53      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.91/1.53      inference(cnf_transformation,[],[f52]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4,plain,
% 7.91/1.53      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.91/1.53      inference(cnf_transformation,[],[f91]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_6548,plain,
% 7.91/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.91/1.53      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_7726,plain,
% 7.91/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.91/1.53      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_9,c_6548]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_7938,plain,
% 7.91/1.53      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_6543,c_7726]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_7954,plain,
% 7.91/1.53      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.91/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_7938]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_7956,plain,
% 7.91/1.53      ( ~ r2_hidden(sK4,k1_xboole_0) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_7954]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_24,plain,
% 7.91/1.53      ( r1_tarski(k1_setfam_1(X0),X1) | ~ r2_hidden(X1,X0) ),
% 7.91/1.53      inference(cnf_transformation,[],[f70]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_6861,plain,
% 7.91/1.53      ( r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 7.91/1.53      | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_24]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_6,plain,
% 7.91/1.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.91/1.53      inference(cnf_transformation,[],[f51]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1880,plain,
% 7.91/1.53      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 7.91/1.53      | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 7.91/1.53      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_6]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_8,plain,
% 7.91/1.53      ( r1_tarski(X0,X0) ),
% 7.91/1.53      inference(cnf_transformation,[],[f94]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_69,plain,
% 7.91/1.53      ( r1_tarski(sK4,sK4) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_8]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_21,plain,
% 7.91/1.53      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 7.91/1.53      inference(cnf_transformation,[],[f103]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_44,plain,
% 7.91/1.53      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_21]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_41,plain,
% 7.91/1.53      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_22]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_27,negated_conjecture,
% 7.91/1.53      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 7.91/1.53      inference(cnf_transformation,[],[f89]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(contradiction,plain,
% 7.91/1.53      ( $false ),
% 7.91/1.53      inference(minisat,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_24393,c_24346,c_24204,c_23923,c_7956,c_6861,c_1880,
% 7.91/1.53                 c_69,c_44,c_41,c_27]) ).
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.91/1.53  
% 7.91/1.53  ------                               Statistics
% 7.91/1.53  
% 7.91/1.53  ------ Selected
% 7.91/1.53  
% 7.91/1.53  total_time:                             0.801
% 7.91/1.53  
%------------------------------------------------------------------------------
