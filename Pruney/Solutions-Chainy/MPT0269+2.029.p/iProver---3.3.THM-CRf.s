%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:49 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  146 (1546 expanded)
%              Number of clauses        :   64 ( 281 expanded)
%              Number of leaves         :   20 ( 447 expanded)
%              Depth                    :   24
%              Number of atoms          :  418 (3702 expanded)
%              Number of equality atoms :  244 (2528 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f50,f47,f47])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 )
   => ( k1_tarski(sK3) != sK2
      & k1_xboole_0 != sK2
      & k4_xboole_0(sK2,k1_tarski(sK3)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_tarski(sK3) != sK2
    & k1_xboole_0 != sK2
    & k4_xboole_0(sK2,k1_tarski(sK3)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f34])).

fof(f66,plain,(
    k4_xboole_0(sK2,k1_tarski(sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f95,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f66,f47,f72])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f51,f47])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f52,f47])).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f71])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f67,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f71])).

fof(f103,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k3_enumset1(X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f89])).

fof(f104,plain,(
    ! [X4,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f103])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f65,f71])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    k1_tarski(sK3) != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK2 ),
    inference(definition_unfolding,[],[f68,f72])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_907,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_906,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2180,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_907,c_906])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2392,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2180,c_0])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2394,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2392,c_13])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_912,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1276,plain,
    ( k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_26,c_0])).

cnf(c_1284,plain,
    ( k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1276,c_13])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_911,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5855,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k5_xboole_0(sK2,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_911])).

cnf(c_1424,plain,
    ( k5_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1284,c_26])).

cnf(c_5869,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5855,c_1424])).

cnf(c_14,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1278,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_14])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_910,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3926,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_910])).

cnf(c_4141,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_3926])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_925,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12,c_14])).

cnf(c_4158,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4141,c_925,c_1278])).

cnf(c_6853,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5869,c_4158])).

cnf(c_6854,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6853])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_899,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6861,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6854,c_899])).

cnf(c_6977,plain,
    ( sK0(sK2,X0,X1) = sK3
    | k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = X1
    | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_6861])).

cnf(c_7018,plain,
    ( sK0(sK2,X0,sK2) = sK3
    | k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = sK2 ),
    inference(superposition,[status(thm)],[c_6977,c_6861])).

cnf(c_7282,plain,
    ( sK0(sK2,sK2,sK2) = sK3
    | k5_xboole_0(sK2,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2394,c_7018])).

cnf(c_7356,plain,
    ( sK0(sK2,sK2,sK2) = sK3
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7282,c_1424])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_38,plain,
    ( r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_450,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1083,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_450])).

cnf(c_1084,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_7379,plain,
    ( sK0(sK2,sK2,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7356,c_25,c_35,c_38,c_1084])).

cnf(c_7382,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = sK2
    | r2_hidden(sK0(sK2,sK2,sK2),sK2) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7379,c_912])).

cnf(c_7388,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = sK2
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7382,c_7379])).

cnf(c_7389,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7388,c_1424,c_2394])).

cnf(c_21,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_898,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_905,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1801,plain,
    ( k5_xboole_0(sK2,sK2) != k1_xboole_0
    | r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_905])).

cnf(c_1804,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1801,c_1424])).

cnf(c_1805,plain,
    ( r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1804])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_908,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3322,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK2
    | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_908])).

cnf(c_24,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1067,plain,
    ( ~ r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2)
    | ~ r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1068,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK2
    | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != iProver_top
    | r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_3625,plain,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3322,c_24,c_1068,c_1805])).

cnf(c_3630,plain,
    ( r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_3625])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7389,c_3630,c_1084,c_38,c_35,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:49:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.05/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.00  
% 3.05/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/1.00  
% 3.05/1.00  ------  iProver source info
% 3.05/1.00  
% 3.05/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.05/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/1.00  git: non_committed_changes: false
% 3.05/1.00  git: last_make_outside_of_git: false
% 3.05/1.00  
% 3.05/1.00  ------ 
% 3.05/1.00  
% 3.05/1.00  ------ Input Options
% 3.05/1.00  
% 3.05/1.00  --out_options                           all
% 3.05/1.00  --tptp_safe_out                         true
% 3.05/1.00  --problem_path                          ""
% 3.05/1.00  --include_path                          ""
% 3.05/1.00  --clausifier                            res/vclausify_rel
% 3.05/1.00  --clausifier_options                    --mode clausify
% 3.05/1.00  --stdin                                 false
% 3.05/1.00  --stats_out                             all
% 3.05/1.00  
% 3.05/1.00  ------ General Options
% 3.05/1.00  
% 3.05/1.00  --fof                                   false
% 3.05/1.00  --time_out_real                         305.
% 3.05/1.00  --time_out_virtual                      -1.
% 3.05/1.00  --symbol_type_check                     false
% 3.05/1.00  --clausify_out                          false
% 3.05/1.00  --sig_cnt_out                           false
% 3.05/1.00  --trig_cnt_out                          false
% 3.05/1.00  --trig_cnt_out_tolerance                1.
% 3.05/1.00  --trig_cnt_out_sk_spl                   false
% 3.05/1.00  --abstr_cl_out                          false
% 3.05/1.00  
% 3.05/1.00  ------ Global Options
% 3.05/1.00  
% 3.05/1.00  --schedule                              default
% 3.05/1.00  --add_important_lit                     false
% 3.05/1.00  --prop_solver_per_cl                    1000
% 3.05/1.00  --min_unsat_core                        false
% 3.05/1.00  --soft_assumptions                      false
% 3.05/1.00  --soft_lemma_size                       3
% 3.05/1.00  --prop_impl_unit_size                   0
% 3.05/1.00  --prop_impl_unit                        []
% 3.05/1.00  --share_sel_clauses                     true
% 3.05/1.00  --reset_solvers                         false
% 3.05/1.00  --bc_imp_inh                            [conj_cone]
% 3.05/1.00  --conj_cone_tolerance                   3.
% 3.05/1.00  --extra_neg_conj                        none
% 3.05/1.00  --large_theory_mode                     true
% 3.05/1.00  --prolific_symb_bound                   200
% 3.05/1.00  --lt_threshold                          2000
% 3.05/1.00  --clause_weak_htbl                      true
% 3.05/1.00  --gc_record_bc_elim                     false
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing Options
% 3.05/1.00  
% 3.05/1.00  --preprocessing_flag                    true
% 3.05/1.00  --time_out_prep_mult                    0.1
% 3.05/1.00  --splitting_mode                        input
% 3.05/1.00  --splitting_grd                         true
% 3.05/1.00  --splitting_cvd                         false
% 3.05/1.00  --splitting_cvd_svl                     false
% 3.05/1.00  --splitting_nvd                         32
% 3.05/1.00  --sub_typing                            true
% 3.05/1.00  --prep_gs_sim                           true
% 3.05/1.00  --prep_unflatten                        true
% 3.05/1.00  --prep_res_sim                          true
% 3.05/1.00  --prep_upred                            true
% 3.05/1.00  --prep_sem_filter                       exhaustive
% 3.05/1.00  --prep_sem_filter_out                   false
% 3.05/1.00  --pred_elim                             true
% 3.05/1.00  --res_sim_input                         true
% 3.05/1.00  --eq_ax_congr_red                       true
% 3.05/1.00  --pure_diseq_elim                       true
% 3.05/1.00  --brand_transform                       false
% 3.05/1.00  --non_eq_to_eq                          false
% 3.05/1.00  --prep_def_merge                        true
% 3.05/1.00  --prep_def_merge_prop_impl              false
% 3.05/1.00  --prep_def_merge_mbd                    true
% 3.05/1.00  --prep_def_merge_tr_red                 false
% 3.05/1.00  --prep_def_merge_tr_cl                  false
% 3.05/1.00  --smt_preprocessing                     true
% 3.05/1.00  --smt_ac_axioms                         fast
% 3.05/1.00  --preprocessed_out                      false
% 3.05/1.00  --preprocessed_stats                    false
% 3.05/1.00  
% 3.05/1.00  ------ Abstraction refinement Options
% 3.05/1.00  
% 3.05/1.00  --abstr_ref                             []
% 3.05/1.00  --abstr_ref_prep                        false
% 3.05/1.00  --abstr_ref_until_sat                   false
% 3.05/1.00  --abstr_ref_sig_restrict                funpre
% 3.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.00  --abstr_ref_under                       []
% 3.05/1.00  
% 3.05/1.00  ------ SAT Options
% 3.05/1.00  
% 3.05/1.00  --sat_mode                              false
% 3.05/1.00  --sat_fm_restart_options                ""
% 3.05/1.00  --sat_gr_def                            false
% 3.05/1.00  --sat_epr_types                         true
% 3.05/1.00  --sat_non_cyclic_types                  false
% 3.05/1.00  --sat_finite_models                     false
% 3.05/1.00  --sat_fm_lemmas                         false
% 3.05/1.00  --sat_fm_prep                           false
% 3.05/1.00  --sat_fm_uc_incr                        true
% 3.05/1.00  --sat_out_model                         small
% 3.05/1.00  --sat_out_clauses                       false
% 3.05/1.00  
% 3.05/1.00  ------ QBF Options
% 3.05/1.00  
% 3.05/1.00  --qbf_mode                              false
% 3.05/1.00  --qbf_elim_univ                         false
% 3.05/1.00  --qbf_dom_inst                          none
% 3.05/1.00  --qbf_dom_pre_inst                      false
% 3.05/1.00  --qbf_sk_in                             false
% 3.05/1.00  --qbf_pred_elim                         true
% 3.05/1.00  --qbf_split                             512
% 3.05/1.00  
% 3.05/1.00  ------ BMC1 Options
% 3.05/1.00  
% 3.05/1.00  --bmc1_incremental                      false
% 3.05/1.00  --bmc1_axioms                           reachable_all
% 3.05/1.00  --bmc1_min_bound                        0
% 3.05/1.00  --bmc1_max_bound                        -1
% 3.05/1.00  --bmc1_max_bound_default                -1
% 3.05/1.00  --bmc1_symbol_reachability              true
% 3.05/1.00  --bmc1_property_lemmas                  false
% 3.05/1.00  --bmc1_k_induction                      false
% 3.05/1.00  --bmc1_non_equiv_states                 false
% 3.05/1.00  --bmc1_deadlock                         false
% 3.05/1.00  --bmc1_ucm                              false
% 3.05/1.00  --bmc1_add_unsat_core                   none
% 3.05/1.00  --bmc1_unsat_core_children              false
% 3.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.00  --bmc1_out_stat                         full
% 3.05/1.00  --bmc1_ground_init                      false
% 3.05/1.00  --bmc1_pre_inst_next_state              false
% 3.05/1.00  --bmc1_pre_inst_state                   false
% 3.05/1.00  --bmc1_pre_inst_reach_state             false
% 3.05/1.00  --bmc1_out_unsat_core                   false
% 3.05/1.00  --bmc1_aig_witness_out                  false
% 3.05/1.00  --bmc1_verbose                          false
% 3.05/1.00  --bmc1_dump_clauses_tptp                false
% 3.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.00  --bmc1_dump_file                        -
% 3.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.00  --bmc1_ucm_extend_mode                  1
% 3.05/1.00  --bmc1_ucm_init_mode                    2
% 3.05/1.00  --bmc1_ucm_cone_mode                    none
% 3.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.00  --bmc1_ucm_relax_model                  4
% 3.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.00  --bmc1_ucm_layered_model                none
% 3.05/1.00  --bmc1_ucm_max_lemma_size               10
% 3.05/1.00  
% 3.05/1.00  ------ AIG Options
% 3.05/1.00  
% 3.05/1.00  --aig_mode                              false
% 3.05/1.00  
% 3.05/1.00  ------ Instantiation Options
% 3.05/1.00  
% 3.05/1.00  --instantiation_flag                    true
% 3.05/1.00  --inst_sos_flag                         false
% 3.05/1.00  --inst_sos_phase                        true
% 3.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.00  --inst_lit_sel_side                     num_symb
% 3.05/1.00  --inst_solver_per_active                1400
% 3.05/1.00  --inst_solver_calls_frac                1.
% 3.05/1.00  --inst_passive_queue_type               priority_queues
% 3.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.00  --inst_passive_queues_freq              [25;2]
% 3.05/1.00  --inst_dismatching                      true
% 3.05/1.00  --inst_eager_unprocessed_to_passive     true
% 3.05/1.00  --inst_prop_sim_given                   true
% 3.05/1.00  --inst_prop_sim_new                     false
% 3.05/1.00  --inst_subs_new                         false
% 3.05/1.00  --inst_eq_res_simp                      false
% 3.05/1.00  --inst_subs_given                       false
% 3.05/1.00  --inst_orphan_elimination               true
% 3.05/1.00  --inst_learning_loop_flag               true
% 3.05/1.00  --inst_learning_start                   3000
% 3.05/1.00  --inst_learning_factor                  2
% 3.05/1.00  --inst_start_prop_sim_after_learn       3
% 3.05/1.00  --inst_sel_renew                        solver
% 3.05/1.00  --inst_lit_activity_flag                true
% 3.05/1.00  --inst_restr_to_given                   false
% 3.05/1.00  --inst_activity_threshold               500
% 3.05/1.00  --inst_out_proof                        true
% 3.05/1.00  
% 3.05/1.00  ------ Resolution Options
% 3.05/1.00  
% 3.05/1.00  --resolution_flag                       true
% 3.05/1.00  --res_lit_sel                           adaptive
% 3.05/1.00  --res_lit_sel_side                      none
% 3.05/1.00  --res_ordering                          kbo
% 3.05/1.00  --res_to_prop_solver                    active
% 3.05/1.00  --res_prop_simpl_new                    false
% 3.05/1.00  --res_prop_simpl_given                  true
% 3.05/1.00  --res_passive_queue_type                priority_queues
% 3.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.00  --res_passive_queues_freq               [15;5]
% 3.05/1.00  --res_forward_subs                      full
% 3.05/1.00  --res_backward_subs                     full
% 3.05/1.00  --res_forward_subs_resolution           true
% 3.05/1.00  --res_backward_subs_resolution          true
% 3.05/1.00  --res_orphan_elimination                true
% 3.05/1.00  --res_time_limit                        2.
% 3.05/1.00  --res_out_proof                         true
% 3.05/1.00  
% 3.05/1.00  ------ Superposition Options
% 3.05/1.00  
% 3.05/1.00  --superposition_flag                    true
% 3.05/1.00  --sup_passive_queue_type                priority_queues
% 3.05/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.05/1.00  --demod_completeness_check              fast
% 3.05/1.00  --demod_use_ground                      true
% 3.05/1.00  --sup_to_prop_solver                    passive
% 3.05/1.00  --sup_prop_simpl_new                    true
% 3.05/1.00  --sup_prop_simpl_given                  true
% 3.05/1.00  --sup_fun_splitting                     false
% 3.05/1.00  --sup_smt_interval                      50000
% 3.05/1.00  
% 3.05/1.00  ------ Superposition Simplification Setup
% 3.05/1.00  
% 3.05/1.00  --sup_indices_passive                   []
% 3.05/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_full_bw                           [BwDemod]
% 3.05/1.00  --sup_immed_triv                        [TrivRules]
% 3.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_immed_bw_main                     []
% 3.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.00  
% 3.05/1.00  ------ Combination Options
% 3.05/1.00  
% 3.05/1.00  --comb_res_mult                         3
% 3.05/1.00  --comb_sup_mult                         2
% 3.05/1.00  --comb_inst_mult                        10
% 3.05/1.00  
% 3.05/1.00  ------ Debug Options
% 3.05/1.00  
% 3.05/1.00  --dbg_backtrace                         false
% 3.05/1.00  --dbg_dump_prop_clauses                 false
% 3.05/1.00  --dbg_dump_prop_clauses_file            -
% 3.05/1.00  --dbg_out_stat                          false
% 3.05/1.00  ------ Parsing...
% 3.05/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/1.00  ------ Proving...
% 3.05/1.00  ------ Problem Properties 
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  clauses                                 26
% 3.05/1.00  conjectures                             3
% 3.05/1.00  EPR                                     3
% 3.05/1.00  Horn                                    20
% 3.05/1.00  unary                                   10
% 3.05/1.00  binary                                  6
% 3.05/1.00  lits                                    54
% 3.05/1.00  lits eq                                 22
% 3.05/1.00  fd_pure                                 0
% 3.05/1.00  fd_pseudo                               0
% 3.05/1.00  fd_cond                                 0
% 3.05/1.00  fd_pseudo_cond                          7
% 3.05/1.00  AC symbols                              0
% 3.05/1.00  
% 3.05/1.00  ------ Schedule dynamic 5 is on 
% 3.05/1.00  
% 3.05/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  ------ 
% 3.05/1.00  Current options:
% 3.05/1.00  ------ 
% 3.05/1.00  
% 3.05/1.00  ------ Input Options
% 3.05/1.00  
% 3.05/1.00  --out_options                           all
% 3.05/1.00  --tptp_safe_out                         true
% 3.05/1.00  --problem_path                          ""
% 3.05/1.00  --include_path                          ""
% 3.05/1.00  --clausifier                            res/vclausify_rel
% 3.05/1.00  --clausifier_options                    --mode clausify
% 3.05/1.00  --stdin                                 false
% 3.05/1.00  --stats_out                             all
% 3.05/1.00  
% 3.05/1.00  ------ General Options
% 3.05/1.00  
% 3.05/1.00  --fof                                   false
% 3.05/1.00  --time_out_real                         305.
% 3.05/1.00  --time_out_virtual                      -1.
% 3.05/1.00  --symbol_type_check                     false
% 3.05/1.00  --clausify_out                          false
% 3.05/1.00  --sig_cnt_out                           false
% 3.05/1.00  --trig_cnt_out                          false
% 3.05/1.00  --trig_cnt_out_tolerance                1.
% 3.05/1.00  --trig_cnt_out_sk_spl                   false
% 3.05/1.00  --abstr_cl_out                          false
% 3.05/1.00  
% 3.05/1.00  ------ Global Options
% 3.05/1.00  
% 3.05/1.00  --schedule                              default
% 3.05/1.00  --add_important_lit                     false
% 3.05/1.00  --prop_solver_per_cl                    1000
% 3.05/1.00  --min_unsat_core                        false
% 3.05/1.00  --soft_assumptions                      false
% 3.05/1.00  --soft_lemma_size                       3
% 3.05/1.00  --prop_impl_unit_size                   0
% 3.05/1.00  --prop_impl_unit                        []
% 3.05/1.00  --share_sel_clauses                     true
% 3.05/1.00  --reset_solvers                         false
% 3.05/1.00  --bc_imp_inh                            [conj_cone]
% 3.05/1.00  --conj_cone_tolerance                   3.
% 3.05/1.00  --extra_neg_conj                        none
% 3.05/1.00  --large_theory_mode                     true
% 3.05/1.00  --prolific_symb_bound                   200
% 3.05/1.00  --lt_threshold                          2000
% 3.05/1.00  --clause_weak_htbl                      true
% 3.05/1.00  --gc_record_bc_elim                     false
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing Options
% 3.05/1.00  
% 3.05/1.00  --preprocessing_flag                    true
% 3.05/1.00  --time_out_prep_mult                    0.1
% 3.05/1.00  --splitting_mode                        input
% 3.05/1.00  --splitting_grd                         true
% 3.05/1.00  --splitting_cvd                         false
% 3.05/1.00  --splitting_cvd_svl                     false
% 3.05/1.00  --splitting_nvd                         32
% 3.05/1.00  --sub_typing                            true
% 3.05/1.00  --prep_gs_sim                           true
% 3.05/1.00  --prep_unflatten                        true
% 3.05/1.00  --prep_res_sim                          true
% 3.05/1.00  --prep_upred                            true
% 3.05/1.00  --prep_sem_filter                       exhaustive
% 3.05/1.00  --prep_sem_filter_out                   false
% 3.05/1.00  --pred_elim                             true
% 3.05/1.00  --res_sim_input                         true
% 3.05/1.00  --eq_ax_congr_red                       true
% 3.05/1.00  --pure_diseq_elim                       true
% 3.05/1.00  --brand_transform                       false
% 3.05/1.00  --non_eq_to_eq                          false
% 3.05/1.00  --prep_def_merge                        true
% 3.05/1.00  --prep_def_merge_prop_impl              false
% 3.05/1.00  --prep_def_merge_mbd                    true
% 3.05/1.00  --prep_def_merge_tr_red                 false
% 3.05/1.00  --prep_def_merge_tr_cl                  false
% 3.05/1.00  --smt_preprocessing                     true
% 3.05/1.00  --smt_ac_axioms                         fast
% 3.05/1.00  --preprocessed_out                      false
% 3.05/1.00  --preprocessed_stats                    false
% 3.05/1.00  
% 3.05/1.00  ------ Abstraction refinement Options
% 3.05/1.00  
% 3.05/1.00  --abstr_ref                             []
% 3.05/1.00  --abstr_ref_prep                        false
% 3.05/1.00  --abstr_ref_until_sat                   false
% 3.05/1.00  --abstr_ref_sig_restrict                funpre
% 3.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.00  --abstr_ref_under                       []
% 3.05/1.00  
% 3.05/1.00  ------ SAT Options
% 3.05/1.00  
% 3.05/1.00  --sat_mode                              false
% 3.05/1.00  --sat_fm_restart_options                ""
% 3.05/1.00  --sat_gr_def                            false
% 3.05/1.00  --sat_epr_types                         true
% 3.05/1.00  --sat_non_cyclic_types                  false
% 3.05/1.00  --sat_finite_models                     false
% 3.05/1.00  --sat_fm_lemmas                         false
% 3.05/1.00  --sat_fm_prep                           false
% 3.05/1.00  --sat_fm_uc_incr                        true
% 3.05/1.00  --sat_out_model                         small
% 3.05/1.00  --sat_out_clauses                       false
% 3.05/1.00  
% 3.05/1.00  ------ QBF Options
% 3.05/1.00  
% 3.05/1.00  --qbf_mode                              false
% 3.05/1.00  --qbf_elim_univ                         false
% 3.05/1.00  --qbf_dom_inst                          none
% 3.05/1.00  --qbf_dom_pre_inst                      false
% 3.05/1.00  --qbf_sk_in                             false
% 3.05/1.00  --qbf_pred_elim                         true
% 3.05/1.00  --qbf_split                             512
% 3.05/1.00  
% 3.05/1.00  ------ BMC1 Options
% 3.05/1.00  
% 3.05/1.00  --bmc1_incremental                      false
% 3.05/1.00  --bmc1_axioms                           reachable_all
% 3.05/1.00  --bmc1_min_bound                        0
% 3.05/1.00  --bmc1_max_bound                        -1
% 3.05/1.00  --bmc1_max_bound_default                -1
% 3.05/1.00  --bmc1_symbol_reachability              true
% 3.05/1.00  --bmc1_property_lemmas                  false
% 3.05/1.00  --bmc1_k_induction                      false
% 3.05/1.00  --bmc1_non_equiv_states                 false
% 3.05/1.00  --bmc1_deadlock                         false
% 3.05/1.00  --bmc1_ucm                              false
% 3.05/1.00  --bmc1_add_unsat_core                   none
% 3.05/1.00  --bmc1_unsat_core_children              false
% 3.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.00  --bmc1_out_stat                         full
% 3.05/1.00  --bmc1_ground_init                      false
% 3.05/1.00  --bmc1_pre_inst_next_state              false
% 3.05/1.00  --bmc1_pre_inst_state                   false
% 3.05/1.00  --bmc1_pre_inst_reach_state             false
% 3.05/1.00  --bmc1_out_unsat_core                   false
% 3.05/1.00  --bmc1_aig_witness_out                  false
% 3.05/1.00  --bmc1_verbose                          false
% 3.05/1.00  --bmc1_dump_clauses_tptp                false
% 3.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.00  --bmc1_dump_file                        -
% 3.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.00  --bmc1_ucm_extend_mode                  1
% 3.05/1.00  --bmc1_ucm_init_mode                    2
% 3.05/1.00  --bmc1_ucm_cone_mode                    none
% 3.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.00  --bmc1_ucm_relax_model                  4
% 3.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.00  --bmc1_ucm_layered_model                none
% 3.05/1.00  --bmc1_ucm_max_lemma_size               10
% 3.05/1.00  
% 3.05/1.00  ------ AIG Options
% 3.05/1.00  
% 3.05/1.00  --aig_mode                              false
% 3.05/1.00  
% 3.05/1.00  ------ Instantiation Options
% 3.05/1.00  
% 3.05/1.00  --instantiation_flag                    true
% 3.05/1.00  --inst_sos_flag                         false
% 3.05/1.00  --inst_sos_phase                        true
% 3.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.00  --inst_lit_sel_side                     none
% 3.05/1.00  --inst_solver_per_active                1400
% 3.05/1.00  --inst_solver_calls_frac                1.
% 3.05/1.00  --inst_passive_queue_type               priority_queues
% 3.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.00  --inst_passive_queues_freq              [25;2]
% 3.05/1.00  --inst_dismatching                      true
% 3.05/1.00  --inst_eager_unprocessed_to_passive     true
% 3.05/1.00  --inst_prop_sim_given                   true
% 3.05/1.00  --inst_prop_sim_new                     false
% 3.05/1.00  --inst_subs_new                         false
% 3.05/1.00  --inst_eq_res_simp                      false
% 3.05/1.00  --inst_subs_given                       false
% 3.05/1.00  --inst_orphan_elimination               true
% 3.05/1.00  --inst_learning_loop_flag               true
% 3.05/1.00  --inst_learning_start                   3000
% 3.05/1.00  --inst_learning_factor                  2
% 3.05/1.00  --inst_start_prop_sim_after_learn       3
% 3.05/1.00  --inst_sel_renew                        solver
% 3.05/1.00  --inst_lit_activity_flag                true
% 3.05/1.00  --inst_restr_to_given                   false
% 3.05/1.00  --inst_activity_threshold               500
% 3.05/1.00  --inst_out_proof                        true
% 3.05/1.00  
% 3.05/1.00  ------ Resolution Options
% 3.05/1.00  
% 3.05/1.00  --resolution_flag                       false
% 3.05/1.00  --res_lit_sel                           adaptive
% 3.05/1.00  --res_lit_sel_side                      none
% 3.05/1.00  --res_ordering                          kbo
% 3.05/1.00  --res_to_prop_solver                    active
% 3.05/1.00  --res_prop_simpl_new                    false
% 3.05/1.00  --res_prop_simpl_given                  true
% 3.05/1.00  --res_passive_queue_type                priority_queues
% 3.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.00  --res_passive_queues_freq               [15;5]
% 3.05/1.00  --res_forward_subs                      full
% 3.05/1.00  --res_backward_subs                     full
% 3.05/1.00  --res_forward_subs_resolution           true
% 3.05/1.00  --res_backward_subs_resolution          true
% 3.05/1.00  --res_orphan_elimination                true
% 3.05/1.00  --res_time_limit                        2.
% 3.05/1.00  --res_out_proof                         true
% 3.05/1.00  
% 3.05/1.00  ------ Superposition Options
% 3.05/1.00  
% 3.05/1.00  --superposition_flag                    true
% 3.05/1.00  --sup_passive_queue_type                priority_queues
% 3.05/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.05/1.00  --demod_completeness_check              fast
% 3.05/1.00  --demod_use_ground                      true
% 3.05/1.00  --sup_to_prop_solver                    passive
% 3.05/1.00  --sup_prop_simpl_new                    true
% 3.05/1.00  --sup_prop_simpl_given                  true
% 3.05/1.00  --sup_fun_splitting                     false
% 3.05/1.00  --sup_smt_interval                      50000
% 3.05/1.00  
% 3.05/1.00  ------ Superposition Simplification Setup
% 3.05/1.00  
% 3.05/1.00  --sup_indices_passive                   []
% 3.05/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_full_bw                           [BwDemod]
% 3.05/1.00  --sup_immed_triv                        [TrivRules]
% 3.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_immed_bw_main                     []
% 3.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.00  
% 3.05/1.00  ------ Combination Options
% 3.05/1.00  
% 3.05/1.00  --comb_res_mult                         3
% 3.05/1.00  --comb_sup_mult                         2
% 3.05/1.00  --comb_inst_mult                        10
% 3.05/1.00  
% 3.05/1.00  ------ Debug Options
% 3.05/1.00  
% 3.05/1.00  --dbg_backtrace                         false
% 3.05/1.00  --dbg_dump_prop_clauses                 false
% 3.05/1.00  --dbg_dump_prop_clauses_file            -
% 3.05/1.00  --dbg_out_stat                          false
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  ------ Proving...
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  % SZS status Theorem for theBenchmark.p
% 3.05/1.00  
% 3.05/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/1.00  
% 3.05/1.00  fof(f2,axiom,(
% 3.05/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f24,plain,(
% 3.05/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.05/1.00    inference(nnf_transformation,[],[f2])).
% 3.05/1.00  
% 3.05/1.00  fof(f25,plain,(
% 3.05/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.05/1.00    inference(flattening,[],[f24])).
% 3.05/1.00  
% 3.05/1.00  fof(f42,plain,(
% 3.05/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.05/1.00    inference(cnf_transformation,[],[f25])).
% 3.05/1.00  
% 3.05/1.00  fof(f100,plain,(
% 3.05/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.05/1.00    inference(equality_resolution,[],[f42])).
% 3.05/1.00  
% 3.05/1.00  fof(f3,axiom,(
% 3.05/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f26,plain,(
% 3.05/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.05/1.00    inference(nnf_transformation,[],[f3])).
% 3.05/1.00  
% 3.05/1.00  fof(f46,plain,(
% 3.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f26])).
% 3.05/1.00  
% 3.05/1.00  fof(f4,axiom,(
% 3.05/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f47,plain,(
% 3.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.05/1.00    inference(cnf_transformation,[],[f4])).
% 3.05/1.00  
% 3.05/1.00  fof(f80,plain,(
% 3.05/1.00    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.05/1.00    inference(definition_unfolding,[],[f46,f47])).
% 3.05/1.00  
% 3.05/1.00  fof(f7,axiom,(
% 3.05/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f50,plain,(
% 3.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f7])).
% 3.05/1.00  
% 3.05/1.00  fof(f73,plain,(
% 3.05/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.05/1.00    inference(definition_unfolding,[],[f50,f47,f47])).
% 3.05/1.00  
% 3.05/1.00  fof(f6,axiom,(
% 3.05/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f49,plain,(
% 3.05/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.05/1.00    inference(cnf_transformation,[],[f6])).
% 3.05/1.00  
% 3.05/1.00  fof(f83,plain,(
% 3.05/1.00    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.05/1.00    inference(definition_unfolding,[],[f49,f47])).
% 3.05/1.00  
% 3.05/1.00  fof(f1,axiom,(
% 3.05/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f19,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.05/1.00    inference(nnf_transformation,[],[f1])).
% 3.05/1.00  
% 3.05/1.00  fof(f20,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.05/1.00    inference(flattening,[],[f19])).
% 3.05/1.00  
% 3.05/1.00  fof(f21,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.05/1.00    inference(rectify,[],[f20])).
% 3.05/1.00  
% 3.05/1.00  fof(f22,plain,(
% 3.05/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.05/1.00    introduced(choice_axiom,[])).
% 3.05/1.00  
% 3.05/1.00  fof(f23,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.05/1.00  
% 3.05/1.00  fof(f39,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f23])).
% 3.05/1.00  
% 3.05/1.00  fof(f76,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.05/1.00    inference(definition_unfolding,[],[f39,f47])).
% 3.05/1.00  
% 3.05/1.00  fof(f16,conjecture,(
% 3.05/1.00    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f17,negated_conjecture,(
% 3.05/1.00    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 3.05/1.00    inference(negated_conjecture,[],[f16])).
% 3.05/1.00  
% 3.05/1.00  fof(f18,plain,(
% 3.05/1.00    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 3.05/1.00    inference(ennf_transformation,[],[f17])).
% 3.05/1.00  
% 3.05/1.00  fof(f34,plain,(
% 3.05/1.00    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0) => (k1_tarski(sK3) != sK2 & k1_xboole_0 != sK2 & k4_xboole_0(sK2,k1_tarski(sK3)) = k1_xboole_0)),
% 3.05/1.00    introduced(choice_axiom,[])).
% 3.05/1.00  
% 3.05/1.00  fof(f35,plain,(
% 3.05/1.00    k1_tarski(sK3) != sK2 & k1_xboole_0 != sK2 & k4_xboole_0(sK2,k1_tarski(sK3)) = k1_xboole_0),
% 3.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f34])).
% 3.05/1.00  
% 3.05/1.00  fof(f66,plain,(
% 3.05/1.00    k4_xboole_0(sK2,k1_tarski(sK3)) = k1_xboole_0),
% 3.05/1.00    inference(cnf_transformation,[],[f35])).
% 3.05/1.00  
% 3.05/1.00  fof(f11,axiom,(
% 3.05/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f59,plain,(
% 3.05/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f11])).
% 3.05/1.00  
% 3.05/1.00  fof(f12,axiom,(
% 3.05/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f60,plain,(
% 3.05/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f12])).
% 3.05/1.00  
% 3.05/1.00  fof(f13,axiom,(
% 3.05/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f61,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f13])).
% 3.05/1.00  
% 3.05/1.00  fof(f14,axiom,(
% 3.05/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f62,plain,(
% 3.05/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f14])).
% 3.05/1.00  
% 3.05/1.00  fof(f70,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.05/1.00    inference(definition_unfolding,[],[f61,f62])).
% 3.05/1.00  
% 3.05/1.00  fof(f71,plain,(
% 3.05/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.05/1.00    inference(definition_unfolding,[],[f60,f70])).
% 3.05/1.00  
% 3.05/1.00  fof(f72,plain,(
% 3.05/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.05/1.00    inference(definition_unfolding,[],[f59,f71])).
% 3.05/1.00  
% 3.05/1.00  fof(f95,plain,(
% 3.05/1.00    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),
% 3.05/1.00    inference(definition_unfolding,[],[f66,f47,f72])).
% 3.05/1.00  
% 3.05/1.00  fof(f38,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.05/1.00    inference(cnf_transformation,[],[f23])).
% 3.05/1.00  
% 3.05/1.00  fof(f77,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.05/1.00    inference(definition_unfolding,[],[f38,f47])).
% 3.05/1.00  
% 3.05/1.00  fof(f96,plain,(
% 3.05/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.05/1.00    inference(equality_resolution,[],[f77])).
% 3.05/1.00  
% 3.05/1.00  fof(f8,axiom,(
% 3.05/1.00    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f51,plain,(
% 3.05/1.00    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 3.05/1.00    inference(cnf_transformation,[],[f8])).
% 3.05/1.00  
% 3.05/1.00  fof(f84,plain,(
% 3.05/1.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 3.05/1.00    inference(definition_unfolding,[],[f51,f47])).
% 3.05/1.00  
% 3.05/1.00  fof(f37,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.05/1.00    inference(cnf_transformation,[],[f23])).
% 3.05/1.00  
% 3.05/1.00  fof(f78,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.05/1.00    inference(definition_unfolding,[],[f37,f47])).
% 3.05/1.00  
% 3.05/1.00  fof(f97,plain,(
% 3.05/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.05/1.00    inference(equality_resolution,[],[f78])).
% 3.05/1.00  
% 3.05/1.00  fof(f5,axiom,(
% 3.05/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f48,plain,(
% 3.05/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.05/1.00    inference(cnf_transformation,[],[f5])).
% 3.05/1.00  
% 3.05/1.00  fof(f9,axiom,(
% 3.05/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f52,plain,(
% 3.05/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f9])).
% 3.05/1.00  
% 3.05/1.00  fof(f69,plain,(
% 3.05/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.05/1.00    inference(definition_unfolding,[],[f52,f47])).
% 3.05/1.00  
% 3.05/1.00  fof(f82,plain,(
% 3.05/1.00    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.05/1.00    inference(definition_unfolding,[],[f48,f69])).
% 3.05/1.00  
% 3.05/1.00  fof(f10,axiom,(
% 3.05/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f27,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.05/1.00    inference(nnf_transformation,[],[f10])).
% 3.05/1.00  
% 3.05/1.00  fof(f28,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.05/1.00    inference(flattening,[],[f27])).
% 3.05/1.00  
% 3.05/1.00  fof(f29,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.05/1.00    inference(rectify,[],[f28])).
% 3.05/1.00  
% 3.05/1.00  fof(f30,plain,(
% 3.05/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.05/1.00    introduced(choice_axiom,[])).
% 3.05/1.00  
% 3.05/1.00  fof(f31,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.05/1.00  
% 3.05/1.00  fof(f53,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.05/1.00    inference(cnf_transformation,[],[f31])).
% 3.05/1.00  
% 3.05/1.00  fof(f90,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 3.05/1.00    inference(definition_unfolding,[],[f53,f71])).
% 3.05/1.00  
% 3.05/1.00  fof(f105,plain,(
% 3.05/1.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.05/1.00    inference(equality_resolution,[],[f90])).
% 3.05/1.00  
% 3.05/1.00  fof(f67,plain,(
% 3.05/1.00    k1_xboole_0 != sK2),
% 3.05/1.00    inference(cnf_transformation,[],[f35])).
% 3.05/1.00  
% 3.05/1.00  fof(f54,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.05/1.00    inference(cnf_transformation,[],[f31])).
% 3.05/1.00  
% 3.05/1.00  fof(f89,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 3.05/1.00    inference(definition_unfolding,[],[f54,f71])).
% 3.05/1.00  
% 3.05/1.00  fof(f103,plain,(
% 3.05/1.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k3_enumset1(X4,X4,X4,X4,X1) != X2) )),
% 3.05/1.00    inference(equality_resolution,[],[f89])).
% 3.05/1.00  
% 3.05/1.00  fof(f104,plain,(
% 3.05/1.00    ( ! [X4,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X4,X1))) )),
% 3.05/1.00    inference(equality_resolution,[],[f103])).
% 3.05/1.00  
% 3.05/1.00  fof(f15,axiom,(
% 3.05/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f32,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.05/1.00    inference(nnf_transformation,[],[f15])).
% 3.05/1.00  
% 3.05/1.00  fof(f33,plain,(
% 3.05/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.05/1.00    inference(flattening,[],[f32])).
% 3.05/1.00  
% 3.05/1.00  fof(f65,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f33])).
% 3.05/1.00  
% 3.05/1.00  fof(f91,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.05/1.00    inference(definition_unfolding,[],[f65,f71])).
% 3.05/1.00  
% 3.05/1.00  fof(f45,plain,(
% 3.05/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.05/1.00    inference(cnf_transformation,[],[f26])).
% 3.05/1.00  
% 3.05/1.00  fof(f81,plain,(
% 3.05/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.05/1.00    inference(definition_unfolding,[],[f45,f47])).
% 3.05/1.00  
% 3.05/1.00  fof(f44,plain,(
% 3.05/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f25])).
% 3.05/1.00  
% 3.05/1.00  fof(f68,plain,(
% 3.05/1.00    k1_tarski(sK3) != sK2),
% 3.05/1.00    inference(cnf_transformation,[],[f35])).
% 3.05/1.00  
% 3.05/1.00  fof(f94,plain,(
% 3.05/1.00    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK2),
% 3.05/1.00    inference(definition_unfolding,[],[f68,f72])).
% 3.05/1.00  
% 3.05/1.00  cnf(c_9,plain,
% 3.05/1.00      ( r1_tarski(X0,X0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_907,plain,
% 3.05/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10,plain,
% 3.05/1.00      ( ~ r1_tarski(X0,X1)
% 3.05/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.05/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_906,plain,
% 3.05/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.05/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2180,plain,
% 3.05/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_907,c_906]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_0,plain,
% 3.05/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.05/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2392,plain,
% 3.05/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_2180,c_0]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_13,plain,
% 3.05/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.05/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2394,plain,
% 3.05/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.05/1.00      inference(light_normalisation,[status(thm)],[c_2392,c_13]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_3,plain,
% 3.05/1.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.05/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.05/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.05/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_912,plain,
% 3.05/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 3.05/1.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.05/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_26,negated_conjecture,
% 3.05/1.00      ( k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 3.05/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1276,plain,
% 3.05/1.00      ( k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)) ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_26,c_0]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1284,plain,
% 3.05/1.00      ( k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 3.05/1.00      inference(demodulation,[status(thm)],[c_1276,c_13]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_4,plain,
% 3.05/1.00      ( ~ r2_hidden(X0,X1)
% 3.05/1.00      | r2_hidden(X0,X2)
% 3.05/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.05/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_911,plain,
% 3.05/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.05/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.05/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_5855,plain,
% 3.05/1.00      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 3.05/1.00      | r2_hidden(X0,k5_xboole_0(sK2,sK2)) = iProver_top
% 3.05/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_1284,c_911]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1424,plain,
% 3.05/1.00      ( k5_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 3.05/1.00      inference(demodulation,[status(thm)],[c_1284,c_26]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_5869,plain,
% 3.05/1.00      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 3.05/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.05/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.05/1.00      inference(light_normalisation,[status(thm)],[c_5855,c_1424]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_14,plain,
% 3.05/1.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.05/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1278,plain,
% 3.05/1.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_0,c_14]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_5,plain,
% 3.05/1.00      ( ~ r2_hidden(X0,X1)
% 3.05/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.05/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_910,plain,
% 3.05/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.05/1.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_3926,plain,
% 3.05/1.00      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 3.05/1.00      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_0,c_910]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_4141,plain,
% 3.05/1.00      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.05/1.00      | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_1278,c_3926]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_12,plain,
% 3.05/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 3.05/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_925,plain,
% 3.05/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.05/1.00      inference(light_normalisation,[status(thm)],[c_12,c_14]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_4158,plain,
% 3.05/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.05/1.00      inference(demodulation,[status(thm)],[c_4141,c_925,c_1278]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6853,plain,
% 3.05/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 3.05/1.00      | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.05/1.00      inference(global_propositional_subsumption,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_5869,c_4158]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6854,plain,
% 3.05/1.00      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 3.05/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 3.05/1.00      inference(renaming,[status(thm)],[c_6853]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_20,plain,
% 3.05/1.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.05/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_899,plain,
% 3.05/1.00      ( X0 = X1
% 3.05/1.00      | X0 = X2
% 3.05/1.00      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6861,plain,
% 3.05/1.00      ( sK3 = X0 | r2_hidden(X0,sK2) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_6854,c_899]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6977,plain,
% 3.05/1.00      ( sK0(sK2,X0,X1) = sK3
% 3.05/1.00      | k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = X1
% 3.05/1.00      | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_912,c_6861]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_7018,plain,
% 3.05/1.00      ( sK0(sK2,X0,sK2) = sK3
% 3.05/1.00      | k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = sK2 ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_6977,c_6861]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_7282,plain,
% 3.05/1.00      ( sK0(sK2,sK2,sK2) = sK3 | k5_xboole_0(sK2,sK2) = sK2 ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_2394,c_7018]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_7356,plain,
% 3.05/1.00      ( sK0(sK2,sK2,sK2) = sK3 | sK2 = k1_xboole_0 ),
% 3.05/1.00      inference(light_normalisation,[status(thm)],[c_7282,c_1424]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_25,negated_conjecture,
% 3.05/1.00      ( k1_xboole_0 != sK2 ),
% 3.05/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_35,plain,
% 3.05/1.00      ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.05/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_19,plain,
% 3.05/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.05/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_38,plain,
% 3.05/1.00      ( r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_450,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1083,plain,
% 3.05/1.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_450]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1084,plain,
% 3.05/1.00      ( sK2 != k1_xboole_0
% 3.05/1.00      | k1_xboole_0 = sK2
% 3.05/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_1083]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_7379,plain,
% 3.05/1.00      ( sK0(sK2,sK2,sK2) = sK3 ),
% 3.05/1.00      inference(global_propositional_subsumption,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_7356,c_25,c_35,c_38,c_1084]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_7382,plain,
% 3.05/1.00      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = sK2
% 3.05/1.00      | r2_hidden(sK0(sK2,sK2,sK2),sK2) = iProver_top
% 3.05/1.00      | r2_hidden(sK3,sK2) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_7379,c_912]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_7388,plain,
% 3.05/1.00      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = sK2
% 3.05/1.00      | r2_hidden(sK3,sK2) = iProver_top ),
% 3.05/1.00      inference(light_normalisation,[status(thm)],[c_7382,c_7379]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_7389,plain,
% 3.05/1.00      ( sK2 = k1_xboole_0 | r2_hidden(sK3,sK2) = iProver_top ),
% 3.05/1.00      inference(demodulation,[status(thm)],[c_7388,c_1424,c_2394]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_21,plain,
% 3.05/1.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 3.05/1.00      | ~ r2_hidden(X1,X2)
% 3.05/1.00      | ~ r2_hidden(X0,X2) ),
% 3.05/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_898,plain,
% 3.05/1.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
% 3.05/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.05/1.00      | r2_hidden(X1,X2) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_11,plain,
% 3.05/1.00      ( r1_tarski(X0,X1)
% 3.05/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.05/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_905,plain,
% 3.05/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 3.05/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1801,plain,
% 3.05/1.00      ( k5_xboole_0(sK2,sK2) != k1_xboole_0
% 3.05/1.00      | r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_1284,c_905]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1804,plain,
% 3.05/1.00      ( k1_xboole_0 != k1_xboole_0
% 3.05/1.00      | r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.05/1.00      inference(light_normalisation,[status(thm)],[c_1801,c_1424]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1805,plain,
% 3.05/1.00      ( r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.05/1.00      inference(equality_resolution_simp,[status(thm)],[c_1804]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_7,plain,
% 3.05/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.05/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_908,plain,
% 3.05/1.00      ( X0 = X1
% 3.05/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.05/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_3322,plain,
% 3.05/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK2
% 3.05/1.00      | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_1805,c_908]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_24,negated_conjecture,
% 3.05/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK2 ),
% 3.05/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1067,plain,
% 3.05/1.00      ( ~ r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2)
% 3.05/1.00      | ~ r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 3.05/1.00      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK2 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_1068,plain,
% 3.05/1.01      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK2
% 3.05/1.01      | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != iProver_top
% 3.05/1.01      | r1_tarski(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3625,plain,
% 3.05/1.01      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != iProver_top ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_3322,c_24,c_1068,c_1805]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3630,plain,
% 3.05/1.01      ( r2_hidden(sK3,sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_898,c_3625]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(contradiction,plain,
% 3.05/1.01      ( $false ),
% 3.05/1.01      inference(minisat,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_7389,c_3630,c_1084,c_38,c_35,c_25]) ).
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/1.01  
% 3.05/1.01  ------                               Statistics
% 3.05/1.01  
% 3.05/1.01  ------ General
% 3.05/1.01  
% 3.05/1.01  abstr_ref_over_cycles:                  0
% 3.05/1.01  abstr_ref_under_cycles:                 0
% 3.05/1.01  gc_basic_clause_elim:                   0
% 3.05/1.01  forced_gc_time:                         0
% 3.05/1.01  parsing_time:                           0.012
% 3.05/1.01  unif_index_cands_time:                  0.
% 3.05/1.01  unif_index_add_time:                    0.
% 3.05/1.01  orderings_time:                         0.
% 3.05/1.01  out_proof_time:                         0.012
% 3.05/1.01  total_time:                             0.326
% 3.05/1.01  num_of_symbols:                         41
% 3.05/1.01  num_of_terms:                           8874
% 3.05/1.01  
% 3.05/1.01  ------ Preprocessing
% 3.05/1.01  
% 3.05/1.01  num_of_splits:                          0
% 3.05/1.01  num_of_split_atoms:                     0
% 3.05/1.01  num_of_reused_defs:                     0
% 3.05/1.01  num_eq_ax_congr_red:                    21
% 3.05/1.01  num_of_sem_filtered_clauses:            1
% 3.05/1.01  num_of_subtypes:                        0
% 3.05/1.01  monotx_restored_types:                  0
% 3.05/1.01  sat_num_of_epr_types:                   0
% 3.05/1.01  sat_num_of_non_cyclic_types:            0
% 3.05/1.01  sat_guarded_non_collapsed_types:        0
% 3.05/1.01  num_pure_diseq_elim:                    0
% 3.05/1.01  simp_replaced_by:                       0
% 3.05/1.01  res_preprocessed:                       119
% 3.05/1.01  prep_upred:                             0
% 3.05/1.01  prep_unflattend:                        0
% 3.05/1.01  smt_new_axioms:                         0
% 3.05/1.01  pred_elim_cands:                        2
% 3.05/1.01  pred_elim:                              0
% 3.05/1.01  pred_elim_cl:                           0
% 3.05/1.01  pred_elim_cycles:                       2
% 3.05/1.01  merged_defs:                            8
% 3.05/1.01  merged_defs_ncl:                        0
% 3.05/1.01  bin_hyper_res:                          8
% 3.05/1.01  prep_cycles:                            4
% 3.05/1.01  pred_elim_time:                         0.001
% 3.05/1.01  splitting_time:                         0.
% 3.05/1.01  sem_filter_time:                        0.
% 3.05/1.01  monotx_time:                            0.
% 3.05/1.01  subtype_inf_time:                       0.
% 3.05/1.01  
% 3.05/1.01  ------ Problem properties
% 3.05/1.01  
% 3.05/1.01  clauses:                                26
% 3.05/1.01  conjectures:                            3
% 3.05/1.01  epr:                                    3
% 3.05/1.01  horn:                                   20
% 3.05/1.01  ground:                                 3
% 3.05/1.01  unary:                                  10
% 3.05/1.01  binary:                                 6
% 3.05/1.01  lits:                                   54
% 3.05/1.01  lits_eq:                                22
% 3.05/1.01  fd_pure:                                0
% 3.05/1.01  fd_pseudo:                              0
% 3.05/1.01  fd_cond:                                0
% 3.05/1.01  fd_pseudo_cond:                         7
% 3.05/1.01  ac_symbols:                             0
% 3.05/1.01  
% 3.05/1.01  ------ Propositional Solver
% 3.05/1.01  
% 3.05/1.01  prop_solver_calls:                      27
% 3.05/1.01  prop_fast_solver_calls:                 651
% 3.05/1.01  smt_solver_calls:                       0
% 3.05/1.01  smt_fast_solver_calls:                  0
% 3.05/1.01  prop_num_of_clauses:                    2431
% 3.05/1.01  prop_preprocess_simplified:             8189
% 3.05/1.01  prop_fo_subsumed:                       6
% 3.05/1.01  prop_solver_time:                       0.
% 3.05/1.01  smt_solver_time:                        0.
% 3.05/1.01  smt_fast_solver_time:                   0.
% 3.05/1.01  prop_fast_solver_time:                  0.
% 3.05/1.01  prop_unsat_core_time:                   0.
% 3.05/1.01  
% 3.05/1.01  ------ QBF
% 3.05/1.01  
% 3.05/1.01  qbf_q_res:                              0
% 3.05/1.01  qbf_num_tautologies:                    0
% 3.05/1.01  qbf_prep_cycles:                        0
% 3.05/1.01  
% 3.05/1.01  ------ BMC1
% 3.05/1.01  
% 3.05/1.01  bmc1_current_bound:                     -1
% 3.05/1.01  bmc1_last_solved_bound:                 -1
% 3.05/1.01  bmc1_unsat_core_size:                   -1
% 3.05/1.01  bmc1_unsat_core_parents_size:           -1
% 3.05/1.01  bmc1_merge_next_fun:                    0
% 3.05/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.05/1.01  
% 3.05/1.01  ------ Instantiation
% 3.05/1.01  
% 3.05/1.01  inst_num_of_clauses:                    711
% 3.05/1.01  inst_num_in_passive:                    390
% 3.05/1.01  inst_num_in_active:                     243
% 3.05/1.01  inst_num_in_unprocessed:                78
% 3.05/1.01  inst_num_of_loops:                      300
% 3.05/1.01  inst_num_of_learning_restarts:          0
% 3.05/1.01  inst_num_moves_active_passive:          56
% 3.05/1.01  inst_lit_activity:                      0
% 3.05/1.01  inst_lit_activity_moves:                0
% 3.05/1.01  inst_num_tautologies:                   0
% 3.05/1.01  inst_num_prop_implied:                  0
% 3.05/1.01  inst_num_existing_simplified:           0
% 3.05/1.01  inst_num_eq_res_simplified:             0
% 3.05/1.01  inst_num_child_elim:                    0
% 3.05/1.01  inst_num_of_dismatching_blockings:      497
% 3.05/1.01  inst_num_of_non_proper_insts:           782
% 3.05/1.01  inst_num_of_duplicates:                 0
% 3.05/1.01  inst_inst_num_from_inst_to_res:         0
% 3.05/1.01  inst_dismatching_checking_time:         0.
% 3.05/1.01  
% 3.05/1.01  ------ Resolution
% 3.05/1.01  
% 3.05/1.01  res_num_of_clauses:                     0
% 3.05/1.01  res_num_in_passive:                     0
% 3.05/1.01  res_num_in_active:                      0
% 3.05/1.01  res_num_of_loops:                       123
% 3.05/1.01  res_forward_subset_subsumed:            195
% 3.05/1.01  res_backward_subset_subsumed:           0
% 3.05/1.01  res_forward_subsumed:                   0
% 3.05/1.01  res_backward_subsumed:                  0
% 3.05/1.01  res_forward_subsumption_resolution:     0
% 3.05/1.01  res_backward_subsumption_resolution:    0
% 3.05/1.01  res_clause_to_clause_subsumption:       512
% 3.05/1.01  res_orphan_elimination:                 0
% 3.05/1.01  res_tautology_del:                      55
% 3.05/1.01  res_num_eq_res_simplified:              0
% 3.05/1.01  res_num_sel_changes:                    0
% 3.05/1.01  res_moves_from_active_to_pass:          0
% 3.05/1.01  
% 3.05/1.01  ------ Superposition
% 3.05/1.01  
% 3.05/1.01  sup_time_total:                         0.
% 3.05/1.01  sup_time_generating:                    0.
% 3.05/1.01  sup_time_sim_full:                      0.
% 3.05/1.01  sup_time_sim_immed:                     0.
% 3.05/1.01  
% 3.05/1.01  sup_num_of_clauses:                     131
% 3.05/1.01  sup_num_in_active:                      52
% 3.05/1.01  sup_num_in_passive:                     79
% 3.05/1.01  sup_num_of_loops:                       59
% 3.05/1.01  sup_fw_superposition:                   154
% 3.05/1.01  sup_bw_superposition:                   116
% 3.05/1.01  sup_immediate_simplified:               126
% 3.05/1.01  sup_given_eliminated:                   1
% 3.05/1.01  comparisons_done:                       0
% 3.05/1.01  comparisons_avoided:                    9
% 3.05/1.01  
% 3.05/1.01  ------ Simplifications
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  sim_fw_subset_subsumed:                 7
% 3.05/1.01  sim_bw_subset_subsumed:                 4
% 3.05/1.01  sim_fw_subsumed:                        12
% 3.05/1.01  sim_bw_subsumed:                        6
% 3.05/1.01  sim_fw_subsumption_res:                 0
% 3.05/1.01  sim_bw_subsumption_res:                 0
% 3.05/1.01  sim_tautology_del:                      19
% 3.05/1.01  sim_eq_tautology_del:                   38
% 3.05/1.01  sim_eq_res_simp:                        9
% 3.05/1.01  sim_fw_demodulated:                     51
% 3.05/1.01  sim_bw_demodulated:                     10
% 3.05/1.01  sim_light_normalised:                   81
% 3.05/1.01  sim_joinable_taut:                      0
% 3.05/1.01  sim_joinable_simp:                      0
% 3.05/1.01  sim_ac_normalised:                      0
% 3.05/1.01  sim_smt_subsumption:                    0
% 3.05/1.01  
%------------------------------------------------------------------------------
