%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:56 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 848 expanded)
%              Number of clauses        :   51 ( 186 expanded)
%              Number of leaves         :   23 ( 240 expanded)
%              Depth                    :   21
%              Number of atoms          :  307 (1576 expanded)
%              Number of equality atoms :  220 (1127 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f30])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK3 != sK5
      & sK3 != sK4
      & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( sK3 != sK5
    & sK3 != sK4
    & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f27,f37])).

fof(f65,plain,(
    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f71,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f87,plain,(
    r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f65,f72,f71])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f57,f48,f63,f72])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f26])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f88,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f89,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f88])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f92,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f85])).

fof(f93,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f92])).

fof(f67,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1412,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1414,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2456,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1414])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1411,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2905,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2456,c_1411])).

cnf(c_2909,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1412,c_2905])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1721,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1727,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1721,c_7])).

cnf(c_3253,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_2909,c_1727])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1718,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_169,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != X0
    | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X1
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_170,plain,
    ( k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_1719,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_170,c_0])).

cnf(c_1734,plain,
    ( k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_1718,c_1719])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2099,plain,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_1734,c_1])).

cnf(c_3256,plain,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k1_xboole_0) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_2909,c_2099])).

cnf(c_3696,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3256,c_3253])).

cnf(c_3257,plain,
    ( k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2909,c_1734])).

cnf(c_3797,plain,
    ( k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3696,c_3257])).

cnf(c_3971,plain,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3),k1_xboole_0) = k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_3797,c_1])).

cnf(c_3998,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_3253,c_3971])).

cnf(c_13,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1406,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4076,plain,
    ( r2_hidden(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3998,c_1406])).

cnf(c_3808,plain,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3),k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,X0) ),
    inference(superposition,[status(thm)],[c_3696,c_1])).

cnf(c_3823,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,X0) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,X0) ),
    inference(demodulation,[status(thm)],[c_3808,c_1])).

cnf(c_3825,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3823,c_3696])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1403,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4009,plain,
    ( sK4 = X0
    | sK5 = X0
    | r2_hidden(X0,k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3825,c_1403])).

cnf(c_4024,plain,
    ( sK4 = sK3
    | sK5 = sK3
    | r2_hidden(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4009])).

cnf(c_1190,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1515,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_1516,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_1513,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_1514,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1513])).

cnf(c_15,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_27,plain,
    ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_24,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_19,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4076,c_4024,c_1516,c_1514,c_27,c_24,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:08:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.00/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.01  
% 3.00/1.01  ------  iProver source info
% 3.00/1.01  
% 3.00/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.01  git: non_committed_changes: false
% 3.00/1.01  git: last_make_outside_of_git: false
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     num_symb
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       true
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  ------ Parsing...
% 3.00/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.01  ------ Proving...
% 3.00/1.01  ------ Problem Properties 
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  clauses                                 20
% 3.00/1.01  conjectures                             2
% 3.00/1.01  EPR                                     3
% 3.00/1.01  Horn                                    16
% 3.00/1.01  unary                                   12
% 3.00/1.01  binary                                  3
% 3.00/1.01  lits                                    36
% 3.00/1.01  lits eq                                 22
% 3.00/1.01  fd_pure                                 0
% 3.00/1.01  fd_pseudo                               0
% 3.00/1.01  fd_cond                                 1
% 3.00/1.01  fd_pseudo_cond                          4
% 3.00/1.01  AC symbols                              0
% 3.00/1.01  
% 3.00/1.01  ------ Schedule dynamic 5 is on 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  Current options:
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     none
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       false
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ Proving...
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  % SZS status Theorem for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  fof(f3,axiom,(
% 3.00/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f24,plain,(
% 3.00/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.00/1.01    inference(ennf_transformation,[],[f3])).
% 3.00/1.01  
% 3.00/1.01  fof(f30,plain,(
% 3.00/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f31,plain,(
% 3.00/1.01    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f30])).
% 3.00/1.01  
% 3.00/1.01  fof(f42,plain,(
% 3.00/1.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.00/1.01    inference(cnf_transformation,[],[f31])).
% 3.00/1.01  
% 3.00/1.01  fof(f6,axiom,(
% 3.00/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f45,plain,(
% 3.00/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.00/1.01    inference(cnf_transformation,[],[f6])).
% 3.00/1.01  
% 3.00/1.01  fof(f2,axiom,(
% 3.00/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f22,plain,(
% 3.00/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.00/1.01    inference(rectify,[],[f2])).
% 3.00/1.01  
% 3.00/1.01  fof(f23,plain,(
% 3.00/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.00/1.01    inference(ennf_transformation,[],[f22])).
% 3.00/1.01  
% 3.00/1.01  fof(f28,plain,(
% 3.00/1.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f29,plain,(
% 3.00/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).
% 3.00/1.01  
% 3.00/1.01  fof(f41,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f29])).
% 3.00/1.01  
% 3.00/1.01  fof(f7,axiom,(
% 3.00/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f46,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f7])).
% 3.00/1.01  
% 3.00/1.01  fof(f76,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.00/1.01    inference(definition_unfolding,[],[f41,f46])).
% 3.00/1.01  
% 3.00/1.01  fof(f8,axiom,(
% 3.00/1.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f47,plain,(
% 3.00/1.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f8])).
% 3.00/1.01  
% 3.00/1.01  fof(f4,axiom,(
% 3.00/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f43,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f4])).
% 3.00/1.01  
% 3.00/1.01  fof(f73,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.00/1.01    inference(definition_unfolding,[],[f43,f46])).
% 3.00/1.01  
% 3.00/1.01  fof(f1,axiom,(
% 3.00/1.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f21,plain,(
% 3.00/1.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.00/1.01    inference(rectify,[],[f1])).
% 3.00/1.01  
% 3.00/1.01  fof(f39,plain,(
% 3.00/1.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.00/1.01    inference(cnf_transformation,[],[f21])).
% 3.00/1.01  
% 3.00/1.01  fof(f75,plain,(
% 3.00/1.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.00/1.01    inference(definition_unfolding,[],[f39,f46])).
% 3.00/1.01  
% 3.00/1.01  fof(f5,axiom,(
% 3.00/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f25,plain,(
% 3.00/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.00/1.01    inference(ennf_transformation,[],[f5])).
% 3.00/1.01  
% 3.00/1.01  fof(f44,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f25])).
% 3.00/1.01  
% 3.00/1.01  fof(f78,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f44,f46])).
% 3.00/1.01  
% 3.00/1.01  fof(f19,conjecture,(
% 3.00/1.01    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f20,negated_conjecture,(
% 3.00/1.01    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.00/1.01    inference(negated_conjecture,[],[f19])).
% 3.00/1.01  
% 3.00/1.01  fof(f27,plain,(
% 3.00/1.01    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.00/1.01    inference(ennf_transformation,[],[f20])).
% 3.00/1.01  
% 3.00/1.01  fof(f37,plain,(
% 3.00/1.01    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f38,plain,(
% 3.00/1.01    sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f27,f37])).
% 3.00/1.01  
% 3.00/1.01  fof(f65,plain,(
% 3.00/1.01    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 3.00/1.01    inference(cnf_transformation,[],[f38])).
% 3.00/1.01  
% 3.00/1.01  fof(f12,axiom,(
% 3.00/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f58,plain,(
% 3.00/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f12])).
% 3.00/1.01  
% 3.00/1.01  fof(f72,plain,(
% 3.00/1.01    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f58,f71])).
% 3.00/1.01  
% 3.00/1.01  fof(f13,axiom,(
% 3.00/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f59,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f13])).
% 3.00/1.01  
% 3.00/1.01  fof(f14,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f60,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f14])).
% 3.00/1.01  
% 3.00/1.01  fof(f15,axiom,(
% 3.00/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f61,plain,(
% 3.00/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f15])).
% 3.00/1.01  
% 3.00/1.01  fof(f16,axiom,(
% 3.00/1.01    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f62,plain,(
% 3.00/1.01    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f16])).
% 3.00/1.01  
% 3.00/1.01  fof(f17,axiom,(
% 3.00/1.01    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f63,plain,(
% 3.00/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f17])).
% 3.00/1.01  
% 3.00/1.01  fof(f68,plain,(
% 3.00/1.01    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f62,f63])).
% 3.00/1.01  
% 3.00/1.01  fof(f69,plain,(
% 3.00/1.01    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f61,f68])).
% 3.00/1.01  
% 3.00/1.01  fof(f70,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f60,f69])).
% 3.00/1.01  
% 3.00/1.01  fof(f71,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f59,f70])).
% 3.00/1.01  
% 3.00/1.01  fof(f87,plain,(
% 3.00/1.01    r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))),
% 3.00/1.01    inference(definition_unfolding,[],[f65,f72,f71])).
% 3.00/1.01  
% 3.00/1.01  fof(f11,axiom,(
% 3.00/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f57,plain,(
% 3.00/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f11])).
% 3.00/1.01  
% 3.00/1.01  fof(f9,axiom,(
% 3.00/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f48,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f9])).
% 3.00/1.01  
% 3.00/1.01  fof(f74,plain,(
% 3.00/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f57,f48,f63,f72])).
% 3.00/1.01  
% 3.00/1.01  fof(f10,axiom,(
% 3.00/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f26,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.00/1.01    inference(ennf_transformation,[],[f10])).
% 3.00/1.01  
% 3.00/1.01  fof(f32,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.00/1.01    inference(nnf_transformation,[],[f26])).
% 3.00/1.01  
% 3.00/1.01  fof(f33,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.00/1.01    inference(flattening,[],[f32])).
% 3.00/1.01  
% 3.00/1.01  fof(f34,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.00/1.01    inference(rectify,[],[f33])).
% 3.00/1.01  
% 3.00/1.01  fof(f35,plain,(
% 3.00/1.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f36,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 3.00/1.01  
% 3.00/1.01  fof(f52,plain,(
% 3.00/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.00/1.01    inference(cnf_transformation,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f83,plain,(
% 3.00/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.00/1.01    inference(definition_unfolding,[],[f52,f70])).
% 3.00/1.01  
% 3.00/1.01  fof(f88,plain,(
% 3.00/1.01    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 3.00/1.01    inference(equality_resolution,[],[f83])).
% 3.00/1.01  
% 3.00/1.01  fof(f89,plain,(
% 3.00/1.01    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 3.00/1.01    inference(equality_resolution,[],[f88])).
% 3.00/1.01  
% 3.00/1.01  fof(f49,plain,(
% 3.00/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.00/1.01    inference(cnf_transformation,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f86,plain,(
% 3.00/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.00/1.01    inference(definition_unfolding,[],[f49,f70])).
% 3.00/1.01  
% 3.00/1.01  fof(f94,plain,(
% 3.00/1.01    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 3.00/1.01    inference(equality_resolution,[],[f86])).
% 3.00/1.01  
% 3.00/1.01  fof(f50,plain,(
% 3.00/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.00/1.01    inference(cnf_transformation,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f85,plain,(
% 3.00/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.00/1.01    inference(definition_unfolding,[],[f50,f70])).
% 3.00/1.01  
% 3.00/1.01  fof(f92,plain,(
% 3.00/1.01    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.00/1.01    inference(equality_resolution,[],[f85])).
% 3.00/1.01  
% 3.00/1.01  fof(f93,plain,(
% 3.00/1.01    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 3.00/1.01    inference(equality_resolution,[],[f92])).
% 3.00/1.01  
% 3.00/1.01  fof(f67,plain,(
% 3.00/1.01    sK3 != sK5),
% 3.00/1.01    inference(cnf_transformation,[],[f38])).
% 3.00/1.01  
% 3.00/1.01  fof(f66,plain,(
% 3.00/1.01    sK3 != sK4),
% 3.00/1.01    inference(cnf_transformation,[],[f38])).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5,plain,
% 3.00/1.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1412,plain,
% 3.00/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_7,plain,
% 3.00/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3,plain,
% 3.00/1.01      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.00/1.01      | ~ r1_xboole_0(X1,X2) ),
% 3.00/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1414,plain,
% 3.00/1.01      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.00/1.01      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2456,plain,
% 3.00/1.01      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
% 3.00/1.01      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_7,c_1414]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_8,plain,
% 3.00/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1411,plain,
% 3.00/1.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2905,plain,
% 3.00/1.01      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
% 3.00/1.01      inference(forward_subsumption_resolution,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_2456,c_1411]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2909,plain,
% 3.00/1.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1412,c_2905]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_0,plain,
% 3.00/1.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.00/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1721,plain,
% 3.00/1.01      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1727,plain,
% 3.00/1.01      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.00/1.01      inference(light_normalisation,[status(thm)],[c_1721,c_7]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3253,plain,
% 3.00/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_2909,c_1727]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2,plain,
% 3.00/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1718,plain,
% 3.00/1.01      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6,plain,
% 3.00/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_20,negated_conjecture,
% 3.00/1.01      ( r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 3.00/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_169,plain,
% 3.00/1.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != X0
% 3.00/1.01      | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X1
% 3.00/1.01      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_170,plain,
% 3.00/1.01      ( k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_169]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1719,plain,
% 3.00/1.01      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_170,c_0]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1734,plain,
% 3.00/1.01      ( k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_1718,c_1719]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1,plain,
% 3.00/1.01      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.00/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2099,plain,
% 3.00/1.01      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1734,c_1]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3256,plain,
% 3.00/1.01      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k1_xboole_0) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3) ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_2909,c_2099]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3696,plain,
% 3.00/1.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3256,c_3253]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3257,plain,
% 3.00/1.01      ( k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k1_xboole_0 ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_2909,c_1734]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3797,plain,
% 3.00/1.01      ( k4_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3)) = k1_xboole_0 ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_3696,c_3257]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3971,plain,
% 3.00/1.01      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3),k1_xboole_0) = k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3797,c_1]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3998,plain,
% 3.00/1.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3253,c_3971]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_13,plain,
% 3.00/1.01      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 3.00/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1406,plain,
% 3.00/1.01      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4076,plain,
% 3.00/1.01      ( r2_hidden(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3)) = iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3998,c_1406]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3808,plain,
% 3.00/1.01      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3),k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK3))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,X0) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3696,c_1]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3823,plain,
% 3.00/1.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,X0) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,X0) ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_3808,c_1]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3825,plain,
% 3.00/1.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_3823,c_3696]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_16,plain,
% 3.00/1.01      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
% 3.00/1.01      | X0 = X1
% 3.00/1.01      | X0 = X2
% 3.00/1.01      | X0 = X3 ),
% 3.00/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1403,plain,
% 3.00/1.01      ( X0 = X1
% 3.00/1.01      | X0 = X2
% 3.00/1.01      | X0 = X3
% 3.00/1.01      | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4009,plain,
% 3.00/1.01      ( sK4 = X0
% 3.00/1.01      | sK5 = X0
% 3.00/1.01      | r2_hidden(X0,k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3)) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3825,c_1403]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4024,plain,
% 3.00/1.01      ( sK4 = sK3
% 3.00/1.01      | sK5 = sK3
% 3.00/1.01      | r2_hidden(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK5,sK3,sK3)) != iProver_top ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_4009]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1190,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1515,plain,
% 3.00/1.01      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1190]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1516,plain,
% 3.00/1.01      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1515]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1513,plain,
% 3.00/1.01      ( sK5 != X0 | sK3 != X0 | sK3 = sK5 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1190]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1514,plain,
% 3.00/1.01      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1513]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_15,plain,
% 3.00/1.01      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 3.00/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_27,plain,
% 3.00/1.01      ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_24,plain,
% 3.00/1.01      ( ~ r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.00/1.01      | sK3 = sK3 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_18,negated_conjecture,
% 3.00/1.01      ( sK3 != sK5 ),
% 3.00/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_19,negated_conjecture,
% 3.00/1.01      ( sK3 != sK4 ),
% 3.00/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(contradiction,plain,
% 3.00/1.01      ( $false ),
% 3.00/1.01      inference(minisat,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_4076,c_4024,c_1516,c_1514,c_27,c_24,c_18,c_19]) ).
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  ------                               Statistics
% 3.00/1.01  
% 3.00/1.01  ------ General
% 3.00/1.01  
% 3.00/1.01  abstr_ref_over_cycles:                  0
% 3.00/1.01  abstr_ref_under_cycles:                 0
% 3.00/1.01  gc_basic_clause_elim:                   0
% 3.00/1.01  forced_gc_time:                         0
% 3.00/1.01  parsing_time:                           0.01
% 3.00/1.01  unif_index_cands_time:                  0.
% 3.00/1.01  unif_index_add_time:                    0.
% 3.00/1.01  orderings_time:                         0.
% 3.00/1.01  out_proof_time:                         0.009
% 3.00/1.01  total_time:                             0.15
% 3.00/1.01  num_of_symbols:                         45
% 3.00/1.01  num_of_terms:                           4779
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing
% 3.00/1.01  
% 3.00/1.01  num_of_splits:                          0
% 3.00/1.01  num_of_split_atoms:                     0
% 3.00/1.01  num_of_reused_defs:                     0
% 3.00/1.01  num_eq_ax_congr_red:                    48
% 3.00/1.01  num_of_sem_filtered_clauses:            1
% 3.00/1.01  num_of_subtypes:                        0
% 3.00/1.01  monotx_restored_types:                  0
% 3.00/1.01  sat_num_of_epr_types:                   0
% 3.00/1.01  sat_num_of_non_cyclic_types:            0
% 3.00/1.01  sat_guarded_non_collapsed_types:        0
% 3.00/1.01  num_pure_diseq_elim:                    0
% 3.00/1.01  simp_replaced_by:                       0
% 3.00/1.01  res_preprocessed:                       96
% 3.00/1.01  prep_upred:                             0
% 3.00/1.01  prep_unflattend:                        72
% 3.00/1.01  smt_new_axioms:                         0
% 3.00/1.01  pred_elim_cands:                        2
% 3.00/1.01  pred_elim:                              1
% 3.00/1.01  pred_elim_cl:                           1
% 3.00/1.01  pred_elim_cycles:                       5
% 3.00/1.01  merged_defs:                            0
% 3.00/1.01  merged_defs_ncl:                        0
% 3.00/1.01  bin_hyper_res:                          0
% 3.00/1.01  prep_cycles:                            4
% 3.00/1.01  pred_elim_time:                         0.014
% 3.00/1.01  splitting_time:                         0.
% 3.00/1.01  sem_filter_time:                        0.
% 3.00/1.01  monotx_time:                            0.
% 3.00/1.01  subtype_inf_time:                       0.
% 3.00/1.01  
% 3.00/1.01  ------ Problem properties
% 3.00/1.01  
% 3.00/1.01  clauses:                                20
% 3.00/1.01  conjectures:                            2
% 3.00/1.01  epr:                                    3
% 3.00/1.01  horn:                                   16
% 3.00/1.01  ground:                                 3
% 3.00/1.01  unary:                                  12
% 3.00/1.01  binary:                                 3
% 3.00/1.01  lits:                                   36
% 3.00/1.01  lits_eq:                                22
% 3.00/1.01  fd_pure:                                0
% 3.00/1.01  fd_pseudo:                              0
% 3.00/1.01  fd_cond:                                1
% 3.00/1.01  fd_pseudo_cond:                         4
% 3.00/1.01  ac_symbols:                             0
% 3.00/1.01  
% 3.00/1.01  ------ Propositional Solver
% 3.00/1.01  
% 3.00/1.01  prop_solver_calls:                      26
% 3.00/1.01  prop_fast_solver_calls:                 661
% 3.00/1.01  smt_solver_calls:                       0
% 3.00/1.01  smt_fast_solver_calls:                  0
% 3.00/1.01  prop_num_of_clauses:                    1388
% 3.00/1.01  prop_preprocess_simplified:             4781
% 3.00/1.01  prop_fo_subsumed:                       5
% 3.00/1.01  prop_solver_time:                       0.
% 3.00/1.01  smt_solver_time:                        0.
% 3.00/1.01  smt_fast_solver_time:                   0.
% 3.00/1.01  prop_fast_solver_time:                  0.
% 3.00/1.01  prop_unsat_core_time:                   0.
% 3.00/1.01  
% 3.00/1.01  ------ QBF
% 3.00/1.01  
% 3.00/1.01  qbf_q_res:                              0
% 3.00/1.01  qbf_num_tautologies:                    0
% 3.00/1.01  qbf_prep_cycles:                        0
% 3.00/1.01  
% 3.00/1.01  ------ BMC1
% 3.00/1.01  
% 3.00/1.01  bmc1_current_bound:                     -1
% 3.00/1.01  bmc1_last_solved_bound:                 -1
% 3.00/1.01  bmc1_unsat_core_size:                   -1
% 3.00/1.01  bmc1_unsat_core_parents_size:           -1
% 3.00/1.01  bmc1_merge_next_fun:                    0
% 3.00/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation
% 3.00/1.01  
% 3.00/1.01  inst_num_of_clauses:                    430
% 3.00/1.01  inst_num_in_passive:                    87
% 3.00/1.01  inst_num_in_active:                     204
% 3.00/1.01  inst_num_in_unprocessed:                139
% 3.00/1.01  inst_num_of_loops:                      210
% 3.00/1.01  inst_num_of_learning_restarts:          0
% 3.00/1.01  inst_num_moves_active_passive:          5
% 3.00/1.01  inst_lit_activity:                      0
% 3.00/1.01  inst_lit_activity_moves:                0
% 3.00/1.01  inst_num_tautologies:                   0
% 3.00/1.01  inst_num_prop_implied:                  0
% 3.00/1.01  inst_num_existing_simplified:           0
% 3.00/1.01  inst_num_eq_res_simplified:             0
% 3.00/1.01  inst_num_child_elim:                    0
% 3.00/1.01  inst_num_of_dismatching_blockings:      31
% 3.00/1.01  inst_num_of_non_proper_insts:           241
% 3.00/1.01  inst_num_of_duplicates:                 0
% 3.00/1.01  inst_inst_num_from_inst_to_res:         0
% 3.00/1.01  inst_dismatching_checking_time:         0.
% 3.00/1.01  
% 3.00/1.01  ------ Resolution
% 3.00/1.01  
% 3.00/1.01  res_num_of_clauses:                     0
% 3.00/1.01  res_num_in_passive:                     0
% 3.00/1.01  res_num_in_active:                      0
% 3.00/1.01  res_num_of_loops:                       100
% 3.00/1.01  res_forward_subset_subsumed:            48
% 3.00/1.01  res_backward_subset_subsumed:           0
% 3.00/1.01  res_forward_subsumed:                   0
% 3.00/1.01  res_backward_subsumed:                  0
% 3.00/1.01  res_forward_subsumption_resolution:     0
% 3.00/1.01  res_backward_subsumption_resolution:    0
% 3.00/1.01  res_clause_to_clause_subsumption:       252
% 3.00/1.01  res_orphan_elimination:                 0
% 3.00/1.01  res_tautology_del:                      11
% 3.00/1.01  res_num_eq_res_simplified:              0
% 3.00/1.01  res_num_sel_changes:                    0
% 3.00/1.01  res_moves_from_active_to_pass:          0
% 3.00/1.01  
% 3.00/1.01  ------ Superposition
% 3.00/1.01  
% 3.00/1.01  sup_time_total:                         0.
% 3.00/1.01  sup_time_generating:                    0.
% 3.00/1.01  sup_time_sim_full:                      0.
% 3.00/1.01  sup_time_sim_immed:                     0.
% 3.00/1.01  
% 3.00/1.01  sup_num_of_clauses:                     56
% 3.00/1.01  sup_num_in_active:                      25
% 3.00/1.01  sup_num_in_passive:                     31
% 3.00/1.01  sup_num_of_loops:                       41
% 3.00/1.01  sup_fw_superposition:                   27
% 3.00/1.01  sup_bw_superposition:                   53
% 3.00/1.01  sup_immediate_simplified:               34
% 3.00/1.01  sup_given_eliminated:                   4
% 3.00/1.01  comparisons_done:                       0
% 3.00/1.01  comparisons_avoided:                    6
% 3.00/1.01  
% 3.00/1.01  ------ Simplifications
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  sim_fw_subset_subsumed:                 4
% 3.00/1.01  sim_bw_subset_subsumed:                 1
% 3.00/1.01  sim_fw_subsumed:                        15
% 3.00/1.01  sim_bw_subsumed:                        1
% 3.00/1.01  sim_fw_subsumption_res:                 1
% 3.00/1.01  sim_bw_subsumption_res:                 0
% 3.00/1.01  sim_tautology_del:                      2
% 3.00/1.01  sim_eq_tautology_del:                   2
% 3.00/1.01  sim_eq_res_simp:                        0
% 3.00/1.01  sim_fw_demodulated:                     16
% 3.00/1.01  sim_bw_demodulated:                     22
% 3.00/1.01  sim_light_normalised:                   13
% 3.00/1.01  sim_joinable_taut:                      0
% 3.00/1.01  sim_joinable_simp:                      0
% 3.00/1.01  sim_ac_normalised:                      0
% 3.00/1.01  sim_smt_subsumption:                    0
% 3.00/1.01  
%------------------------------------------------------------------------------
