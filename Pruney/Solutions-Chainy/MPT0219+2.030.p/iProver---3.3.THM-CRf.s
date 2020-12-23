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
% DateTime   : Thu Dec  3 11:29:14 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 233 expanded)
%              Number of clauses        :   21 (  23 expanded)
%              Number of leaves         :   16 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  213 ( 663 expanded)
%              Number of equality atoms :  173 ( 553 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f58,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f59,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f43,f53,f50,f59])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( sK1 != sK2
    & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f51,plain,(
    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f51,f53,f59,f59,f59])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f70,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f71,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f70])).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f76,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f36,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f74,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f67])).

fof(f75,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f74])).

fof(f52,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_991,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_650,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_1,c_15])).

cnf(c_17562,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_991,c_650])).

cnf(c_10,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_447,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20475,plain,
    ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17562,c_447])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_469,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
    | sK2 = X0
    | sK2 = X1
    | sK2 = X2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_470,plain,
    ( sK2 = X0
    | sK2 = X1
    | sK2 = X2
    | r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_472,plain,
    ( sK2 = sK1
    | r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_319,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_467,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_468,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_12,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_20,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_17,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20475,c_472,c_468,c_20,c_17,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:55:12 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 6.95/1.43  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/1.43  
% 6.95/1.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.95/1.43  
% 6.95/1.43  ------  iProver source info
% 6.95/1.43  
% 6.95/1.43  git: date: 2020-06-30 10:37:57 +0100
% 6.95/1.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.95/1.43  git: non_committed_changes: false
% 6.95/1.43  git: last_make_outside_of_git: false
% 6.95/1.43  
% 6.95/1.43  ------ 
% 6.95/1.43  
% 6.95/1.43  ------ Input Options
% 6.95/1.43  
% 6.95/1.43  --out_options                           all
% 6.95/1.43  --tptp_safe_out                         true
% 6.95/1.43  --problem_path                          ""
% 6.95/1.43  --include_path                          ""
% 6.95/1.43  --clausifier                            res/vclausify_rel
% 6.95/1.43  --clausifier_options                    ""
% 6.95/1.43  --stdin                                 false
% 6.95/1.43  --stats_out                             all
% 6.95/1.43  
% 6.95/1.43  ------ General Options
% 6.95/1.43  
% 6.95/1.43  --fof                                   false
% 6.95/1.43  --time_out_real                         305.
% 6.95/1.43  --time_out_virtual                      -1.
% 6.95/1.43  --symbol_type_check                     false
% 6.95/1.43  --clausify_out                          false
% 6.95/1.43  --sig_cnt_out                           false
% 6.95/1.43  --trig_cnt_out                          false
% 6.95/1.43  --trig_cnt_out_tolerance                1.
% 6.95/1.43  --trig_cnt_out_sk_spl                   false
% 6.95/1.43  --abstr_cl_out                          false
% 6.95/1.43  
% 6.95/1.43  ------ Global Options
% 6.95/1.43  
% 6.95/1.43  --schedule                              default
% 6.95/1.43  --add_important_lit                     false
% 6.95/1.43  --prop_solver_per_cl                    1000
% 6.95/1.43  --min_unsat_core                        false
% 6.95/1.43  --soft_assumptions                      false
% 6.95/1.43  --soft_lemma_size                       3
% 6.95/1.43  --prop_impl_unit_size                   0
% 6.95/1.43  --prop_impl_unit                        []
% 6.95/1.43  --share_sel_clauses                     true
% 6.95/1.43  --reset_solvers                         false
% 6.95/1.43  --bc_imp_inh                            [conj_cone]
% 6.95/1.43  --conj_cone_tolerance                   3.
% 6.95/1.43  --extra_neg_conj                        none
% 6.95/1.43  --large_theory_mode                     true
% 6.95/1.43  --prolific_symb_bound                   200
% 6.95/1.43  --lt_threshold                          2000
% 6.95/1.43  --clause_weak_htbl                      true
% 6.95/1.43  --gc_record_bc_elim                     false
% 6.95/1.43  
% 6.95/1.43  ------ Preprocessing Options
% 6.95/1.43  
% 6.95/1.43  --preprocessing_flag                    true
% 6.95/1.43  --time_out_prep_mult                    0.1
% 6.95/1.43  --splitting_mode                        input
% 6.95/1.43  --splitting_grd                         true
% 6.95/1.43  --splitting_cvd                         false
% 6.95/1.43  --splitting_cvd_svl                     false
% 6.95/1.43  --splitting_nvd                         32
% 6.95/1.43  --sub_typing                            true
% 6.95/1.43  --prep_gs_sim                           true
% 6.95/1.43  --prep_unflatten                        true
% 6.95/1.43  --prep_res_sim                          true
% 6.95/1.43  --prep_upred                            true
% 6.95/1.43  --prep_sem_filter                       exhaustive
% 6.95/1.43  --prep_sem_filter_out                   false
% 6.95/1.43  --pred_elim                             true
% 6.95/1.43  --res_sim_input                         true
% 6.95/1.43  --eq_ax_congr_red                       true
% 6.95/1.43  --pure_diseq_elim                       true
% 6.95/1.43  --brand_transform                       false
% 6.95/1.43  --non_eq_to_eq                          false
% 6.95/1.43  --prep_def_merge                        true
% 6.95/1.43  --prep_def_merge_prop_impl              false
% 6.95/1.43  --prep_def_merge_mbd                    true
% 6.95/1.43  --prep_def_merge_tr_red                 false
% 6.95/1.43  --prep_def_merge_tr_cl                  false
% 6.95/1.43  --smt_preprocessing                     true
% 6.95/1.43  --smt_ac_axioms                         fast
% 6.95/1.43  --preprocessed_out                      false
% 6.95/1.43  --preprocessed_stats                    false
% 6.95/1.43  
% 6.95/1.43  ------ Abstraction refinement Options
% 6.95/1.43  
% 6.95/1.43  --abstr_ref                             []
% 6.95/1.43  --abstr_ref_prep                        false
% 6.95/1.43  --abstr_ref_until_sat                   false
% 6.95/1.43  --abstr_ref_sig_restrict                funpre
% 6.95/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 6.95/1.43  --abstr_ref_under                       []
% 6.95/1.43  
% 6.95/1.43  ------ SAT Options
% 6.95/1.43  
% 6.95/1.43  --sat_mode                              false
% 6.95/1.43  --sat_fm_restart_options                ""
% 6.95/1.43  --sat_gr_def                            false
% 6.95/1.43  --sat_epr_types                         true
% 6.95/1.43  --sat_non_cyclic_types                  false
% 6.95/1.43  --sat_finite_models                     false
% 6.95/1.43  --sat_fm_lemmas                         false
% 6.95/1.43  --sat_fm_prep                           false
% 6.95/1.43  --sat_fm_uc_incr                        true
% 6.95/1.43  --sat_out_model                         small
% 6.95/1.43  --sat_out_clauses                       false
% 6.95/1.43  
% 6.95/1.43  ------ QBF Options
% 6.95/1.43  
% 6.95/1.43  --qbf_mode                              false
% 6.95/1.43  --qbf_elim_univ                         false
% 6.95/1.43  --qbf_dom_inst                          none
% 6.95/1.43  --qbf_dom_pre_inst                      false
% 6.95/1.43  --qbf_sk_in                             false
% 6.95/1.43  --qbf_pred_elim                         true
% 6.95/1.43  --qbf_split                             512
% 6.95/1.43  
% 6.95/1.43  ------ BMC1 Options
% 6.95/1.43  
% 6.95/1.43  --bmc1_incremental                      false
% 6.95/1.43  --bmc1_axioms                           reachable_all
% 6.95/1.43  --bmc1_min_bound                        0
% 6.95/1.43  --bmc1_max_bound                        -1
% 6.95/1.43  --bmc1_max_bound_default                -1
% 6.95/1.43  --bmc1_symbol_reachability              true
% 6.95/1.43  --bmc1_property_lemmas                  false
% 6.95/1.43  --bmc1_k_induction                      false
% 6.95/1.43  --bmc1_non_equiv_states                 false
% 6.95/1.43  --bmc1_deadlock                         false
% 6.95/1.43  --bmc1_ucm                              false
% 6.95/1.43  --bmc1_add_unsat_core                   none
% 6.95/1.43  --bmc1_unsat_core_children              false
% 6.95/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 6.95/1.43  --bmc1_out_stat                         full
% 6.95/1.43  --bmc1_ground_init                      false
% 6.95/1.43  --bmc1_pre_inst_next_state              false
% 6.95/1.43  --bmc1_pre_inst_state                   false
% 6.95/1.43  --bmc1_pre_inst_reach_state             false
% 6.95/1.43  --bmc1_out_unsat_core                   false
% 6.95/1.43  --bmc1_aig_witness_out                  false
% 6.95/1.43  --bmc1_verbose                          false
% 6.95/1.43  --bmc1_dump_clauses_tptp                false
% 6.95/1.43  --bmc1_dump_unsat_core_tptp             false
% 6.95/1.43  --bmc1_dump_file                        -
% 6.95/1.43  --bmc1_ucm_expand_uc_limit              128
% 6.95/1.43  --bmc1_ucm_n_expand_iterations          6
% 6.95/1.43  --bmc1_ucm_extend_mode                  1
% 6.95/1.43  --bmc1_ucm_init_mode                    2
% 6.95/1.43  --bmc1_ucm_cone_mode                    none
% 6.95/1.43  --bmc1_ucm_reduced_relation_type        0
% 6.95/1.43  --bmc1_ucm_relax_model                  4
% 6.95/1.43  --bmc1_ucm_full_tr_after_sat            true
% 6.95/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 6.95/1.43  --bmc1_ucm_layered_model                none
% 6.95/1.43  --bmc1_ucm_max_lemma_size               10
% 6.95/1.43  
% 6.95/1.43  ------ AIG Options
% 6.95/1.43  
% 6.95/1.43  --aig_mode                              false
% 6.95/1.43  
% 6.95/1.43  ------ Instantiation Options
% 6.95/1.43  
% 6.95/1.43  --instantiation_flag                    true
% 6.95/1.43  --inst_sos_flag                         true
% 6.95/1.43  --inst_sos_phase                        true
% 6.95/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.95/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.95/1.43  --inst_lit_sel_side                     num_symb
% 6.95/1.43  --inst_solver_per_active                1400
% 6.95/1.43  --inst_solver_calls_frac                1.
% 6.95/1.43  --inst_passive_queue_type               priority_queues
% 6.95/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.95/1.43  --inst_passive_queues_freq              [25;2]
% 6.95/1.43  --inst_dismatching                      true
% 6.95/1.43  --inst_eager_unprocessed_to_passive     true
% 6.95/1.43  --inst_prop_sim_given                   true
% 6.95/1.43  --inst_prop_sim_new                     false
% 6.95/1.43  --inst_subs_new                         false
% 6.95/1.43  --inst_eq_res_simp                      false
% 6.95/1.43  --inst_subs_given                       false
% 6.95/1.43  --inst_orphan_elimination               true
% 6.95/1.43  --inst_learning_loop_flag               true
% 6.95/1.43  --inst_learning_start                   3000
% 6.95/1.43  --inst_learning_factor                  2
% 6.95/1.43  --inst_start_prop_sim_after_learn       3
% 6.95/1.43  --inst_sel_renew                        solver
% 6.95/1.43  --inst_lit_activity_flag                true
% 6.95/1.43  --inst_restr_to_given                   false
% 6.95/1.43  --inst_activity_threshold               500
% 6.95/1.43  --inst_out_proof                        true
% 6.95/1.43  
% 6.95/1.43  ------ Resolution Options
% 6.95/1.43  
% 6.95/1.43  --resolution_flag                       true
% 6.95/1.43  --res_lit_sel                           adaptive
% 6.95/1.43  --res_lit_sel_side                      none
% 6.95/1.43  --res_ordering                          kbo
% 6.95/1.43  --res_to_prop_solver                    active
% 6.95/1.43  --res_prop_simpl_new                    false
% 6.95/1.43  --res_prop_simpl_given                  true
% 6.95/1.43  --res_passive_queue_type                priority_queues
% 6.95/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.95/1.43  --res_passive_queues_freq               [15;5]
% 6.95/1.43  --res_forward_subs                      full
% 6.95/1.43  --res_backward_subs                     full
% 6.95/1.43  --res_forward_subs_resolution           true
% 6.95/1.43  --res_backward_subs_resolution          true
% 6.95/1.43  --res_orphan_elimination                true
% 6.95/1.43  --res_time_limit                        2.
% 6.95/1.43  --res_out_proof                         true
% 6.95/1.43  
% 6.95/1.43  ------ Superposition Options
% 6.95/1.43  
% 6.95/1.43  --superposition_flag                    true
% 6.95/1.43  --sup_passive_queue_type                priority_queues
% 6.95/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.95/1.43  --sup_passive_queues_freq               [8;1;4]
% 6.95/1.43  --demod_completeness_check              fast
% 6.95/1.43  --demod_use_ground                      true
% 6.95/1.43  --sup_to_prop_solver                    passive
% 6.95/1.43  --sup_prop_simpl_new                    true
% 6.95/1.43  --sup_prop_simpl_given                  true
% 6.95/1.43  --sup_fun_splitting                     true
% 6.95/1.43  --sup_smt_interval                      50000
% 6.95/1.43  
% 6.95/1.43  ------ Superposition Simplification Setup
% 6.95/1.43  
% 6.95/1.43  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.95/1.43  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.95/1.43  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.95/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.95/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 6.95/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.95/1.43  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.95/1.43  --sup_immed_triv                        [TrivRules]
% 6.95/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.95/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.95/1.43  --sup_immed_bw_main                     []
% 6.95/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.95/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 6.95/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.95/1.43  --sup_input_bw                          []
% 6.95/1.43  
% 6.95/1.43  ------ Combination Options
% 6.95/1.43  
% 6.95/1.43  --comb_res_mult                         3
% 6.95/1.43  --comb_sup_mult                         2
% 6.95/1.43  --comb_inst_mult                        10
% 6.95/1.43  
% 6.95/1.43  ------ Debug Options
% 6.95/1.43  
% 6.95/1.43  --dbg_backtrace                         false
% 6.95/1.43  --dbg_dump_prop_clauses                 false
% 6.95/1.43  --dbg_dump_prop_clauses_file            -
% 6.95/1.43  --dbg_out_stat                          false
% 6.95/1.43  ------ Parsing...
% 6.95/1.43  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.95/1.43  
% 6.95/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.95/1.43  
% 6.95/1.43  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.95/1.43  
% 6.95/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.95/1.43  ------ Proving...
% 6.95/1.43  ------ Problem Properties 
% 6.95/1.43  
% 6.95/1.43  
% 6.95/1.43  clauses                                 16
% 6.95/1.43  conjectures                             2
% 6.95/1.43  EPR                                     1
% 6.95/1.43  Horn                                    14
% 6.95/1.43  unary                                   11
% 6.95/1.43  binary                                  0
% 6.95/1.43  lits                                    29
% 6.95/1.43  lits eq                                 21
% 6.95/1.43  fd_pure                                 0
% 6.95/1.43  fd_pseudo                               0
% 6.95/1.43  fd_cond                                 0
% 6.95/1.43  fd_pseudo_cond                          4
% 6.95/1.43  AC symbols                              1
% 6.95/1.43  
% 6.95/1.43  ------ Schedule dynamic 5 is on 
% 6.95/1.43  
% 6.95/1.43  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.95/1.43  
% 6.95/1.43  
% 6.95/1.43  ------ 
% 6.95/1.43  Current options:
% 6.95/1.43  ------ 
% 6.95/1.43  
% 6.95/1.43  ------ Input Options
% 6.95/1.43  
% 6.95/1.43  --out_options                           all
% 6.95/1.43  --tptp_safe_out                         true
% 6.95/1.43  --problem_path                          ""
% 6.95/1.43  --include_path                          ""
% 6.95/1.43  --clausifier                            res/vclausify_rel
% 6.95/1.43  --clausifier_options                    ""
% 6.95/1.43  --stdin                                 false
% 6.95/1.43  --stats_out                             all
% 6.95/1.43  
% 6.95/1.43  ------ General Options
% 6.95/1.43  
% 6.95/1.43  --fof                                   false
% 6.95/1.43  --time_out_real                         305.
% 6.95/1.43  --time_out_virtual                      -1.
% 6.95/1.43  --symbol_type_check                     false
% 6.95/1.43  --clausify_out                          false
% 6.95/1.43  --sig_cnt_out                           false
% 6.95/1.43  --trig_cnt_out                          false
% 6.95/1.43  --trig_cnt_out_tolerance                1.
% 6.95/1.43  --trig_cnt_out_sk_spl                   false
% 6.95/1.43  --abstr_cl_out                          false
% 6.95/1.43  
% 6.95/1.43  ------ Global Options
% 6.95/1.43  
% 6.95/1.43  --schedule                              default
% 6.95/1.43  --add_important_lit                     false
% 6.95/1.43  --prop_solver_per_cl                    1000
% 6.95/1.43  --min_unsat_core                        false
% 6.95/1.43  --soft_assumptions                      false
% 6.95/1.43  --soft_lemma_size                       3
% 6.95/1.43  --prop_impl_unit_size                   0
% 6.95/1.43  --prop_impl_unit                        []
% 6.95/1.43  --share_sel_clauses                     true
% 6.95/1.43  --reset_solvers                         false
% 6.95/1.43  --bc_imp_inh                            [conj_cone]
% 6.95/1.43  --conj_cone_tolerance                   3.
% 6.95/1.43  --extra_neg_conj                        none
% 6.95/1.43  --large_theory_mode                     true
% 6.95/1.43  --prolific_symb_bound                   200
% 6.95/1.43  --lt_threshold                          2000
% 6.95/1.43  --clause_weak_htbl                      true
% 6.95/1.43  --gc_record_bc_elim                     false
% 6.95/1.43  
% 6.95/1.43  ------ Preprocessing Options
% 6.95/1.43  
% 6.95/1.43  --preprocessing_flag                    true
% 6.95/1.43  --time_out_prep_mult                    0.1
% 6.95/1.43  --splitting_mode                        input
% 6.95/1.43  --splitting_grd                         true
% 6.95/1.43  --splitting_cvd                         false
% 6.95/1.43  --splitting_cvd_svl                     false
% 6.95/1.43  --splitting_nvd                         32
% 6.95/1.43  --sub_typing                            true
% 6.95/1.43  --prep_gs_sim                           true
% 6.95/1.43  --prep_unflatten                        true
% 6.95/1.43  --prep_res_sim                          true
% 6.95/1.43  --prep_upred                            true
% 6.95/1.43  --prep_sem_filter                       exhaustive
% 6.95/1.43  --prep_sem_filter_out                   false
% 6.95/1.43  --pred_elim                             true
% 6.95/1.43  --res_sim_input                         true
% 6.95/1.43  --eq_ax_congr_red                       true
% 6.95/1.43  --pure_diseq_elim                       true
% 6.95/1.43  --brand_transform                       false
% 6.95/1.43  --non_eq_to_eq                          false
% 6.95/1.43  --prep_def_merge                        true
% 6.95/1.43  --prep_def_merge_prop_impl              false
% 6.95/1.43  --prep_def_merge_mbd                    true
% 6.95/1.43  --prep_def_merge_tr_red                 false
% 6.95/1.43  --prep_def_merge_tr_cl                  false
% 6.95/1.43  --smt_preprocessing                     true
% 6.95/1.43  --smt_ac_axioms                         fast
% 6.95/1.43  --preprocessed_out                      false
% 6.95/1.43  --preprocessed_stats                    false
% 6.95/1.43  
% 6.95/1.43  ------ Abstraction refinement Options
% 6.95/1.43  
% 6.95/1.43  --abstr_ref                             []
% 6.95/1.43  --abstr_ref_prep                        false
% 6.95/1.43  --abstr_ref_until_sat                   false
% 6.95/1.43  --abstr_ref_sig_restrict                funpre
% 6.95/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 6.95/1.43  --abstr_ref_under                       []
% 6.95/1.43  
% 6.95/1.43  ------ SAT Options
% 6.95/1.43  
% 6.95/1.43  --sat_mode                              false
% 6.95/1.43  --sat_fm_restart_options                ""
% 6.95/1.43  --sat_gr_def                            false
% 6.95/1.43  --sat_epr_types                         true
% 6.95/1.43  --sat_non_cyclic_types                  false
% 6.95/1.43  --sat_finite_models                     false
% 6.95/1.43  --sat_fm_lemmas                         false
% 6.95/1.43  --sat_fm_prep                           false
% 6.95/1.43  --sat_fm_uc_incr                        true
% 6.95/1.43  --sat_out_model                         small
% 6.95/1.43  --sat_out_clauses                       false
% 6.95/1.43  
% 6.95/1.43  ------ QBF Options
% 6.95/1.43  
% 6.95/1.43  --qbf_mode                              false
% 6.95/1.43  --qbf_elim_univ                         false
% 6.95/1.43  --qbf_dom_inst                          none
% 6.95/1.43  --qbf_dom_pre_inst                      false
% 6.95/1.43  --qbf_sk_in                             false
% 6.95/1.43  --qbf_pred_elim                         true
% 6.95/1.43  --qbf_split                             512
% 6.95/1.43  
% 6.95/1.43  ------ BMC1 Options
% 6.95/1.43  
% 6.95/1.43  --bmc1_incremental                      false
% 6.95/1.43  --bmc1_axioms                           reachable_all
% 6.95/1.43  --bmc1_min_bound                        0
% 6.95/1.43  --bmc1_max_bound                        -1
% 6.95/1.43  --bmc1_max_bound_default                -1
% 6.95/1.43  --bmc1_symbol_reachability              true
% 6.95/1.43  --bmc1_property_lemmas                  false
% 6.95/1.43  --bmc1_k_induction                      false
% 6.95/1.43  --bmc1_non_equiv_states                 false
% 6.95/1.43  --bmc1_deadlock                         false
% 6.95/1.43  --bmc1_ucm                              false
% 6.95/1.43  --bmc1_add_unsat_core                   none
% 6.95/1.43  --bmc1_unsat_core_children              false
% 6.95/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 6.95/1.43  --bmc1_out_stat                         full
% 6.95/1.43  --bmc1_ground_init                      false
% 6.95/1.43  --bmc1_pre_inst_next_state              false
% 6.95/1.43  --bmc1_pre_inst_state                   false
% 6.95/1.43  --bmc1_pre_inst_reach_state             false
% 6.95/1.43  --bmc1_out_unsat_core                   false
% 6.95/1.43  --bmc1_aig_witness_out                  false
% 6.95/1.43  --bmc1_verbose                          false
% 6.95/1.43  --bmc1_dump_clauses_tptp                false
% 6.95/1.43  --bmc1_dump_unsat_core_tptp             false
% 6.95/1.43  --bmc1_dump_file                        -
% 6.95/1.43  --bmc1_ucm_expand_uc_limit              128
% 6.95/1.43  --bmc1_ucm_n_expand_iterations          6
% 6.95/1.43  --bmc1_ucm_extend_mode                  1
% 6.95/1.43  --bmc1_ucm_init_mode                    2
% 6.95/1.43  --bmc1_ucm_cone_mode                    none
% 6.95/1.43  --bmc1_ucm_reduced_relation_type        0
% 6.95/1.43  --bmc1_ucm_relax_model                  4
% 6.95/1.43  --bmc1_ucm_full_tr_after_sat            true
% 6.95/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 6.95/1.43  --bmc1_ucm_layered_model                none
% 6.95/1.43  --bmc1_ucm_max_lemma_size               10
% 6.95/1.43  
% 6.95/1.43  ------ AIG Options
% 6.95/1.43  
% 6.95/1.43  --aig_mode                              false
% 6.95/1.43  
% 6.95/1.43  ------ Instantiation Options
% 6.95/1.43  
% 6.95/1.43  --instantiation_flag                    true
% 6.95/1.43  --inst_sos_flag                         true
% 6.95/1.43  --inst_sos_phase                        true
% 6.95/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.95/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.95/1.43  --inst_lit_sel_side                     none
% 6.95/1.43  --inst_solver_per_active                1400
% 6.95/1.43  --inst_solver_calls_frac                1.
% 6.95/1.43  --inst_passive_queue_type               priority_queues
% 6.95/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.95/1.43  --inst_passive_queues_freq              [25;2]
% 6.95/1.43  --inst_dismatching                      true
% 6.95/1.43  --inst_eager_unprocessed_to_passive     true
% 6.95/1.43  --inst_prop_sim_given                   true
% 6.95/1.43  --inst_prop_sim_new                     false
% 6.95/1.43  --inst_subs_new                         false
% 6.95/1.43  --inst_eq_res_simp                      false
% 6.95/1.43  --inst_subs_given                       false
% 6.95/1.43  --inst_orphan_elimination               true
% 6.95/1.43  --inst_learning_loop_flag               true
% 6.95/1.43  --inst_learning_start                   3000
% 6.95/1.43  --inst_learning_factor                  2
% 6.95/1.43  --inst_start_prop_sim_after_learn       3
% 6.95/1.43  --inst_sel_renew                        solver
% 6.95/1.43  --inst_lit_activity_flag                true
% 6.95/1.43  --inst_restr_to_given                   false
% 6.95/1.43  --inst_activity_threshold               500
% 6.95/1.43  --inst_out_proof                        true
% 6.95/1.43  
% 6.95/1.43  ------ Resolution Options
% 6.95/1.43  
% 6.95/1.43  --resolution_flag                       false
% 6.95/1.43  --res_lit_sel                           adaptive
% 6.95/1.43  --res_lit_sel_side                      none
% 6.95/1.43  --res_ordering                          kbo
% 6.95/1.43  --res_to_prop_solver                    active
% 6.95/1.43  --res_prop_simpl_new                    false
% 6.95/1.43  --res_prop_simpl_given                  true
% 6.95/1.43  --res_passive_queue_type                priority_queues
% 6.95/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.95/1.43  --res_passive_queues_freq               [15;5]
% 6.95/1.43  --res_forward_subs                      full
% 6.95/1.43  --res_backward_subs                     full
% 6.95/1.43  --res_forward_subs_resolution           true
% 6.95/1.43  --res_backward_subs_resolution          true
% 6.95/1.43  --res_orphan_elimination                true
% 6.95/1.43  --res_time_limit                        2.
% 6.95/1.43  --res_out_proof                         true
% 6.95/1.43  
% 6.95/1.43  ------ Superposition Options
% 6.95/1.43  
% 6.95/1.43  --superposition_flag                    true
% 6.95/1.43  --sup_passive_queue_type                priority_queues
% 6.95/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.95/1.43  --sup_passive_queues_freq               [8;1;4]
% 6.95/1.43  --demod_completeness_check              fast
% 6.95/1.43  --demod_use_ground                      true
% 6.95/1.43  --sup_to_prop_solver                    passive
% 6.95/1.43  --sup_prop_simpl_new                    true
% 6.95/1.43  --sup_prop_simpl_given                  true
% 6.95/1.43  --sup_fun_splitting                     true
% 6.95/1.43  --sup_smt_interval                      50000
% 6.95/1.43  
% 6.95/1.43  ------ Superposition Simplification Setup
% 6.95/1.43  
% 6.95/1.43  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.95/1.43  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.95/1.43  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.95/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.95/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 6.95/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.95/1.43  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.95/1.43  --sup_immed_triv                        [TrivRules]
% 6.95/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.95/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.95/1.43  --sup_immed_bw_main                     []
% 6.95/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.95/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 6.95/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.95/1.43  --sup_input_bw                          []
% 6.95/1.43  
% 6.95/1.43  ------ Combination Options
% 6.95/1.43  
% 6.95/1.43  --comb_res_mult                         3
% 6.95/1.43  --comb_sup_mult                         2
% 6.95/1.43  --comb_inst_mult                        10
% 6.95/1.43  
% 6.95/1.43  ------ Debug Options
% 6.95/1.43  
% 6.95/1.43  --dbg_backtrace                         false
% 6.95/1.43  --dbg_dump_prop_clauses                 false
% 6.95/1.43  --dbg_dump_prop_clauses_file            -
% 6.95/1.43  --dbg_out_stat                          false
% 6.95/1.43  
% 6.95/1.43  
% 6.95/1.43  
% 6.95/1.43  
% 6.95/1.43  ------ Proving...
% 6.95/1.43  
% 6.95/1.43  
% 6.95/1.43  % SZS status Theorem for theBenchmark.p
% 6.95/1.43  
% 6.95/1.43  % SZS output start CNFRefutation for theBenchmark.p
% 6.95/1.43  
% 6.95/1.43  fof(f1,axiom,(
% 6.95/1.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f28,plain,(
% 6.95/1.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f1])).
% 6.95/1.43  
% 6.95/1.43  fof(f9,axiom,(
% 6.95/1.43    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f43,plain,(
% 6.95/1.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f9])).
% 6.95/1.43  
% 6.95/1.43  fof(f7,axiom,(
% 6.95/1.43    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f34,plain,(
% 6.95/1.43    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f7])).
% 6.95/1.43  
% 6.95/1.43  fof(f3,axiom,(
% 6.95/1.43    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f30,plain,(
% 6.95/1.43    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f3])).
% 6.95/1.43  
% 6.95/1.43  fof(f53,plain,(
% 6.95/1.43    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 6.95/1.43    inference(definition_unfolding,[],[f34,f30])).
% 6.95/1.43  
% 6.95/1.43  fof(f10,axiom,(
% 6.95/1.43    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f44,plain,(
% 6.95/1.43    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f10])).
% 6.95/1.43  
% 6.95/1.43  fof(f11,axiom,(
% 6.95/1.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f45,plain,(
% 6.95/1.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f11])).
% 6.95/1.43  
% 6.95/1.43  fof(f12,axiom,(
% 6.95/1.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f46,plain,(
% 6.95/1.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f12])).
% 6.95/1.43  
% 6.95/1.43  fof(f13,axiom,(
% 6.95/1.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f47,plain,(
% 6.95/1.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f13])).
% 6.95/1.43  
% 6.95/1.43  fof(f14,axiom,(
% 6.95/1.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f48,plain,(
% 6.95/1.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f14])).
% 6.95/1.43  
% 6.95/1.43  fof(f15,axiom,(
% 6.95/1.43    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f49,plain,(
% 6.95/1.43    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f15])).
% 6.95/1.43  
% 6.95/1.43  fof(f16,axiom,(
% 6.95/1.43    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f50,plain,(
% 6.95/1.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 6.95/1.43    inference(cnf_transformation,[],[f16])).
% 6.95/1.43  
% 6.95/1.43  fof(f54,plain,(
% 6.95/1.43    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 6.95/1.43    inference(definition_unfolding,[],[f49,f50])).
% 6.95/1.43  
% 6.95/1.43  fof(f55,plain,(
% 6.95/1.43    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 6.95/1.43    inference(definition_unfolding,[],[f48,f54])).
% 6.95/1.43  
% 6.95/1.43  fof(f56,plain,(
% 6.95/1.43    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.95/1.43    inference(definition_unfolding,[],[f47,f55])).
% 6.95/1.43  
% 6.95/1.43  fof(f57,plain,(
% 6.95/1.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.95/1.43    inference(definition_unfolding,[],[f46,f56])).
% 6.95/1.43  
% 6.95/1.43  fof(f58,plain,(
% 6.95/1.43    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.95/1.43    inference(definition_unfolding,[],[f45,f57])).
% 6.95/1.43  
% 6.95/1.43  fof(f59,plain,(
% 6.95/1.43    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 6.95/1.43    inference(definition_unfolding,[],[f44,f58])).
% 6.95/1.43  
% 6.95/1.43  fof(f60,plain,(
% 6.95/1.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 6.95/1.43    inference(definition_unfolding,[],[f43,f53,f50,f59])).
% 6.95/1.43  
% 6.95/1.43  fof(f17,conjecture,(
% 6.95/1.43    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f18,negated_conjecture,(
% 6.95/1.43    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 6.95/1.43    inference(negated_conjecture,[],[f17])).
% 6.95/1.43  
% 6.95/1.43  fof(f20,plain,(
% 6.95/1.43    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 6.95/1.43    inference(ennf_transformation,[],[f18])).
% 6.95/1.43  
% 6.95/1.43  fof(f26,plain,(
% 6.95/1.43    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 6.95/1.43    introduced(choice_axiom,[])).
% 6.95/1.43  
% 6.95/1.43  fof(f27,plain,(
% 6.95/1.43    sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 6.95/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 6.95/1.43  
% 6.95/1.43  fof(f51,plain,(
% 6.95/1.43    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 6.95/1.43    inference(cnf_transformation,[],[f27])).
% 6.95/1.43  
% 6.95/1.43  fof(f69,plain,(
% 6.95/1.43    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 6.95/1.43    inference(definition_unfolding,[],[f51,f53,f59,f59,f59])).
% 6.95/1.43  
% 6.95/1.43  fof(f8,axiom,(
% 6.95/1.43    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 6.95/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.43  
% 6.95/1.43  fof(f19,plain,(
% 6.95/1.43    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 6.95/1.43    inference(ennf_transformation,[],[f8])).
% 6.95/1.43  
% 6.95/1.43  fof(f21,plain,(
% 6.95/1.43    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 6.95/1.43    inference(nnf_transformation,[],[f19])).
% 6.95/1.43  
% 6.95/1.43  fof(f22,plain,(
% 6.95/1.43    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 6.95/1.43    inference(flattening,[],[f21])).
% 6.95/1.43  
% 6.95/1.43  fof(f23,plain,(
% 6.95/1.43    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 6.95/1.43    inference(rectify,[],[f22])).
% 6.95/1.43  
% 6.95/1.43  fof(f24,plain,(
% 6.95/1.43    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 6.95/1.43    introduced(choice_axiom,[])).
% 6.95/1.43  
% 6.95/1.43  fof(f25,plain,(
% 6.95/1.43    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 6.95/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 6.95/1.43  
% 6.95/1.43  fof(f38,plain,(
% 6.95/1.43    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 6.95/1.43    inference(cnf_transformation,[],[f25])).
% 6.95/1.43  
% 6.95/1.43  fof(f65,plain,(
% 6.95/1.43    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 6.95/1.43    inference(definition_unfolding,[],[f38,f57])).
% 6.95/1.43  
% 6.95/1.43  fof(f70,plain,(
% 6.95/1.43    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 6.95/1.43    inference(equality_resolution,[],[f65])).
% 6.95/1.43  
% 6.95/1.43  fof(f71,plain,(
% 6.95/1.43    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 6.95/1.43    inference(equality_resolution,[],[f70])).
% 6.95/1.43  
% 6.95/1.43  fof(f35,plain,(
% 6.95/1.43    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 6.95/1.43    inference(cnf_transformation,[],[f25])).
% 6.95/1.43  
% 6.95/1.43  fof(f68,plain,(
% 6.95/1.43    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 6.95/1.43    inference(definition_unfolding,[],[f35,f57])).
% 6.95/1.43  
% 6.95/1.43  fof(f76,plain,(
% 6.95/1.43    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 6.95/1.43    inference(equality_resolution,[],[f68])).
% 6.95/1.43  
% 6.95/1.43  fof(f36,plain,(
% 6.95/1.43    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 6.95/1.43    inference(cnf_transformation,[],[f25])).
% 6.95/1.43  
% 6.95/1.43  fof(f67,plain,(
% 6.95/1.43    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 6.95/1.43    inference(definition_unfolding,[],[f36,f57])).
% 6.95/1.43  
% 6.95/1.43  fof(f74,plain,(
% 6.95/1.43    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 6.95/1.43    inference(equality_resolution,[],[f67])).
% 6.95/1.43  
% 6.95/1.43  fof(f75,plain,(
% 6.95/1.43    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 6.95/1.43    inference(equality_resolution,[],[f74])).
% 6.95/1.43  
% 6.95/1.43  fof(f52,plain,(
% 6.95/1.43    sK1 != sK2),
% 6.95/1.43    inference(cnf_transformation,[],[f27])).
% 6.95/1.43  
% 6.95/1.43  cnf(c_1,plain,
% 6.95/1.43      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 6.95/1.43      inference(cnf_transformation,[],[f28]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_0,plain,
% 6.95/1.43      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 6.95/1.43      inference(cnf_transformation,[],[f60]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_991,plain,
% 6.95/1.43      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 6.95/1.43      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_15,negated_conjecture,
% 6.95/1.43      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 6.95/1.43      inference(cnf_transformation,[],[f69]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_650,plain,
% 6.95/1.43      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 6.95/1.43      inference(demodulation,[status(thm)],[c_1,c_15]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_17562,plain,
% 6.95/1.43      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 6.95/1.43      inference(superposition,[status(thm)],[c_991,c_650]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_10,plain,
% 6.95/1.43      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 6.95/1.43      inference(cnf_transformation,[],[f71]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_447,plain,
% 6.95/1.43      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 6.95/1.43      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_20475,plain,
% 6.95/1.43      ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 6.95/1.43      inference(superposition,[status(thm)],[c_17562,c_447]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_13,plain,
% 6.95/1.43      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 6.95/1.43      | X0 = X1
% 6.95/1.43      | X0 = X2
% 6.95/1.43      | X0 = X3 ),
% 6.95/1.43      inference(cnf_transformation,[],[f76]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_469,plain,
% 6.95/1.43      ( ~ r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
% 6.95/1.43      | sK2 = X0
% 6.95/1.43      | sK2 = X1
% 6.95/1.43      | sK2 = X2 ),
% 6.95/1.43      inference(instantiation,[status(thm)],[c_13]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_470,plain,
% 6.95/1.43      ( sK2 = X0
% 6.95/1.43      | sK2 = X1
% 6.95/1.43      | sK2 = X2
% 6.95/1.43      | r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
% 6.95/1.43      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_472,plain,
% 6.95/1.43      ( sK2 = sK1
% 6.95/1.43      | r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 6.95/1.43      inference(instantiation,[status(thm)],[c_470]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_319,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_467,plain,
% 6.95/1.43      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 6.95/1.43      inference(instantiation,[status(thm)],[c_319]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_468,plain,
% 6.95/1.43      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 6.95/1.43      inference(instantiation,[status(thm)],[c_467]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_12,plain,
% 6.95/1.43      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 6.95/1.43      inference(cnf_transformation,[],[f75]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_20,plain,
% 6.95/1.43      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 6.95/1.43      inference(instantiation,[status(thm)],[c_12]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_17,plain,
% 6.95/1.43      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 6.95/1.43      | sK1 = sK1 ),
% 6.95/1.43      inference(instantiation,[status(thm)],[c_13]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(c_14,negated_conjecture,
% 6.95/1.43      ( sK1 != sK2 ),
% 6.95/1.43      inference(cnf_transformation,[],[f52]) ).
% 6.95/1.43  
% 6.95/1.43  cnf(contradiction,plain,
% 6.95/1.43      ( $false ),
% 6.95/1.43      inference(minisat,
% 6.95/1.43                [status(thm)],
% 6.95/1.43                [c_20475,c_472,c_468,c_20,c_17,c_14]) ).
% 6.95/1.43  
% 6.95/1.43  
% 6.95/1.43  % SZS output end CNFRefutation for theBenchmark.p
% 6.95/1.43  
% 6.95/1.43  ------                               Statistics
% 6.95/1.43  
% 6.95/1.43  ------ General
% 6.95/1.43  
% 6.95/1.43  abstr_ref_over_cycles:                  0
% 6.95/1.43  abstr_ref_under_cycles:                 0
% 6.95/1.43  gc_basic_clause_elim:                   0
% 6.95/1.43  forced_gc_time:                         0
% 6.95/1.43  parsing_time:                           0.008
% 6.95/1.43  unif_index_cands_time:                  0.
% 6.95/1.43  unif_index_add_time:                    0.
% 6.95/1.43  orderings_time:                         0.
% 6.95/1.43  out_proof_time:                         0.009
% 6.95/1.43  total_time:                             0.964
% 6.95/1.43  num_of_symbols:                         39
% 6.95/1.43  num_of_terms:                           36053
% 6.95/1.43  
% 6.95/1.43  ------ Preprocessing
% 6.95/1.43  
% 6.95/1.43  num_of_splits:                          0
% 6.95/1.43  num_of_split_atoms:                     0
% 6.95/1.43  num_of_reused_defs:                     0
% 6.95/1.43  num_eq_ax_congr_red:                    8
% 6.95/1.43  num_of_sem_filtered_clauses:            1
% 6.95/1.43  num_of_subtypes:                        0
% 6.95/1.43  monotx_restored_types:                  0
% 6.95/1.43  sat_num_of_epr_types:                   0
% 6.95/1.43  sat_num_of_non_cyclic_types:            0
% 6.95/1.43  sat_guarded_non_collapsed_types:        0
% 6.95/1.43  num_pure_diseq_elim:                    0
% 6.95/1.43  simp_replaced_by:                       0
% 6.95/1.43  res_preprocessed:                       61
% 6.95/1.43  prep_upred:                             0
% 6.95/1.43  prep_unflattend:                        14
% 6.95/1.43  smt_new_axioms:                         0
% 6.95/1.43  pred_elim_cands:                        1
% 6.95/1.43  pred_elim:                              0
% 6.95/1.43  pred_elim_cl:                           0
% 6.95/1.43  pred_elim_cycles:                       1
% 6.95/1.43  merged_defs:                            0
% 6.95/1.43  merged_defs_ncl:                        0
% 6.95/1.43  bin_hyper_res:                          0
% 6.95/1.43  prep_cycles:                            3
% 6.95/1.43  pred_elim_time:                         0.002
% 6.95/1.43  splitting_time:                         0.
% 6.95/1.43  sem_filter_time:                        0.
% 6.95/1.43  monotx_time:                            0.
% 6.95/1.43  subtype_inf_time:                       0.
% 6.95/1.43  
% 6.95/1.43  ------ Problem properties
% 6.95/1.43  
% 6.95/1.43  clauses:                                16
% 6.95/1.43  conjectures:                            2
% 6.95/1.43  epr:                                    1
% 6.95/1.43  horn:                                   14
% 6.95/1.43  ground:                                 2
% 6.95/1.43  unary:                                  11
% 6.95/1.43  binary:                                 0
% 6.95/1.43  lits:                                   29
% 6.95/1.43  lits_eq:                                21
% 6.95/1.43  fd_pure:                                0
% 6.95/1.43  fd_pseudo:                              0
% 6.95/1.43  fd_cond:                                0
% 6.95/1.43  fd_pseudo_cond:                         4
% 6.95/1.43  ac_symbols:                             1
% 6.95/1.43  
% 6.95/1.43  ------ Propositional Solver
% 6.95/1.43  
% 6.95/1.43  prop_solver_calls:                      28
% 6.95/1.43  prop_fast_solver_calls:                 458
% 6.95/1.43  smt_solver_calls:                       0
% 6.95/1.43  smt_fast_solver_calls:                  0
% 6.95/1.43  prop_num_of_clauses:                    5075
% 6.95/1.43  prop_preprocess_simplified:             8204
% 6.95/1.43  prop_fo_subsumed:                       0
% 6.95/1.43  prop_solver_time:                       0.
% 6.95/1.43  smt_solver_time:                        0.
% 6.95/1.43  smt_fast_solver_time:                   0.
% 6.95/1.43  prop_fast_solver_time:                  0.
% 6.95/1.43  prop_unsat_core_time:                   0.
% 6.95/1.43  
% 6.95/1.43  ------ QBF
% 6.95/1.43  
% 6.95/1.43  qbf_q_res:                              0
% 6.95/1.43  qbf_num_tautologies:                    0
% 6.95/1.43  qbf_prep_cycles:                        0
% 6.95/1.43  
% 6.95/1.43  ------ BMC1
% 6.95/1.43  
% 6.95/1.43  bmc1_current_bound:                     -1
% 6.95/1.43  bmc1_last_solved_bound:                 -1
% 6.95/1.43  bmc1_unsat_core_size:                   -1
% 6.95/1.43  bmc1_unsat_core_parents_size:           -1
% 6.95/1.43  bmc1_merge_next_fun:                    0
% 6.95/1.43  bmc1_unsat_core_clauses_time:           0.
% 6.95/1.43  
% 6.95/1.43  ------ Instantiation
% 6.95/1.43  
% 6.95/1.43  inst_num_of_clauses:                    1172
% 6.95/1.43  inst_num_in_passive:                    260
% 6.95/1.43  inst_num_in_active:                     390
% 6.95/1.43  inst_num_in_unprocessed:                522
% 6.95/1.43  inst_num_of_loops:                      420
% 6.95/1.43  inst_num_of_learning_restarts:          0
% 6.95/1.43  inst_num_moves_active_passive:          26
% 6.95/1.43  inst_lit_activity:                      0
% 6.95/1.43  inst_lit_activity_moves:                0
% 6.95/1.43  inst_num_tautologies:                   0
% 6.95/1.43  inst_num_prop_implied:                  0
% 6.95/1.43  inst_num_existing_simplified:           0
% 6.95/1.43  inst_num_eq_res_simplified:             0
% 6.95/1.43  inst_num_child_elim:                    0
% 6.95/1.43  inst_num_of_dismatching_blockings:      939
% 6.95/1.43  inst_num_of_non_proper_insts:           1380
% 6.95/1.43  inst_num_of_duplicates:                 0
% 6.95/1.43  inst_inst_num_from_inst_to_res:         0
% 6.95/1.43  inst_dismatching_checking_time:         0.
% 6.95/1.43  
% 6.95/1.43  ------ Resolution
% 6.95/1.43  
% 6.95/1.43  res_num_of_clauses:                     0
% 6.95/1.43  res_num_in_passive:                     0
% 6.95/1.43  res_num_in_active:                      0
% 6.95/1.43  res_num_of_loops:                       64
% 6.95/1.43  res_forward_subset_subsumed:            511
% 6.95/1.43  res_backward_subset_subsumed:           0
% 6.95/1.43  res_forward_subsumed:                   0
% 6.95/1.43  res_backward_subsumed:                  0
% 6.95/1.43  res_forward_subsumption_resolution:     0
% 6.95/1.43  res_backward_subsumption_resolution:    0
% 6.95/1.43  res_clause_to_clause_subsumption:       43824
% 6.95/1.43  res_orphan_elimination:                 0
% 6.95/1.43  res_tautology_del:                      89
% 6.95/1.43  res_num_eq_res_simplified:              0
% 6.95/1.43  res_num_sel_changes:                    0
% 6.95/1.43  res_moves_from_active_to_pass:          0
% 6.95/1.43  
% 6.95/1.43  ------ Superposition
% 6.95/1.43  
% 6.95/1.43  sup_time_total:                         0.
% 6.95/1.43  sup_time_generating:                    0.
% 6.95/1.43  sup_time_sim_full:                      0.
% 6.95/1.43  sup_time_sim_immed:                     0.
% 6.95/1.43  
% 6.95/1.43  sup_num_of_clauses:                     1322
% 6.95/1.43  sup_num_in_active:                      73
% 6.95/1.43  sup_num_in_passive:                     1249
% 6.95/1.43  sup_num_of_loops:                       83
% 6.95/1.43  sup_fw_superposition:                   4602
% 6.95/1.43  sup_bw_superposition:                   2888
% 6.95/1.43  sup_immediate_simplified:               4076
% 6.95/1.43  sup_given_eliminated:                   4
% 6.95/1.43  comparisons_done:                       0
% 6.95/1.43  comparisons_avoided:                    6
% 6.95/1.43  
% 6.95/1.43  ------ Simplifications
% 6.95/1.43  
% 6.95/1.43  
% 6.95/1.43  sim_fw_subset_subsumed:                 0
% 6.95/1.43  sim_bw_subset_subsumed:                 0
% 6.95/1.43  sim_fw_subsumed:                        351
% 6.95/1.43  sim_bw_subsumed:                        10
% 6.95/1.43  sim_fw_subsumption_res:                 0
% 6.95/1.43  sim_bw_subsumption_res:                 0
% 6.95/1.43  sim_tautology_del:                      0
% 6.95/1.43  sim_eq_tautology_del:                   880
% 6.95/1.43  sim_eq_res_simp:                        0
% 6.95/1.43  sim_fw_demodulated:                     2404
% 6.95/1.43  sim_bw_demodulated:                     79
% 6.95/1.43  sim_light_normalised:                   1889
% 6.95/1.43  sim_joinable_taut:                      406
% 6.95/1.43  sim_joinable_simp:                      0
% 6.95/1.43  sim_ac_normalised:                      0
% 6.95/1.43  sim_smt_subsumption:                    0
% 6.95/1.43  
%------------------------------------------------------------------------------
