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
% DateTime   : Thu Dec  3 11:31:03 EST 2020

% Result     : Theorem 19.42s
% Output     : CNFRefutation 19.42s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 202 expanded)
%              Number of clauses        :   35 (  44 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  231 ( 433 expanded)
%              Number of equality atoms :  186 ( 360 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(nnf_transformation,[],[f21])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f77,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f70])).

fof(f78,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f77])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f28])).

fof(f54,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f62,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f47,f61])).

fof(f72,plain,(
    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f54,f61,f62])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f46,f56,f53,f62])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f79,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f55,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_749,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_122,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != X1
    | k3_xboole_0(X1,X0) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_123,plain,
    ( k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_122])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1164,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_43272,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_123,c_1164])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_822,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_2])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1018,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_1015,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_967,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_1025,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1015,c_967])).

cnf(c_1510,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1018,c_1025])).

cnf(c_1526,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1510,c_4])).

cnf(c_2006,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_822,c_1526])).

cnf(c_46402,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_43272,c_2006])).

cnf(c_46404,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_46402,c_6,c_967])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_748,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_46992,plain,
    ( sK3 = X0
    | r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46404,c_748])).

cnf(c_56706,plain,
    ( sK3 = sK1 ),
    inference(superposition,[status(thm)],[c_749,c_46992])).

cnf(c_613,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_860,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_614,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_835,plain,
    ( sK3 != X0
    | sK1 != X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_859,plain,
    ( sK3 != sK1
    | sK1 = sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_15,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_56706,c_860,c_859,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:18:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.42/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.42/3.00  
% 19.42/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.42/3.00  
% 19.42/3.00  ------  iProver source info
% 19.42/3.00  
% 19.42/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.42/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.42/3.00  git: non_committed_changes: false
% 19.42/3.00  git: last_make_outside_of_git: false
% 19.42/3.00  
% 19.42/3.00  ------ 
% 19.42/3.00  
% 19.42/3.00  ------ Input Options
% 19.42/3.00  
% 19.42/3.00  --out_options                           all
% 19.42/3.00  --tptp_safe_out                         true
% 19.42/3.00  --problem_path                          ""
% 19.42/3.00  --include_path                          ""
% 19.42/3.00  --clausifier                            res/vclausify_rel
% 19.42/3.00  --clausifier_options                    --mode clausify
% 19.42/3.00  --stdin                                 false
% 19.42/3.00  --stats_out                             all
% 19.42/3.00  
% 19.42/3.00  ------ General Options
% 19.42/3.00  
% 19.42/3.00  --fof                                   false
% 19.42/3.00  --time_out_real                         305.
% 19.42/3.00  --time_out_virtual                      -1.
% 19.42/3.00  --symbol_type_check                     false
% 19.42/3.00  --clausify_out                          false
% 19.42/3.00  --sig_cnt_out                           false
% 19.42/3.00  --trig_cnt_out                          false
% 19.42/3.00  --trig_cnt_out_tolerance                1.
% 19.42/3.00  --trig_cnt_out_sk_spl                   false
% 19.42/3.00  --abstr_cl_out                          false
% 19.42/3.00  
% 19.42/3.00  ------ Global Options
% 19.42/3.00  
% 19.42/3.00  --schedule                              default
% 19.42/3.00  --add_important_lit                     false
% 19.42/3.00  --prop_solver_per_cl                    1000
% 19.42/3.00  --min_unsat_core                        false
% 19.42/3.00  --soft_assumptions                      false
% 19.42/3.00  --soft_lemma_size                       3
% 19.42/3.00  --prop_impl_unit_size                   0
% 19.42/3.00  --prop_impl_unit                        []
% 19.42/3.00  --share_sel_clauses                     true
% 19.42/3.00  --reset_solvers                         false
% 19.42/3.00  --bc_imp_inh                            [conj_cone]
% 19.42/3.00  --conj_cone_tolerance                   3.
% 19.42/3.00  --extra_neg_conj                        none
% 19.42/3.00  --large_theory_mode                     true
% 19.42/3.00  --prolific_symb_bound                   200
% 19.42/3.00  --lt_threshold                          2000
% 19.42/3.00  --clause_weak_htbl                      true
% 19.42/3.00  --gc_record_bc_elim                     false
% 19.42/3.00  
% 19.42/3.00  ------ Preprocessing Options
% 19.42/3.00  
% 19.42/3.00  --preprocessing_flag                    true
% 19.42/3.00  --time_out_prep_mult                    0.1
% 19.42/3.00  --splitting_mode                        input
% 19.42/3.00  --splitting_grd                         true
% 19.42/3.00  --splitting_cvd                         false
% 19.42/3.00  --splitting_cvd_svl                     false
% 19.42/3.00  --splitting_nvd                         32
% 19.42/3.00  --sub_typing                            true
% 19.42/3.00  --prep_gs_sim                           true
% 19.42/3.00  --prep_unflatten                        true
% 19.42/3.00  --prep_res_sim                          true
% 19.42/3.00  --prep_upred                            true
% 19.42/3.00  --prep_sem_filter                       exhaustive
% 19.42/3.00  --prep_sem_filter_out                   false
% 19.42/3.00  --pred_elim                             true
% 19.42/3.00  --res_sim_input                         true
% 19.42/3.00  --eq_ax_congr_red                       true
% 19.42/3.00  --pure_diseq_elim                       true
% 19.42/3.00  --brand_transform                       false
% 19.42/3.00  --non_eq_to_eq                          false
% 19.42/3.00  --prep_def_merge                        true
% 19.42/3.00  --prep_def_merge_prop_impl              false
% 19.42/3.00  --prep_def_merge_mbd                    true
% 19.42/3.00  --prep_def_merge_tr_red                 false
% 19.42/3.00  --prep_def_merge_tr_cl                  false
% 19.42/3.00  --smt_preprocessing                     true
% 19.42/3.00  --smt_ac_axioms                         fast
% 19.42/3.00  --preprocessed_out                      false
% 19.42/3.00  --preprocessed_stats                    false
% 19.42/3.00  
% 19.42/3.00  ------ Abstraction refinement Options
% 19.42/3.00  
% 19.42/3.00  --abstr_ref                             []
% 19.42/3.00  --abstr_ref_prep                        false
% 19.42/3.00  --abstr_ref_until_sat                   false
% 19.42/3.00  --abstr_ref_sig_restrict                funpre
% 19.42/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.42/3.00  --abstr_ref_under                       []
% 19.42/3.00  
% 19.42/3.00  ------ SAT Options
% 19.42/3.00  
% 19.42/3.00  --sat_mode                              false
% 19.42/3.00  --sat_fm_restart_options                ""
% 19.42/3.00  --sat_gr_def                            false
% 19.42/3.00  --sat_epr_types                         true
% 19.42/3.00  --sat_non_cyclic_types                  false
% 19.42/3.00  --sat_finite_models                     false
% 19.42/3.00  --sat_fm_lemmas                         false
% 19.42/3.00  --sat_fm_prep                           false
% 19.42/3.00  --sat_fm_uc_incr                        true
% 19.42/3.00  --sat_out_model                         small
% 19.42/3.00  --sat_out_clauses                       false
% 19.42/3.00  
% 19.42/3.00  ------ QBF Options
% 19.42/3.00  
% 19.42/3.00  --qbf_mode                              false
% 19.42/3.00  --qbf_elim_univ                         false
% 19.42/3.00  --qbf_dom_inst                          none
% 19.42/3.00  --qbf_dom_pre_inst                      false
% 19.42/3.00  --qbf_sk_in                             false
% 19.42/3.00  --qbf_pred_elim                         true
% 19.42/3.00  --qbf_split                             512
% 19.42/3.00  
% 19.42/3.00  ------ BMC1 Options
% 19.42/3.00  
% 19.42/3.00  --bmc1_incremental                      false
% 19.42/3.00  --bmc1_axioms                           reachable_all
% 19.42/3.00  --bmc1_min_bound                        0
% 19.42/3.00  --bmc1_max_bound                        -1
% 19.42/3.00  --bmc1_max_bound_default                -1
% 19.42/3.00  --bmc1_symbol_reachability              true
% 19.42/3.00  --bmc1_property_lemmas                  false
% 19.42/3.00  --bmc1_k_induction                      false
% 19.42/3.00  --bmc1_non_equiv_states                 false
% 19.42/3.00  --bmc1_deadlock                         false
% 19.42/3.00  --bmc1_ucm                              false
% 19.42/3.00  --bmc1_add_unsat_core                   none
% 19.42/3.00  --bmc1_unsat_core_children              false
% 19.42/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.42/3.00  --bmc1_out_stat                         full
% 19.42/3.00  --bmc1_ground_init                      false
% 19.42/3.00  --bmc1_pre_inst_next_state              false
% 19.42/3.00  --bmc1_pre_inst_state                   false
% 19.42/3.00  --bmc1_pre_inst_reach_state             false
% 19.42/3.00  --bmc1_out_unsat_core                   false
% 19.42/3.00  --bmc1_aig_witness_out                  false
% 19.42/3.00  --bmc1_verbose                          false
% 19.42/3.00  --bmc1_dump_clauses_tptp                false
% 19.42/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.42/3.00  --bmc1_dump_file                        -
% 19.42/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.42/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.42/3.00  --bmc1_ucm_extend_mode                  1
% 19.42/3.00  --bmc1_ucm_init_mode                    2
% 19.42/3.00  --bmc1_ucm_cone_mode                    none
% 19.42/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.42/3.00  --bmc1_ucm_relax_model                  4
% 19.42/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.42/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.42/3.00  --bmc1_ucm_layered_model                none
% 19.42/3.00  --bmc1_ucm_max_lemma_size               10
% 19.42/3.00  
% 19.42/3.00  ------ AIG Options
% 19.42/3.00  
% 19.42/3.00  --aig_mode                              false
% 19.42/3.00  
% 19.42/3.00  ------ Instantiation Options
% 19.42/3.00  
% 19.42/3.00  --instantiation_flag                    true
% 19.42/3.00  --inst_sos_flag                         false
% 19.42/3.00  --inst_sos_phase                        true
% 19.42/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.42/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.42/3.00  --inst_lit_sel_side                     num_symb
% 19.42/3.00  --inst_solver_per_active                1400
% 19.42/3.00  --inst_solver_calls_frac                1.
% 19.42/3.00  --inst_passive_queue_type               priority_queues
% 19.42/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.42/3.00  --inst_passive_queues_freq              [25;2]
% 19.42/3.00  --inst_dismatching                      true
% 19.42/3.00  --inst_eager_unprocessed_to_passive     true
% 19.42/3.00  --inst_prop_sim_given                   true
% 19.42/3.00  --inst_prop_sim_new                     false
% 19.42/3.00  --inst_subs_new                         false
% 19.42/3.00  --inst_eq_res_simp                      false
% 19.42/3.00  --inst_subs_given                       false
% 19.42/3.00  --inst_orphan_elimination               true
% 19.42/3.00  --inst_learning_loop_flag               true
% 19.42/3.00  --inst_learning_start                   3000
% 19.42/3.00  --inst_learning_factor                  2
% 19.42/3.00  --inst_start_prop_sim_after_learn       3
% 19.42/3.00  --inst_sel_renew                        solver
% 19.42/3.00  --inst_lit_activity_flag                true
% 19.42/3.00  --inst_restr_to_given                   false
% 19.42/3.00  --inst_activity_threshold               500
% 19.42/3.00  --inst_out_proof                        true
% 19.42/3.00  
% 19.42/3.00  ------ Resolution Options
% 19.42/3.00  
% 19.42/3.00  --resolution_flag                       true
% 19.42/3.00  --res_lit_sel                           adaptive
% 19.42/3.00  --res_lit_sel_side                      none
% 19.42/3.00  --res_ordering                          kbo
% 19.42/3.00  --res_to_prop_solver                    active
% 19.42/3.00  --res_prop_simpl_new                    false
% 19.42/3.00  --res_prop_simpl_given                  true
% 19.42/3.00  --res_passive_queue_type                priority_queues
% 19.42/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.42/3.00  --res_passive_queues_freq               [15;5]
% 19.42/3.00  --res_forward_subs                      full
% 19.42/3.00  --res_backward_subs                     full
% 19.42/3.00  --res_forward_subs_resolution           true
% 19.42/3.00  --res_backward_subs_resolution          true
% 19.42/3.00  --res_orphan_elimination                true
% 19.42/3.00  --res_time_limit                        2.
% 19.42/3.00  --res_out_proof                         true
% 19.42/3.00  
% 19.42/3.00  ------ Superposition Options
% 19.42/3.00  
% 19.42/3.00  --superposition_flag                    true
% 19.42/3.00  --sup_passive_queue_type                priority_queues
% 19.42/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.42/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.42/3.00  --demod_completeness_check              fast
% 19.42/3.00  --demod_use_ground                      true
% 19.42/3.00  --sup_to_prop_solver                    passive
% 19.42/3.00  --sup_prop_simpl_new                    true
% 19.42/3.00  --sup_prop_simpl_given                  true
% 19.42/3.00  --sup_fun_splitting                     false
% 19.42/3.00  --sup_smt_interval                      50000
% 19.42/3.00  
% 19.42/3.00  ------ Superposition Simplification Setup
% 19.42/3.00  
% 19.42/3.00  --sup_indices_passive                   []
% 19.42/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.42/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.00  --sup_full_bw                           [BwDemod]
% 19.42/3.00  --sup_immed_triv                        [TrivRules]
% 19.42/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.42/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.00  --sup_immed_bw_main                     []
% 19.42/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.42/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.42/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.42/3.00  
% 19.42/3.00  ------ Combination Options
% 19.42/3.00  
% 19.42/3.00  --comb_res_mult                         3
% 19.42/3.00  --comb_sup_mult                         2
% 19.42/3.00  --comb_inst_mult                        10
% 19.42/3.00  
% 19.42/3.00  ------ Debug Options
% 19.42/3.00  
% 19.42/3.00  --dbg_backtrace                         false
% 19.42/3.00  --dbg_dump_prop_clauses                 false
% 19.42/3.00  --dbg_dump_prop_clauses_file            -
% 19.42/3.00  --dbg_out_stat                          false
% 19.42/3.00  ------ Parsing...
% 19.42/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.42/3.00  
% 19.42/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.42/3.00  
% 19.42/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.42/3.00  
% 19.42/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.42/3.00  ------ Proving...
% 19.42/3.00  ------ Problem Properties 
% 19.42/3.00  
% 19.42/3.00  
% 19.42/3.00  clauses                                 16
% 19.42/3.00  conjectures                             1
% 19.42/3.00  EPR                                     1
% 19.42/3.00  Horn                                    14
% 19.42/3.00  unary                                   11
% 19.42/3.00  binary                                  0
% 19.42/3.00  lits                                    29
% 19.42/3.00  lits eq                                 21
% 19.42/3.00  fd_pure                                 0
% 19.42/3.00  fd_pseudo                               0
% 19.42/3.00  fd_cond                                 0
% 19.42/3.00  fd_pseudo_cond                          4
% 19.42/3.00  AC symbols                              1
% 19.42/3.00  
% 19.42/3.00  ------ Schedule dynamic 5 is on 
% 19.42/3.00  
% 19.42/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.42/3.00  
% 19.42/3.00  
% 19.42/3.00  ------ 
% 19.42/3.00  Current options:
% 19.42/3.00  ------ 
% 19.42/3.00  
% 19.42/3.00  ------ Input Options
% 19.42/3.00  
% 19.42/3.00  --out_options                           all
% 19.42/3.00  --tptp_safe_out                         true
% 19.42/3.00  --problem_path                          ""
% 19.42/3.00  --include_path                          ""
% 19.42/3.00  --clausifier                            res/vclausify_rel
% 19.42/3.00  --clausifier_options                    --mode clausify
% 19.42/3.00  --stdin                                 false
% 19.42/3.00  --stats_out                             all
% 19.42/3.00  
% 19.42/3.00  ------ General Options
% 19.42/3.00  
% 19.42/3.00  --fof                                   false
% 19.42/3.00  --time_out_real                         305.
% 19.42/3.00  --time_out_virtual                      -1.
% 19.42/3.00  --symbol_type_check                     false
% 19.42/3.00  --clausify_out                          false
% 19.42/3.00  --sig_cnt_out                           false
% 19.42/3.00  --trig_cnt_out                          false
% 19.42/3.00  --trig_cnt_out_tolerance                1.
% 19.42/3.00  --trig_cnt_out_sk_spl                   false
% 19.42/3.00  --abstr_cl_out                          false
% 19.42/3.00  
% 19.42/3.00  ------ Global Options
% 19.42/3.00  
% 19.42/3.00  --schedule                              default
% 19.42/3.00  --add_important_lit                     false
% 19.42/3.00  --prop_solver_per_cl                    1000
% 19.42/3.00  --min_unsat_core                        false
% 19.42/3.00  --soft_assumptions                      false
% 19.42/3.00  --soft_lemma_size                       3
% 19.42/3.00  --prop_impl_unit_size                   0
% 19.42/3.00  --prop_impl_unit                        []
% 19.42/3.00  --share_sel_clauses                     true
% 19.42/3.00  --reset_solvers                         false
% 19.42/3.00  --bc_imp_inh                            [conj_cone]
% 19.42/3.00  --conj_cone_tolerance                   3.
% 19.42/3.00  --extra_neg_conj                        none
% 19.42/3.00  --large_theory_mode                     true
% 19.42/3.00  --prolific_symb_bound                   200
% 19.42/3.00  --lt_threshold                          2000
% 19.42/3.00  --clause_weak_htbl                      true
% 19.42/3.00  --gc_record_bc_elim                     false
% 19.42/3.00  
% 19.42/3.00  ------ Preprocessing Options
% 19.42/3.00  
% 19.42/3.00  --preprocessing_flag                    true
% 19.42/3.00  --time_out_prep_mult                    0.1
% 19.42/3.00  --splitting_mode                        input
% 19.42/3.00  --splitting_grd                         true
% 19.42/3.00  --splitting_cvd                         false
% 19.42/3.00  --splitting_cvd_svl                     false
% 19.42/3.00  --splitting_nvd                         32
% 19.42/3.00  --sub_typing                            true
% 19.42/3.00  --prep_gs_sim                           true
% 19.42/3.00  --prep_unflatten                        true
% 19.42/3.00  --prep_res_sim                          true
% 19.42/3.00  --prep_upred                            true
% 19.42/3.00  --prep_sem_filter                       exhaustive
% 19.42/3.00  --prep_sem_filter_out                   false
% 19.42/3.00  --pred_elim                             true
% 19.42/3.00  --res_sim_input                         true
% 19.42/3.00  --eq_ax_congr_red                       true
% 19.42/3.00  --pure_diseq_elim                       true
% 19.42/3.00  --brand_transform                       false
% 19.42/3.00  --non_eq_to_eq                          false
% 19.42/3.00  --prep_def_merge                        true
% 19.42/3.00  --prep_def_merge_prop_impl              false
% 19.42/3.00  --prep_def_merge_mbd                    true
% 19.42/3.00  --prep_def_merge_tr_red                 false
% 19.42/3.00  --prep_def_merge_tr_cl                  false
% 19.42/3.00  --smt_preprocessing                     true
% 19.42/3.00  --smt_ac_axioms                         fast
% 19.42/3.00  --preprocessed_out                      false
% 19.42/3.00  --preprocessed_stats                    false
% 19.42/3.00  
% 19.42/3.00  ------ Abstraction refinement Options
% 19.42/3.00  
% 19.42/3.00  --abstr_ref                             []
% 19.42/3.00  --abstr_ref_prep                        false
% 19.42/3.00  --abstr_ref_until_sat                   false
% 19.42/3.00  --abstr_ref_sig_restrict                funpre
% 19.42/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.42/3.00  --abstr_ref_under                       []
% 19.42/3.00  
% 19.42/3.00  ------ SAT Options
% 19.42/3.00  
% 19.42/3.00  --sat_mode                              false
% 19.42/3.00  --sat_fm_restart_options                ""
% 19.42/3.00  --sat_gr_def                            false
% 19.42/3.00  --sat_epr_types                         true
% 19.42/3.00  --sat_non_cyclic_types                  false
% 19.42/3.00  --sat_finite_models                     false
% 19.42/3.00  --sat_fm_lemmas                         false
% 19.42/3.00  --sat_fm_prep                           false
% 19.42/3.00  --sat_fm_uc_incr                        true
% 19.42/3.00  --sat_out_model                         small
% 19.42/3.00  --sat_out_clauses                       false
% 19.42/3.00  
% 19.42/3.00  ------ QBF Options
% 19.42/3.00  
% 19.42/3.00  --qbf_mode                              false
% 19.42/3.00  --qbf_elim_univ                         false
% 19.42/3.00  --qbf_dom_inst                          none
% 19.42/3.00  --qbf_dom_pre_inst                      false
% 19.42/3.00  --qbf_sk_in                             false
% 19.42/3.00  --qbf_pred_elim                         true
% 19.42/3.00  --qbf_split                             512
% 19.42/3.00  
% 19.42/3.00  ------ BMC1 Options
% 19.42/3.00  
% 19.42/3.00  --bmc1_incremental                      false
% 19.42/3.00  --bmc1_axioms                           reachable_all
% 19.42/3.00  --bmc1_min_bound                        0
% 19.42/3.00  --bmc1_max_bound                        -1
% 19.42/3.00  --bmc1_max_bound_default                -1
% 19.42/3.00  --bmc1_symbol_reachability              true
% 19.42/3.00  --bmc1_property_lemmas                  false
% 19.42/3.00  --bmc1_k_induction                      false
% 19.42/3.00  --bmc1_non_equiv_states                 false
% 19.42/3.00  --bmc1_deadlock                         false
% 19.42/3.00  --bmc1_ucm                              false
% 19.42/3.00  --bmc1_add_unsat_core                   none
% 19.42/3.00  --bmc1_unsat_core_children              false
% 19.42/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.42/3.00  --bmc1_out_stat                         full
% 19.42/3.00  --bmc1_ground_init                      false
% 19.42/3.00  --bmc1_pre_inst_next_state              false
% 19.42/3.00  --bmc1_pre_inst_state                   false
% 19.42/3.00  --bmc1_pre_inst_reach_state             false
% 19.42/3.00  --bmc1_out_unsat_core                   false
% 19.42/3.00  --bmc1_aig_witness_out                  false
% 19.42/3.00  --bmc1_verbose                          false
% 19.42/3.00  --bmc1_dump_clauses_tptp                false
% 19.42/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.42/3.00  --bmc1_dump_file                        -
% 19.42/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.42/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.42/3.00  --bmc1_ucm_extend_mode                  1
% 19.42/3.00  --bmc1_ucm_init_mode                    2
% 19.42/3.00  --bmc1_ucm_cone_mode                    none
% 19.42/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.42/3.00  --bmc1_ucm_relax_model                  4
% 19.42/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.42/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.42/3.00  --bmc1_ucm_layered_model                none
% 19.42/3.00  --bmc1_ucm_max_lemma_size               10
% 19.42/3.00  
% 19.42/3.00  ------ AIG Options
% 19.42/3.00  
% 19.42/3.00  --aig_mode                              false
% 19.42/3.00  
% 19.42/3.00  ------ Instantiation Options
% 19.42/3.00  
% 19.42/3.00  --instantiation_flag                    true
% 19.42/3.00  --inst_sos_flag                         false
% 19.42/3.00  --inst_sos_phase                        true
% 19.42/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.42/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.42/3.00  --inst_lit_sel_side                     none
% 19.42/3.00  --inst_solver_per_active                1400
% 19.42/3.00  --inst_solver_calls_frac                1.
% 19.42/3.00  --inst_passive_queue_type               priority_queues
% 19.42/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.42/3.00  --inst_passive_queues_freq              [25;2]
% 19.42/3.00  --inst_dismatching                      true
% 19.42/3.00  --inst_eager_unprocessed_to_passive     true
% 19.42/3.00  --inst_prop_sim_given                   true
% 19.42/3.00  --inst_prop_sim_new                     false
% 19.42/3.00  --inst_subs_new                         false
% 19.42/3.00  --inst_eq_res_simp                      false
% 19.42/3.00  --inst_subs_given                       false
% 19.42/3.00  --inst_orphan_elimination               true
% 19.42/3.00  --inst_learning_loop_flag               true
% 19.42/3.00  --inst_learning_start                   3000
% 19.42/3.00  --inst_learning_factor                  2
% 19.42/3.00  --inst_start_prop_sim_after_learn       3
% 19.42/3.00  --inst_sel_renew                        solver
% 19.42/3.00  --inst_lit_activity_flag                true
% 19.42/3.00  --inst_restr_to_given                   false
% 19.42/3.00  --inst_activity_threshold               500
% 19.42/3.00  --inst_out_proof                        true
% 19.42/3.00  
% 19.42/3.00  ------ Resolution Options
% 19.42/3.00  
% 19.42/3.00  --resolution_flag                       false
% 19.42/3.00  --res_lit_sel                           adaptive
% 19.42/3.00  --res_lit_sel_side                      none
% 19.42/3.00  --res_ordering                          kbo
% 19.42/3.00  --res_to_prop_solver                    active
% 19.42/3.00  --res_prop_simpl_new                    false
% 19.42/3.00  --res_prop_simpl_given                  true
% 19.42/3.00  --res_passive_queue_type                priority_queues
% 19.42/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.42/3.00  --res_passive_queues_freq               [15;5]
% 19.42/3.00  --res_forward_subs                      full
% 19.42/3.00  --res_backward_subs                     full
% 19.42/3.00  --res_forward_subs_resolution           true
% 19.42/3.00  --res_backward_subs_resolution          true
% 19.42/3.00  --res_orphan_elimination                true
% 19.42/3.00  --res_time_limit                        2.
% 19.42/3.00  --res_out_proof                         true
% 19.42/3.00  
% 19.42/3.00  ------ Superposition Options
% 19.42/3.00  
% 19.42/3.00  --superposition_flag                    true
% 19.42/3.00  --sup_passive_queue_type                priority_queues
% 19.42/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.42/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.42/3.00  --demod_completeness_check              fast
% 19.42/3.00  --demod_use_ground                      true
% 19.42/3.00  --sup_to_prop_solver                    passive
% 19.42/3.00  --sup_prop_simpl_new                    true
% 19.42/3.00  --sup_prop_simpl_given                  true
% 19.42/3.00  --sup_fun_splitting                     false
% 19.42/3.00  --sup_smt_interval                      50000
% 19.42/3.00  
% 19.42/3.00  ------ Superposition Simplification Setup
% 19.42/3.00  
% 19.42/3.00  --sup_indices_passive                   []
% 19.42/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.42/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.00  --sup_full_bw                           [BwDemod]
% 19.42/3.00  --sup_immed_triv                        [TrivRules]
% 19.42/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.42/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.00  --sup_immed_bw_main                     []
% 19.42/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.42/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.42/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.42/3.00  
% 19.42/3.00  ------ Combination Options
% 19.42/3.00  
% 19.42/3.00  --comb_res_mult                         3
% 19.42/3.00  --comb_sup_mult                         2
% 19.42/3.00  --comb_inst_mult                        10
% 19.42/3.00  
% 19.42/3.00  ------ Debug Options
% 19.42/3.00  
% 19.42/3.00  --dbg_backtrace                         false
% 19.42/3.00  --dbg_dump_prop_clauses                 false
% 19.42/3.00  --dbg_dump_prop_clauses_file            -
% 19.42/3.00  --dbg_out_stat                          false
% 19.42/3.00  
% 19.42/3.00  
% 19.42/3.00  
% 19.42/3.00  
% 19.42/3.00  ------ Proving...
% 19.42/3.00  
% 19.42/3.00  
% 19.42/3.00  % SZS status Theorem for theBenchmark.p
% 19.42/3.00  
% 19.42/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.42/3.00  
% 19.42/3.00  fof(f9,axiom,(
% 19.42/3.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f21,plain,(
% 19.42/3.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 19.42/3.00    inference(ennf_transformation,[],[f9])).
% 19.42/3.00  
% 19.42/3.00  fof(f23,plain,(
% 19.42/3.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.42/3.00    inference(nnf_transformation,[],[f21])).
% 19.42/3.00  
% 19.42/3.00  fof(f24,plain,(
% 19.42/3.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.42/3.00    inference(flattening,[],[f23])).
% 19.42/3.00  
% 19.42/3.00  fof(f25,plain,(
% 19.42/3.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.42/3.00    inference(rectify,[],[f24])).
% 19.42/3.00  
% 19.42/3.00  fof(f26,plain,(
% 19.42/3.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 19.42/3.00    introduced(choice_axiom,[])).
% 19.42/3.00  
% 19.42/3.00  fof(f27,plain,(
% 19.42/3.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.42/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 19.42/3.00  
% 19.42/3.00  fof(f39,plain,(
% 19.42/3.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 19.42/3.00    inference(cnf_transformation,[],[f27])).
% 19.42/3.00  
% 19.42/3.00  fof(f13,axiom,(
% 19.42/3.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f49,plain,(
% 19.42/3.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f13])).
% 19.42/3.00  
% 19.42/3.00  fof(f14,axiom,(
% 19.42/3.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f50,plain,(
% 19.42/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f14])).
% 19.42/3.00  
% 19.42/3.00  fof(f15,axiom,(
% 19.42/3.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f51,plain,(
% 19.42/3.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f15])).
% 19.42/3.00  
% 19.42/3.00  fof(f16,axiom,(
% 19.42/3.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f52,plain,(
% 19.42/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f16])).
% 19.42/3.00  
% 19.42/3.00  fof(f17,axiom,(
% 19.42/3.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f53,plain,(
% 19.42/3.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f17])).
% 19.42/3.00  
% 19.42/3.00  fof(f57,plain,(
% 19.42/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 19.42/3.00    inference(definition_unfolding,[],[f52,f53])).
% 19.42/3.00  
% 19.42/3.00  fof(f58,plain,(
% 19.42/3.00    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 19.42/3.00    inference(definition_unfolding,[],[f51,f57])).
% 19.42/3.00  
% 19.42/3.00  fof(f59,plain,(
% 19.42/3.00    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 19.42/3.00    inference(definition_unfolding,[],[f50,f58])).
% 19.42/3.00  
% 19.42/3.00  fof(f60,plain,(
% 19.42/3.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.42/3.00    inference(definition_unfolding,[],[f49,f59])).
% 19.42/3.00  
% 19.42/3.00  fof(f70,plain,(
% 19.42/3.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 19.42/3.00    inference(definition_unfolding,[],[f39,f60])).
% 19.42/3.00  
% 19.42/3.00  fof(f77,plain,(
% 19.42/3.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 19.42/3.00    inference(equality_resolution,[],[f70])).
% 19.42/3.00  
% 19.42/3.00  fof(f78,plain,(
% 19.42/3.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 19.42/3.00    inference(equality_resolution,[],[f77])).
% 19.42/3.00  
% 19.42/3.00  fof(f4,axiom,(
% 19.42/3.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f20,plain,(
% 19.42/3.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.42/3.00    inference(ennf_transformation,[],[f4])).
% 19.42/3.00  
% 19.42/3.00  fof(f33,plain,(
% 19.42/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f20])).
% 19.42/3.00  
% 19.42/3.00  fof(f18,conjecture,(
% 19.42/3.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f19,negated_conjecture,(
% 19.42/3.00    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 19.42/3.00    inference(negated_conjecture,[],[f18])).
% 19.42/3.00  
% 19.42/3.00  fof(f22,plain,(
% 19.42/3.00    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 19.42/3.00    inference(ennf_transformation,[],[f19])).
% 19.42/3.00  
% 19.42/3.00  fof(f28,plain,(
% 19.42/3.00    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 19.42/3.00    introduced(choice_axiom,[])).
% 19.42/3.00  
% 19.42/3.00  fof(f29,plain,(
% 19.42/3.00    sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3))),
% 19.42/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f28])).
% 19.42/3.00  
% 19.42/3.00  fof(f54,plain,(
% 19.42/3.00    r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3))),
% 19.42/3.00    inference(cnf_transformation,[],[f29])).
% 19.42/3.00  
% 19.42/3.00  fof(f11,axiom,(
% 19.42/3.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f47,plain,(
% 19.42/3.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f11])).
% 19.42/3.00  
% 19.42/3.00  fof(f12,axiom,(
% 19.42/3.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f48,plain,(
% 19.42/3.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f12])).
% 19.42/3.00  
% 19.42/3.00  fof(f61,plain,(
% 19.42/3.00    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.42/3.00    inference(definition_unfolding,[],[f48,f60])).
% 19.42/3.00  
% 19.42/3.00  fof(f62,plain,(
% 19.42/3.00    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 19.42/3.00    inference(definition_unfolding,[],[f47,f61])).
% 19.42/3.00  
% 19.42/3.00  fof(f72,plain,(
% 19.42/3.00    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 19.42/3.00    inference(definition_unfolding,[],[f54,f61,f62])).
% 19.42/3.00  
% 19.42/3.00  fof(f1,axiom,(
% 19.42/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f30,plain,(
% 19.42/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f1])).
% 19.42/3.00  
% 19.42/3.00  fof(f10,axiom,(
% 19.42/3.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f46,plain,(
% 19.42/3.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f10])).
% 19.42/3.00  
% 19.42/3.00  fof(f8,axiom,(
% 19.42/3.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f37,plain,(
% 19.42/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f8])).
% 19.42/3.00  
% 19.42/3.00  fof(f3,axiom,(
% 19.42/3.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f32,plain,(
% 19.42/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f3])).
% 19.42/3.00  
% 19.42/3.00  fof(f56,plain,(
% 19.42/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 19.42/3.00    inference(definition_unfolding,[],[f37,f32])).
% 19.42/3.00  
% 19.42/3.00  fof(f63,plain,(
% 19.42/3.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 19.42/3.00    inference(definition_unfolding,[],[f46,f56,f53,f62])).
% 19.42/3.00  
% 19.42/3.00  fof(f6,axiom,(
% 19.42/3.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f35,plain,(
% 19.42/3.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f6])).
% 19.42/3.00  
% 19.42/3.00  fof(f2,axiom,(
% 19.42/3.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f31,plain,(
% 19.42/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 19.42/3.00    inference(cnf_transformation,[],[f2])).
% 19.42/3.00  
% 19.42/3.00  fof(f7,axiom,(
% 19.42/3.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f36,plain,(
% 19.42/3.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 19.42/3.00    inference(cnf_transformation,[],[f7])).
% 19.42/3.00  
% 19.42/3.00  fof(f5,axiom,(
% 19.42/3.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.42/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.42/3.00  
% 19.42/3.00  fof(f34,plain,(
% 19.42/3.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.42/3.00    inference(cnf_transformation,[],[f5])).
% 19.42/3.00  
% 19.42/3.00  fof(f38,plain,(
% 19.42/3.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 19.42/3.00    inference(cnf_transformation,[],[f27])).
% 19.42/3.00  
% 19.42/3.00  fof(f71,plain,(
% 19.42/3.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 19.42/3.00    inference(definition_unfolding,[],[f38,f60])).
% 19.42/3.00  
% 19.42/3.00  fof(f79,plain,(
% 19.42/3.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 19.42/3.00    inference(equality_resolution,[],[f71])).
% 19.42/3.00  
% 19.42/3.00  fof(f55,plain,(
% 19.42/3.00    sK1 != sK3),
% 19.42/3.00    inference(cnf_transformation,[],[f29])).
% 19.42/3.00  
% 19.42/3.00  cnf(c_13,plain,
% 19.42/3.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 19.42/3.00      inference(cnf_transformation,[],[f78]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_749,plain,
% 19.42/3.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 19.42/3.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_3,plain,
% 19.42/3.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 19.42/3.00      inference(cnf_transformation,[],[f33]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_16,negated_conjecture,
% 19.42/3.00      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 19.42/3.00      inference(cnf_transformation,[],[f72]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_122,plain,
% 19.42/3.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
% 19.42/3.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != X1
% 19.42/3.00      | k3_xboole_0(X1,X0) = X1 ),
% 19.42/3.00      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_123,plain,
% 19.42/3.00      ( k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
% 19.42/3.00      inference(unflattening,[status(thm)],[c_122]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_1,plain,
% 19.42/3.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 19.42/3.00      inference(cnf_transformation,[],[f30]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_0,plain,
% 19.42/3.00      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 19.42/3.00      inference(cnf_transformation,[],[f63]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_1164,plain,
% 19.42/3.00      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_43272,plain,
% 19.42/3.00      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK3) ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_123,c_1164]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_5,plain,
% 19.42/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.42/3.00      inference(cnf_transformation,[],[f35]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_2,plain,
% 19.42/3.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.42/3.00      inference(cnf_transformation,[],[f31]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_822,plain,
% 19.42/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_5,c_2]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_6,plain,
% 19.42/3.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.42/3.00      inference(cnf_transformation,[],[f36]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_1018,plain,
% 19.42/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_1015,plain,
% 19.42/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_4,plain,
% 19.42/3.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.42/3.00      inference(cnf_transformation,[],[f34]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_967,plain,
% 19.42/3.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_1025,plain,
% 19.42/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 19.42/3.00      inference(demodulation,[status(thm)],[c_1015,c_967]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_1510,plain,
% 19.42/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_1018,c_1025]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_1526,plain,
% 19.42/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 19.42/3.00      inference(demodulation,[status(thm)],[c_1510,c_4]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_2006,plain,
% 19.42/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_822,c_1526]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_46402,plain,
% 19.42/3.00      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_43272,c_2006]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_46404,plain,
% 19.42/3.00      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 19.42/3.00      inference(demodulation,[status(thm)],[c_46402,c_6,c_967]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_14,plain,
% 19.42/3.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 19.42/3.00      | X0 = X1
% 19.42/3.00      | X0 = X2
% 19.42/3.00      | X0 = X3 ),
% 19.42/3.00      inference(cnf_transformation,[],[f79]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_748,plain,
% 19.42/3.00      ( X0 = X1
% 19.42/3.00      | X0 = X2
% 19.42/3.00      | X0 = X3
% 19.42/3.00      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
% 19.42/3.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_46992,plain,
% 19.42/3.00      ( sK3 = X0
% 19.42/3.00      | r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK3)) != iProver_top ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_46404,c_748]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_56706,plain,
% 19.42/3.00      ( sK3 = sK1 ),
% 19.42/3.00      inference(superposition,[status(thm)],[c_749,c_46992]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_613,plain,( X0 = X0 ),theory(equality) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_860,plain,
% 19.42/3.00      ( sK1 = sK1 ),
% 19.42/3.00      inference(instantiation,[status(thm)],[c_613]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_614,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_835,plain,
% 19.42/3.00      ( sK3 != X0 | sK1 != X0 | sK1 = sK3 ),
% 19.42/3.00      inference(instantiation,[status(thm)],[c_614]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_859,plain,
% 19.42/3.00      ( sK3 != sK1 | sK1 = sK3 | sK1 != sK1 ),
% 19.42/3.00      inference(instantiation,[status(thm)],[c_835]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(c_15,negated_conjecture,
% 19.42/3.00      ( sK1 != sK3 ),
% 19.42/3.00      inference(cnf_transformation,[],[f55]) ).
% 19.42/3.00  
% 19.42/3.00  cnf(contradiction,plain,
% 19.42/3.00      ( $false ),
% 19.42/3.00      inference(minisat,[status(thm)],[c_56706,c_860,c_859,c_15]) ).
% 19.42/3.00  
% 19.42/3.00  
% 19.42/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.42/3.00  
% 19.42/3.00  ------                               Statistics
% 19.42/3.00  
% 19.42/3.00  ------ General
% 19.42/3.00  
% 19.42/3.00  abstr_ref_over_cycles:                  0
% 19.42/3.00  abstr_ref_under_cycles:                 0
% 19.42/3.00  gc_basic_clause_elim:                   0
% 19.42/3.00  forced_gc_time:                         0
% 19.42/3.00  parsing_time:                           0.008
% 19.42/3.00  unif_index_cands_time:                  0.
% 19.42/3.00  unif_index_add_time:                    0.
% 19.42/3.00  orderings_time:                         0.
% 19.42/3.00  out_proof_time:                         0.012
% 19.42/3.00  total_time:                             2.415
% 19.42/3.00  num_of_symbols:                         41
% 19.42/3.00  num_of_terms:                           69021
% 19.42/3.00  
% 19.42/3.00  ------ Preprocessing
% 19.42/3.00  
% 19.42/3.00  num_of_splits:                          0
% 19.42/3.00  num_of_split_atoms:                     0
% 19.42/3.00  num_of_reused_defs:                     0
% 19.42/3.00  num_eq_ax_congr_red:                    12
% 19.42/3.00  num_of_sem_filtered_clauses:            1
% 19.42/3.00  num_of_subtypes:                        0
% 19.42/3.00  monotx_restored_types:                  0
% 19.42/3.00  sat_num_of_epr_types:                   0
% 19.42/3.00  sat_num_of_non_cyclic_types:            0
% 19.42/3.00  sat_guarded_non_collapsed_types:        0
% 19.42/3.00  num_pure_diseq_elim:                    0
% 19.42/3.00  simp_replaced_by:                       0
% 19.42/3.00  res_preprocessed:                       78
% 19.42/3.00  prep_upred:                             0
% 19.42/3.00  prep_unflattend:                        30
% 19.42/3.00  smt_new_axioms:                         0
% 19.42/3.00  pred_elim_cands:                        1
% 19.42/3.00  pred_elim:                              1
% 19.42/3.00  pred_elim_cl:                           1
% 19.42/3.00  pred_elim_cycles:                       3
% 19.42/3.00  merged_defs:                            0
% 19.42/3.00  merged_defs_ncl:                        0
% 19.42/3.00  bin_hyper_res:                          0
% 19.42/3.00  prep_cycles:                            4
% 19.42/3.00  pred_elim_time:                         0.006
% 19.42/3.00  splitting_time:                         0.
% 19.42/3.00  sem_filter_time:                        0.
% 19.42/3.00  monotx_time:                            0.
% 19.42/3.00  subtype_inf_time:                       0.
% 19.42/3.00  
% 19.42/3.00  ------ Problem properties
% 19.42/3.00  
% 19.42/3.00  clauses:                                16
% 19.42/3.00  conjectures:                            1
% 19.42/3.00  epr:                                    1
% 19.42/3.00  horn:                                   14
% 19.42/3.00  ground:                                 2
% 19.42/3.00  unary:                                  11
% 19.42/3.00  binary:                                 0
% 19.42/3.00  lits:                                   29
% 19.42/3.00  lits_eq:                                21
% 19.42/3.00  fd_pure:                                0
% 19.42/3.00  fd_pseudo:                              0
% 19.42/3.00  fd_cond:                                0
% 19.42/3.00  fd_pseudo_cond:                         4
% 19.42/3.00  ac_symbols:                             1
% 19.42/3.00  
% 19.42/3.00  ------ Propositional Solver
% 19.42/3.00  
% 19.42/3.00  prop_solver_calls:                      30
% 19.42/3.00  prop_fast_solver_calls:                 569
% 19.42/3.00  smt_solver_calls:                       0
% 19.42/3.00  smt_fast_solver_calls:                  0
% 19.42/3.00  prop_num_of_clauses:                    11669
% 19.42/3.00  prop_preprocess_simplified:             20396
% 19.42/3.00  prop_fo_subsumed:                       0
% 19.42/3.00  prop_solver_time:                       0.
% 19.42/3.00  smt_solver_time:                        0.
% 19.42/3.00  smt_fast_solver_time:                   0.
% 19.42/3.00  prop_fast_solver_time:                  0.
% 19.42/3.00  prop_unsat_core_time:                   0.002
% 19.42/3.00  
% 19.42/3.00  ------ QBF
% 19.42/3.00  
% 19.42/3.00  qbf_q_res:                              0
% 19.42/3.00  qbf_num_tautologies:                    0
% 19.42/3.00  qbf_prep_cycles:                        0
% 19.42/3.00  
% 19.42/3.00  ------ BMC1
% 19.42/3.00  
% 19.42/3.00  bmc1_current_bound:                     -1
% 19.42/3.00  bmc1_last_solved_bound:                 -1
% 19.42/3.00  bmc1_unsat_core_size:                   -1
% 19.42/3.00  bmc1_unsat_core_parents_size:           -1
% 19.42/3.00  bmc1_merge_next_fun:                    0
% 19.42/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.42/3.00  
% 19.42/3.00  ------ Instantiation
% 19.42/3.00  
% 19.42/3.00  inst_num_of_clauses:                    2440
% 19.42/3.00  inst_num_in_passive:                    1217
% 19.42/3.00  inst_num_in_active:                     474
% 19.42/3.00  inst_num_in_unprocessed:                750
% 19.42/3.00  inst_num_of_loops:                      530
% 19.42/3.00  inst_num_of_learning_restarts:          0
% 19.42/3.00  inst_num_moves_active_passive:          54
% 19.42/3.00  inst_lit_activity:                      0
% 19.42/3.00  inst_lit_activity_moves:                0
% 19.42/3.00  inst_num_tautologies:                   0
% 19.42/3.00  inst_num_prop_implied:                  0
% 19.42/3.00  inst_num_existing_simplified:           0
% 19.42/3.00  inst_num_eq_res_simplified:             0
% 19.42/3.00  inst_num_child_elim:                    0
% 19.42/3.00  inst_num_of_dismatching_blockings:      2106
% 19.42/3.00  inst_num_of_non_proper_insts:           2136
% 19.42/3.00  inst_num_of_duplicates:                 0
% 19.42/3.00  inst_inst_num_from_inst_to_res:         0
% 19.42/3.00  inst_dismatching_checking_time:         0.
% 19.42/3.00  
% 19.42/3.00  ------ Resolution
% 19.42/3.00  
% 19.42/3.00  res_num_of_clauses:                     0
% 19.42/3.00  res_num_in_passive:                     0
% 19.42/3.00  res_num_in_active:                      0
% 19.42/3.00  res_num_of_loops:                       82
% 19.42/3.00  res_forward_subset_subsumed:            528
% 19.42/3.00  res_backward_subset_subsumed:           2
% 19.42/3.00  res_forward_subsumed:                   0
% 19.42/3.00  res_backward_subsumed:                  0
% 19.42/3.00  res_forward_subsumption_resolution:     0
% 19.42/3.00  res_backward_subsumption_resolution:    0
% 19.42/3.00  res_clause_to_clause_subsumption:       167228
% 19.42/3.00  res_orphan_elimination:                 0
% 19.42/3.00  res_tautology_del:                      65
% 19.42/3.00  res_num_eq_res_simplified:              0
% 19.42/3.00  res_num_sel_changes:                    0
% 19.42/3.00  res_moves_from_active_to_pass:          0
% 19.42/3.00  
% 19.42/3.00  ------ Superposition
% 19.42/3.00  
% 19.42/3.00  sup_time_total:                         0.
% 19.42/3.01  sup_time_generating:                    0.
% 19.42/3.01  sup_time_sim_full:                      0.
% 19.42/3.01  sup_time_sim_immed:                     0.
% 19.42/3.01  
% 19.42/3.01  sup_num_of_clauses:                     3380
% 19.42/3.01  sup_num_in_active:                      96
% 19.42/3.01  sup_num_in_passive:                     3284
% 19.42/3.01  sup_num_of_loops:                       104
% 19.42/3.01  sup_fw_superposition:                   10935
% 19.42/3.01  sup_bw_superposition:                   8502
% 19.42/3.01  sup_immediate_simplified:               5830
% 19.42/3.01  sup_given_eliminated:                   3
% 19.42/3.01  comparisons_done:                       0
% 19.42/3.01  comparisons_avoided:                    6
% 19.42/3.01  
% 19.42/3.01  ------ Simplifications
% 19.42/3.01  
% 19.42/3.01  
% 19.42/3.01  sim_fw_subset_subsumed:                 0
% 19.42/3.01  sim_bw_subset_subsumed:                 0
% 19.42/3.01  sim_fw_subsumed:                        493
% 19.42/3.01  sim_bw_subsumed:                        12
% 19.42/3.01  sim_fw_subsumption_res:                 0
% 19.42/3.01  sim_bw_subsumption_res:                 0
% 19.42/3.01  sim_tautology_del:                      0
% 19.42/3.01  sim_eq_tautology_del:                   1017
% 19.42/3.01  sim_eq_res_simp:                        0
% 19.42/3.01  sim_fw_demodulated:                     3121
% 19.42/3.01  sim_bw_demodulated:                     251
% 19.42/3.01  sim_light_normalised:                   2315
% 19.42/3.01  sim_joinable_taut:                      419
% 19.42/3.01  sim_joinable_simp:                      0
% 19.42/3.01  sim_ac_normalised:                      0
% 19.42/3.01  sim_smt_subsumption:                    0
% 19.42/3.01  
%------------------------------------------------------------------------------
