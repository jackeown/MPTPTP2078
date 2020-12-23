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
% DateTime   : Thu Dec  3 11:58:11 EST 2020

% Result     : Theorem 11.45s
% Output     : CNFRefutation 11.45s
% Verified   : 
% Statistics : Number of formulae       :  110 (1555 expanded)
%              Number of clauses        :   55 ( 286 expanded)
%              Number of leaves         :   17 ( 356 expanded)
%              Depth                    :   22
%              Number of atoms          :  237 (4582 expanded)
%              Number of equality atoms :  197 (4416 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f39,f51,f51])).

fof(f63,plain,(
    ! [X1] : ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f30,f41,f34,f51])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f31,f41,f34,f50])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK5 != sK9
        | sK4 != sK8
        | sK3 != sK7
        | sK2 != sK6 )
      & k4_mcart_1(sK2,sK3,sK4,sK5) = k4_mcart_1(sK6,sK7,sK8,sK9) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( sK5 != sK9
      | sK4 != sK8
      | sK3 != sK7
      | sK2 != sK6 )
    & k4_mcart_1(sK2,sK3,sK4,sK5) = k4_mcart_1(sK6,sK7,sK8,sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f21,f28])).

fof(f48,plain,(
    k4_mcart_1(sK2,sK3,sK4,sK5) = k4_mcart_1(sK6,sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5) = k4_tarski(k4_tarski(k4_tarski(sK6,sK7),sK8),sK9) ),
    inference(definition_unfolding,[],[f48,f47,f47])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK0(X0,X1) != X1
        & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK0(X0,X1) != X1
              & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f42,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f42])).

fof(f67,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_mcart_1(k4_tarski(X4,X5)) = X4
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f66])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f38,f51])).

fof(f62,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f49,plain,
    ( sK5 != sK9
    | sK4 != sK8
    | sK3 != sK7
    | sK2 != sK6 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( r1_xboole_0(k2_tarski(X0,X1),X2)
    | r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_38923,plain,
    ( r1_xboole_0(k2_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_38924,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_39393,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X1,X1) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_39729,plain,
    ( r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38924,c_39393])).

cnf(c_39734,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_38923,c_39729])).

cnf(c_13,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5) = k4_tarski(k4_tarski(k4_tarski(sK6,sK7),sK8),sK9) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3396,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[status(thm)],[c_9])).

cnf(c_38890,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_3396])).

cnf(c_39050,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5)) = k4_tarski(k4_tarski(sK6,sK7),sK8) ),
    inference(superposition,[status(thm)],[c_13,c_38890])).

cnf(c_39051,plain,
    ( k4_tarski(k4_tarski(sK6,sK7),sK8) = k4_tarski(k4_tarski(sK2,sK3),sK4) ),
    inference(demodulation,[status(thm)],[c_39050,c_38890])).

cnf(c_39054,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(sK2,sK3),sK4)) = k4_tarski(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_39051,c_38890])).

cnf(c_39055,plain,
    ( k4_tarski(sK6,sK7) = k4_tarski(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_39054,c_38890])).

cnf(c_39128,plain,
    ( k1_mcart_1(k4_tarski(sK2,sK3)) = sK6 ),
    inference(superposition,[status(thm)],[c_39055,c_38890])).

cnf(c_39129,plain,
    ( sK6 = sK2 ),
    inference(demodulation,[status(thm)],[c_39128,c_38890])).

cnf(c_39215,plain,
    ( k4_tarski(sK2,sK7) = k4_tarski(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_39129,c_39055])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_38927,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_39963,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k2_tarski(X2,X2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38927,c_39393])).

cnf(c_39971,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(X0,k2_tarski(sK7,sK7))) = iProver_top
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_39215,c_39963])).

cnf(c_39053,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK9) = k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5) ),
    inference(demodulation,[status(thm)],[c_39051,c_13])).

cnf(c_3,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
    | X3 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38926,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_39824,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,k2_tarski(X1,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38926,c_39393])).

cnf(c_39828,plain,
    ( sK9 = X0
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5),k2_zfmisc_1(X1,k2_tarski(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39053,c_39824])).

cnf(c_39974,plain,
    ( sK9 = sK5
    | r2_hidden(k4_tarski(k4_tarski(sK2,sK3),sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_39963,c_39828])).

cnf(c_40353,plain,
    ( sK9 = sK5 ),
    inference(superposition,[status(thm)],[c_39734,c_39974])).

cnf(c_12,negated_conjecture,
    ( sK2 != sK6
    | sK3 != sK7
    | sK4 != sK8
    | sK5 != sK9 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_93,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_114,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_94,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_648,plain,
    ( sK6 != X0
    | sK2 != X0
    | sK2 = sK6 ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_649,plain,
    ( sK6 != sK2
    | sK2 = sK6
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_3419,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5)) = k4_tarski(k4_tarski(sK6,sK7),sK8) ),
    inference(superposition,[status(thm)],[c_13,c_3396])).

cnf(c_3420,plain,
    ( k4_tarski(k4_tarski(sK6,sK7),sK8) = k4_tarski(k4_tarski(sK2,sK3),sK4) ),
    inference(demodulation,[status(thm)],[c_3419,c_3396])).

cnf(c_4215,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(sK2,sK3),sK4)) = k4_tarski(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_3420,c_3396])).

cnf(c_4216,plain,
    ( k4_tarski(sK6,sK7) = k4_tarski(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_4215,c_3396])).

cnf(c_5521,plain,
    ( k1_mcart_1(k4_tarski(sK2,sK3)) = sK6 ),
    inference(superposition,[status(thm)],[c_4216,c_3396])).

cnf(c_5523,plain,
    ( sK6 = sK2 ),
    inference(demodulation,[status(thm)],[c_5521,c_3396])).

cnf(c_31401,negated_conjecture,
    ( sK3 != sK7
    | sK4 != sK8
    | sK5 != sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_114,c_649,c_5523])).

cnf(c_38902,negated_conjecture,
    ( sK3 != sK7
    | sK4 != sK8
    | sK5 != sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_114,c_649,c_5523])).

cnf(c_40486,plain,
    ( sK7 != sK3
    | sK8 != sK4
    | sK5 != sK5 ),
    inference(demodulation,[status(thm)],[c_40353,c_38902])).

cnf(c_40487,plain,
    ( sK7 != sK3
    | sK8 != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_40486])).

cnf(c_39127,plain,
    ( k4_tarski(k4_tarski(sK2,sK3),sK8) = k4_tarski(k4_tarski(sK2,sK3),sK4) ),
    inference(demodulation,[status(thm)],[c_39055,c_39051])).

cnf(c_39829,plain,
    ( sK8 = X0
    | r2_hidden(k4_tarski(k4_tarski(sK2,sK3),sK4),k2_zfmisc_1(X1,k2_tarski(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39127,c_39824])).

cnf(c_39975,plain,
    ( sK8 = sK4
    | r2_hidden(k4_tarski(sK2,sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_39963,c_39829])).

cnf(c_40575,plain,
    ( sK8 = sK4 ),
    inference(superposition,[status(thm)],[c_39734,c_39975])).

cnf(c_39830,plain,
    ( sK7 = X0
    | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(X1,k2_tarski(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39215,c_39824])).

cnf(c_40803,plain,
    ( sK7 = sK3
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_39963,c_39830])).

cnf(c_41214,plain,
    ( r2_hidden(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39971,c_40487,c_40575,c_40803])).

cnf(c_41221,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_39734,c_41214])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:43:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.45/1.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.45/1.94  
% 11.45/1.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.45/1.94  
% 11.45/1.94  ------  iProver source info
% 11.45/1.94  
% 11.45/1.94  git: date: 2020-06-30 10:37:57 +0100
% 11.45/1.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.45/1.94  git: non_committed_changes: false
% 11.45/1.94  git: last_make_outside_of_git: false
% 11.45/1.94  
% 11.45/1.94  ------ 
% 11.45/1.94  ------ Parsing...
% 11.45/1.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  ------ Proving...
% 11.45/1.94  ------ Problem Properties 
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  clauses                                 14
% 11.45/1.94  conjectures                             2
% 11.45/1.94  EPR                                     1
% 11.45/1.94  Horn                                    12
% 11.45/1.94  unary                                   4
% 11.45/1.94  binary                                  8
% 11.45/1.94  lits                                    27
% 11.45/1.94  lits eq                                 15
% 11.45/1.94  fd_pure                                 0
% 11.45/1.94  fd_pseudo                               0
% 11.45/1.94  fd_cond                                 0
% 11.45/1.94  fd_pseudo_cond                          4
% 11.45/1.94  AC symbols                              0
% 11.45/1.94  
% 11.45/1.94  ------ Input Options Time Limit: Unbounded
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.45/1.94  Current options:
% 11.45/1.94  ------ 
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.45/1.94  
% 11.45/1.94  ------ Proving...
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  % SZS status Theorem for theBenchmark.p
% 11.45/1.94  
% 11.45/1.94   Resolution empty clause
% 11.45/1.94  
% 11.45/1.94  % SZS output start CNFRefutation for theBenchmark.p
% 11.45/1.94  
% 11.45/1.94  fof(f9,axiom,(
% 11.45/1.94    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f18,plain,(
% 11.45/1.94    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 11.45/1.94    inference(ennf_transformation,[],[f9])).
% 11.45/1.94  
% 11.45/1.94  fof(f40,plain,(
% 11.45/1.94    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 11.45/1.94    inference(cnf_transformation,[],[f18])).
% 11.45/1.94  
% 11.45/1.94  fof(f8,axiom,(
% 11.45/1.94    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f17,plain,(
% 11.45/1.94    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 11.45/1.94    inference(ennf_transformation,[],[f8])).
% 11.45/1.94  
% 11.45/1.94  fof(f39,plain,(
% 11.45/1.94    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 11.45/1.94    inference(cnf_transformation,[],[f17])).
% 11.45/1.94  
% 11.45/1.94  fof(f3,axiom,(
% 11.45/1.94    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f32,plain,(
% 11.45/1.94    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 11.45/1.94    inference(cnf_transformation,[],[f3])).
% 11.45/1.94  
% 11.45/1.94  fof(f4,axiom,(
% 11.45/1.94    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f33,plain,(
% 11.45/1.94    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 11.45/1.94    inference(cnf_transformation,[],[f4])).
% 11.45/1.94  
% 11.45/1.94  fof(f5,axiom,(
% 11.45/1.94    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f34,plain,(
% 11.45/1.94    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.45/1.94    inference(cnf_transformation,[],[f5])).
% 11.45/1.94  
% 11.45/1.94  fof(f50,plain,(
% 11.45/1.94    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 11.45/1.94    inference(definition_unfolding,[],[f33,f34])).
% 11.45/1.94  
% 11.45/1.94  fof(f51,plain,(
% 11.45/1.94    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.45/1.94    inference(definition_unfolding,[],[f32,f50])).
% 11.45/1.94  
% 11.45/1.94  fof(f58,plain,(
% 11.45/1.94    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 11.45/1.94    inference(definition_unfolding,[],[f39,f51,f51])).
% 11.45/1.94  
% 11.45/1.94  fof(f63,plain,(
% 11.45/1.94    ( ! [X1] : (~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 11.45/1.94    inference(equality_resolution,[],[f58])).
% 11.45/1.94  
% 11.45/1.94  fof(f6,axiom,(
% 11.45/1.94    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f35,plain,(
% 11.45/1.94    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.45/1.94    inference(cnf_transformation,[],[f6])).
% 11.45/1.94  
% 11.45/1.94  fof(f1,axiom,(
% 11.45/1.94    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f30,plain,(
% 11.45/1.94    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 11.45/1.94    inference(cnf_transformation,[],[f1])).
% 11.45/1.94  
% 11.45/1.94  fof(f10,axiom,(
% 11.45/1.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f41,plain,(
% 11.45/1.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.45/1.94    inference(cnf_transformation,[],[f10])).
% 11.45/1.94  
% 11.45/1.94  fof(f52,plain,(
% 11.45/1.94    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)))) )),
% 11.45/1.94    inference(definition_unfolding,[],[f30,f41,f34,f51])).
% 11.45/1.94  
% 11.45/1.94  fof(f53,plain,(
% 11.45/1.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 11.45/1.94    inference(definition_unfolding,[],[f35,f52])).
% 11.45/1.94  
% 11.45/1.94  fof(f2,axiom,(
% 11.45/1.94    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f31,plain,(
% 11.45/1.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 11.45/1.94    inference(cnf_transformation,[],[f2])).
% 11.45/1.94  
% 11.45/1.94  fof(f54,plain,(
% 11.45/1.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7)))) )),
% 11.45/1.94    inference(definition_unfolding,[],[f31,f41,f34,f50])).
% 11.45/1.94  
% 11.45/1.94  fof(f14,conjecture,(
% 11.45/1.94    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f15,negated_conjecture,(
% 11.45/1.94    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 11.45/1.94    inference(negated_conjecture,[],[f14])).
% 11.45/1.94  
% 11.45/1.94  fof(f21,plain,(
% 11.45/1.94    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 11.45/1.94    inference(ennf_transformation,[],[f15])).
% 11.45/1.94  
% 11.45/1.94  fof(f28,plain,(
% 11.45/1.94    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK5 != sK9 | sK4 != sK8 | sK3 != sK7 | sK2 != sK6) & k4_mcart_1(sK2,sK3,sK4,sK5) = k4_mcart_1(sK6,sK7,sK8,sK9))),
% 11.45/1.94    introduced(choice_axiom,[])).
% 11.45/1.94  
% 11.45/1.94  fof(f29,plain,(
% 11.45/1.94    (sK5 != sK9 | sK4 != sK8 | sK3 != sK7 | sK2 != sK6) & k4_mcart_1(sK2,sK3,sK4,sK5) = k4_mcart_1(sK6,sK7,sK8,sK9)),
% 11.45/1.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f21,f28])).
% 11.45/1.94  
% 11.45/1.94  fof(f48,plain,(
% 11.45/1.94    k4_mcart_1(sK2,sK3,sK4,sK5) = k4_mcart_1(sK6,sK7,sK8,sK9)),
% 11.45/1.94    inference(cnf_transformation,[],[f29])).
% 11.45/1.94  
% 11.45/1.94  fof(f13,axiom,(
% 11.45/1.94    ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f47,plain,(
% 11.45/1.94    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 11.45/1.94    inference(cnf_transformation,[],[f13])).
% 11.45/1.94  
% 11.45/1.94  fof(f61,plain,(
% 11.45/1.94    k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5) = k4_tarski(k4_tarski(k4_tarski(sK6,sK7),sK8),sK9)),
% 11.45/1.94    inference(definition_unfolding,[],[f48,f47,f47])).
% 11.45/1.94  
% 11.45/1.94  fof(f11,axiom,(
% 11.45/1.94    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k1_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X2)))),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f16,plain,(
% 11.45/1.94    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X4)))),
% 11.45/1.94    inference(rectify,[],[f11])).
% 11.45/1.94  
% 11.45/1.94  fof(f19,plain,(
% 11.45/1.94    ! [X0] : (! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 11.45/1.94    inference(ennf_transformation,[],[f16])).
% 11.45/1.94  
% 11.45/1.94  fof(f24,plain,(
% 11.45/1.94    ! [X0] : (! [X3] : ((k1_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X4 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 11.45/1.94    inference(nnf_transformation,[],[f19])).
% 11.45/1.94  
% 11.45/1.94  fof(f25,plain,(
% 11.45/1.94    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 11.45/1.94    inference(rectify,[],[f24])).
% 11.45/1.94  
% 11.45/1.94  fof(f26,plain,(
% 11.45/1.94    ! [X1,X0] : (? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0) => (sK0(X0,X1) != X1 & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0))),
% 11.45/1.94    introduced(choice_axiom,[])).
% 11.45/1.94  
% 11.45/1.94  fof(f27,plain,(
% 11.45/1.94    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | (sK0(X0,X1) != X1 & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 11.45/1.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 11.45/1.94  
% 11.45/1.94  fof(f42,plain,(
% 11.45/1.94    ( ! [X6,X4,X0,X7,X5,X1] : (X1 = X4 | k4_tarski(X4,X5) != X0 | k1_mcart_1(X0) != X1 | k4_tarski(X6,X7) != X0) )),
% 11.45/1.94    inference(cnf_transformation,[],[f27])).
% 11.45/1.94  
% 11.45/1.94  fof(f66,plain,(
% 11.45/1.94    ( ! [X6,X4,X7,X5,X1] : (X1 = X4 | k1_mcart_1(k4_tarski(X4,X5)) != X1 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 11.45/1.94    inference(equality_resolution,[],[f42])).
% 11.45/1.94  
% 11.45/1.94  fof(f67,plain,(
% 11.45/1.94    ( ! [X6,X4,X7,X5] : (k1_mcart_1(k4_tarski(X4,X5)) = X4 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 11.45/1.94    inference(equality_resolution,[],[f66])).
% 11.45/1.94  
% 11.45/1.94  fof(f7,axiom,(
% 11.45/1.94    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 11.45/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.45/1.94  
% 11.45/1.94  fof(f22,plain,(
% 11.45/1.94    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 11.45/1.94    inference(nnf_transformation,[],[f7])).
% 11.45/1.94  
% 11.45/1.94  fof(f23,plain,(
% 11.45/1.94    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 11.45/1.94    inference(flattening,[],[f22])).
% 11.45/1.94  
% 11.45/1.94  fof(f38,plain,(
% 11.45/1.94    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 11.45/1.94    inference(cnf_transformation,[],[f23])).
% 11.45/1.94  
% 11.45/1.94  fof(f55,plain,(
% 11.45/1.94    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 11.45/1.94    inference(definition_unfolding,[],[f38,f51])).
% 11.45/1.94  
% 11.45/1.94  fof(f62,plain,(
% 11.45/1.94    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 11.45/1.94    inference(equality_resolution,[],[f55])).
% 11.45/1.94  
% 11.45/1.94  fof(f37,plain,(
% 11.45/1.94    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 11.45/1.94    inference(cnf_transformation,[],[f23])).
% 11.45/1.94  
% 11.45/1.94  fof(f56,plain,(
% 11.45/1.94    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))) )),
% 11.45/1.94    inference(definition_unfolding,[],[f37,f51])).
% 11.45/1.94  
% 11.45/1.94  fof(f49,plain,(
% 11.45/1.94    sK5 != sK9 | sK4 != sK8 | sK3 != sK7 | sK2 != sK6),
% 11.45/1.94    inference(cnf_transformation,[],[f29])).
% 11.45/1.94  
% 11.45/1.94  cnf(c_6,plain,
% 11.45/1.94      ( r1_xboole_0(k2_tarski(X0,X1),X2)
% 11.45/1.94      | r2_hidden(X0,X2)
% 11.45/1.94      | r2_hidden(X1,X2) ),
% 11.45/1.94      inference(cnf_transformation,[],[f40]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_38923,plain,
% 11.45/1.94      ( r1_xboole_0(k2_tarski(X0,X1),X2) = iProver_top
% 11.45/1.94      | r2_hidden(X0,X2) = iProver_top
% 11.45/1.94      | r2_hidden(X1,X2) = iProver_top ),
% 11.45/1.94      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_5,plain,
% 11.45/1.94      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 11.45/1.94      inference(cnf_transformation,[],[f63]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_38924,plain,
% 11.45/1.94      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 11.45/1.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_0,plain,
% 11.45/1.94      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k2_tarski(X0,X1) ),
% 11.45/1.94      inference(cnf_transformation,[],[f53]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_1,plain,
% 11.45/1.94      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 11.45/1.94      inference(cnf_transformation,[],[f54]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39393,plain,
% 11.45/1.94      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X1,X1) = k2_tarski(X0,X1) ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39729,plain,
% 11.45/1.94      ( r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) != iProver_top ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_38924,c_39393]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39734,plain,
% 11.45/1.94      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_38923,c_39729]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_13,negated_conjecture,
% 11.45/1.94      ( k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5) = k4_tarski(k4_tarski(k4_tarski(sK6,sK7),sK8),sK9) ),
% 11.45/1.94      inference(cnf_transformation,[],[f61]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_9,plain,
% 11.45/1.94      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
% 11.45/1.94      | k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 11.45/1.94      inference(cnf_transformation,[],[f67]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_3396,plain,
% 11.45/1.94      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 11.45/1.94      inference(equality_resolution,[status(thm)],[c_9]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_38890,plain,
% 11.45/1.94      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 11.45/1.94      inference(global_propositional_subsumption,[status(thm)],[c_9,c_3396]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39050,plain,
% 11.45/1.94      ( k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5)) = k4_tarski(k4_tarski(sK6,sK7),sK8) ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_13,c_38890]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39051,plain,
% 11.45/1.94      ( k4_tarski(k4_tarski(sK6,sK7),sK8) = k4_tarski(k4_tarski(sK2,sK3),sK4) ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_39050,c_38890]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39054,plain,
% 11.45/1.94      ( k1_mcart_1(k4_tarski(k4_tarski(sK2,sK3),sK4)) = k4_tarski(sK6,sK7) ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39051,c_38890]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39055,plain,
% 11.45/1.94      ( k4_tarski(sK6,sK7) = k4_tarski(sK2,sK3) ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_39054,c_38890]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39128,plain,
% 11.45/1.94      ( k1_mcart_1(k4_tarski(sK2,sK3)) = sK6 ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39055,c_38890]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39129,plain,
% 11.45/1.94      ( sK6 = sK2 ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_39128,c_38890]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39215,plain,
% 11.45/1.94      ( k4_tarski(sK2,sK7) = k4_tarski(sK2,sK3) ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_39129,c_39055]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_2,plain,
% 11.45/1.94      ( ~ r2_hidden(X0,X1)
% 11.45/1.94      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
% 11.45/1.94      inference(cnf_transformation,[],[f62]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_38927,plain,
% 11.45/1.94      ( r2_hidden(X0,X1) != iProver_top
% 11.45/1.94      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) = iProver_top ),
% 11.45/1.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39963,plain,
% 11.45/1.94      ( r2_hidden(X0,X1) != iProver_top
% 11.45/1.94      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k2_tarski(X2,X2))) = iProver_top ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_38927,c_39393]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39971,plain,
% 11.45/1.94      ( r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(X0,k2_tarski(sK7,sK7))) = iProver_top
% 11.45/1.94      | r2_hidden(sK2,X0) != iProver_top ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39215,c_39963]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39053,plain,
% 11.45/1.94      ( k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK9) = k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5) ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_39051,c_13]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_3,plain,
% 11.45/1.94      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
% 11.45/1.94      | X3 = X1 ),
% 11.45/1.94      inference(cnf_transformation,[],[f56]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_38926,plain,
% 11.45/1.94      ( X0 = X1
% 11.45/1.94      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 11.45/1.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39824,plain,
% 11.45/1.94      ( X0 = X1
% 11.45/1.94      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,k2_tarski(X1,X1))) != iProver_top ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_38926,c_39393]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39828,plain,
% 11.45/1.94      ( sK9 = X0
% 11.45/1.94      | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5),k2_zfmisc_1(X1,k2_tarski(X0,X0))) != iProver_top ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39053,c_39824]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39974,plain,
% 11.45/1.94      ( sK9 = sK5
% 11.45/1.94      | r2_hidden(k4_tarski(k4_tarski(sK2,sK3),sK4),X0) != iProver_top ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39963,c_39828]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_40353,plain,
% 11.45/1.94      ( sK9 = sK5 ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39734,c_39974]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_12,negated_conjecture,
% 11.45/1.94      ( sK2 != sK6 | sK3 != sK7 | sK4 != sK8 | sK5 != sK9 ),
% 11.45/1.94      inference(cnf_transformation,[],[f49]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_93,plain,( X0 = X0 ),theory(equality) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_114,plain,
% 11.45/1.94      ( sK2 = sK2 ),
% 11.45/1.94      inference(instantiation,[status(thm)],[c_93]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_94,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_648,plain,
% 11.45/1.94      ( sK6 != X0 | sK2 != X0 | sK2 = sK6 ),
% 11.45/1.94      inference(instantiation,[status(thm)],[c_94]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_649,plain,
% 11.45/1.94      ( sK6 != sK2 | sK2 = sK6 | sK2 != sK2 ),
% 11.45/1.94      inference(instantiation,[status(thm)],[c_648]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_3419,plain,
% 11.45/1.94      ( k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK2,sK3),sK4),sK5)) = k4_tarski(k4_tarski(sK6,sK7),sK8) ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_13,c_3396]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_3420,plain,
% 11.45/1.94      ( k4_tarski(k4_tarski(sK6,sK7),sK8) = k4_tarski(k4_tarski(sK2,sK3),sK4) ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_3419,c_3396]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_4215,plain,
% 11.45/1.94      ( k1_mcart_1(k4_tarski(k4_tarski(sK2,sK3),sK4)) = k4_tarski(sK6,sK7) ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_3420,c_3396]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_4216,plain,
% 11.45/1.94      ( k4_tarski(sK6,sK7) = k4_tarski(sK2,sK3) ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_4215,c_3396]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_5521,plain,
% 11.45/1.94      ( k1_mcart_1(k4_tarski(sK2,sK3)) = sK6 ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_4216,c_3396]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_5523,plain,
% 11.45/1.94      ( sK6 = sK2 ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_5521,c_3396]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_31401,negated_conjecture,
% 11.45/1.94      ( sK3 != sK7 | sK4 != sK8 | sK5 != sK9 ),
% 11.45/1.94      inference(global_propositional_subsumption,
% 11.45/1.94                [status(thm)],
% 11.45/1.94                [c_12,c_114,c_649,c_5523]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_38902,negated_conjecture,
% 11.45/1.94      ( sK3 != sK7 | sK4 != sK8 | sK5 != sK9 ),
% 11.45/1.94      inference(global_propositional_subsumption,
% 11.45/1.94                [status(thm)],
% 11.45/1.94                [c_12,c_114,c_649,c_5523]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_40486,plain,
% 11.45/1.94      ( sK7 != sK3 | sK8 != sK4 | sK5 != sK5 ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_40353,c_38902]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_40487,plain,
% 11.45/1.94      ( sK7 != sK3 | sK8 != sK4 ),
% 11.45/1.94      inference(equality_resolution_simp,[status(thm)],[c_40486]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39127,plain,
% 11.45/1.94      ( k4_tarski(k4_tarski(sK2,sK3),sK8) = k4_tarski(k4_tarski(sK2,sK3),sK4) ),
% 11.45/1.94      inference(demodulation,[status(thm)],[c_39055,c_39051]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39829,plain,
% 11.45/1.94      ( sK8 = X0
% 11.45/1.94      | r2_hidden(k4_tarski(k4_tarski(sK2,sK3),sK4),k2_zfmisc_1(X1,k2_tarski(X0,X0))) != iProver_top ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39127,c_39824]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39975,plain,
% 11.45/1.94      ( sK8 = sK4 | r2_hidden(k4_tarski(sK2,sK3),X0) != iProver_top ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39963,c_39829]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_40575,plain,
% 11.45/1.94      ( sK8 = sK4 ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39734,c_39975]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_39830,plain,
% 11.45/1.94      ( sK7 = X0
% 11.45/1.94      | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(X1,k2_tarski(X0,X0))) != iProver_top ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39215,c_39824]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_40803,plain,
% 11.45/1.94      ( sK7 = sK3 | r2_hidden(sK2,X0) != iProver_top ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39963,c_39830]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_41214,plain,
% 11.45/1.94      ( r2_hidden(sK2,X0) != iProver_top ),
% 11.45/1.94      inference(global_propositional_subsumption,
% 11.45/1.94                [status(thm)],
% 11.45/1.94                [c_39971,c_40487,c_40575,c_40803]) ).
% 11.45/1.94  
% 11.45/1.94  cnf(c_41221,plain,
% 11.45/1.94      ( $false ),
% 11.45/1.94      inference(superposition,[status(thm)],[c_39734,c_41214]) ).
% 11.45/1.94  
% 11.45/1.94  
% 11.45/1.94  % SZS output end CNFRefutation for theBenchmark.p
% 11.45/1.94  
% 11.45/1.94  ------                               Statistics
% 11.45/1.94  
% 11.45/1.94  ------ Selected
% 11.45/1.94  
% 11.45/1.94  total_time:                             1.061
% 11.45/1.94  
%------------------------------------------------------------------------------
