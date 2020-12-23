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
% DateTime   : Thu Dec  3 11:29:52 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 337 expanded)
%              Number of clauses        :   35 (  62 expanded)
%              Number of leaves         :   18 (  97 expanded)
%              Depth                    :   19
%              Number of atoms          :  264 ( 609 expanded)
%              Number of equality atoms :  198 ( 495 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f23])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f88,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f89,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f88])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( sK2 != sK3
    & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f34])).

fof(f63,plain,(
    k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f87,plain,(
    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f63,f40,f66,f66,f66])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f42,f59,f66])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f97,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f95,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f83])).

fof(f96,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f95])).

fof(f64,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_895,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1243,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_21,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1244,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_21,c_0])).

cnf(c_1256,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_1243,c_1244])).

cnf(c_4,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_900,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2000,plain,
    ( r1_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_900])).

cnf(c_2027,plain,
    ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2000,c_3])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_901,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3181,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2027,c_901])).

cnf(c_3212,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3181,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3214,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_3212,c_5])).

cnf(c_3215,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3214,c_3181])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1771,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK3,sK3,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1256,c_1])).

cnf(c_3275,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0) = k2_enumset1(sK3,sK3,sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_3215,c_1771])).

cnf(c_3523,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_3275,c_5])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_888,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4387,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3523,c_888])).

cnf(c_5575,plain,
    ( sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_895,c_4387])).

cnf(c_650,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1018,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_1019,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_28,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_20,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5575,c_1019,c_28,c_25,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.69/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/0.98  
% 2.69/0.98  ------  iProver source info
% 2.69/0.98  
% 2.69/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.69/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/0.98  git: non_committed_changes: false
% 2.69/0.98  git: last_make_outside_of_git: false
% 2.69/0.98  
% 2.69/0.98  ------ 
% 2.69/0.98  
% 2.69/0.98  ------ Input Options
% 2.69/0.98  
% 2.69/0.98  --out_options                           all
% 2.69/0.98  --tptp_safe_out                         true
% 2.69/0.98  --problem_path                          ""
% 2.69/0.98  --include_path                          ""
% 2.69/0.98  --clausifier                            res/vclausify_rel
% 2.69/0.98  --clausifier_options                    --mode clausify
% 2.69/0.98  --stdin                                 false
% 2.69/0.98  --stats_out                             all
% 2.69/0.98  
% 2.69/0.98  ------ General Options
% 2.69/0.98  
% 2.69/0.98  --fof                                   false
% 2.69/0.98  --time_out_real                         305.
% 2.69/0.98  --time_out_virtual                      -1.
% 2.69/0.98  --symbol_type_check                     false
% 2.69/0.98  --clausify_out                          false
% 2.69/0.98  --sig_cnt_out                           false
% 2.69/0.99  --trig_cnt_out                          false
% 2.69/0.99  --trig_cnt_out_tolerance                1.
% 2.69/0.99  --trig_cnt_out_sk_spl                   false
% 2.69/0.99  --abstr_cl_out                          false
% 2.69/0.99  
% 2.69/0.99  ------ Global Options
% 2.69/0.99  
% 2.69/0.99  --schedule                              default
% 2.69/0.99  --add_important_lit                     false
% 2.69/0.99  --prop_solver_per_cl                    1000
% 2.69/0.99  --min_unsat_core                        false
% 2.69/0.99  --soft_assumptions                      false
% 2.69/0.99  --soft_lemma_size                       3
% 2.69/0.99  --prop_impl_unit_size                   0
% 2.69/0.99  --prop_impl_unit                        []
% 2.69/0.99  --share_sel_clauses                     true
% 2.69/0.99  --reset_solvers                         false
% 2.69/0.99  --bc_imp_inh                            [conj_cone]
% 2.69/0.99  --conj_cone_tolerance                   3.
% 2.69/0.99  --extra_neg_conj                        none
% 2.69/0.99  --large_theory_mode                     true
% 2.69/0.99  --prolific_symb_bound                   200
% 2.69/0.99  --lt_threshold                          2000
% 2.69/0.99  --clause_weak_htbl                      true
% 2.69/0.99  --gc_record_bc_elim                     false
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing Options
% 2.69/0.99  
% 2.69/0.99  --preprocessing_flag                    true
% 2.69/0.99  --time_out_prep_mult                    0.1
% 2.69/0.99  --splitting_mode                        input
% 2.69/0.99  --splitting_grd                         true
% 2.69/0.99  --splitting_cvd                         false
% 2.69/0.99  --splitting_cvd_svl                     false
% 2.69/0.99  --splitting_nvd                         32
% 2.69/0.99  --sub_typing                            true
% 2.69/0.99  --prep_gs_sim                           true
% 2.69/0.99  --prep_unflatten                        true
% 2.69/0.99  --prep_res_sim                          true
% 2.69/0.99  --prep_upred                            true
% 2.69/0.99  --prep_sem_filter                       exhaustive
% 2.69/0.99  --prep_sem_filter_out                   false
% 2.69/0.99  --pred_elim                             true
% 2.69/0.99  --res_sim_input                         true
% 2.69/0.99  --eq_ax_congr_red                       true
% 2.69/0.99  --pure_diseq_elim                       true
% 2.69/0.99  --brand_transform                       false
% 2.69/0.99  --non_eq_to_eq                          false
% 2.69/0.99  --prep_def_merge                        true
% 2.69/0.99  --prep_def_merge_prop_impl              false
% 2.69/0.99  --prep_def_merge_mbd                    true
% 2.69/0.99  --prep_def_merge_tr_red                 false
% 2.69/0.99  --prep_def_merge_tr_cl                  false
% 2.69/0.99  --smt_preprocessing                     true
% 2.69/0.99  --smt_ac_axioms                         fast
% 2.69/0.99  --preprocessed_out                      false
% 2.69/0.99  --preprocessed_stats                    false
% 2.69/0.99  
% 2.69/0.99  ------ Abstraction refinement Options
% 2.69/0.99  
% 2.69/0.99  --abstr_ref                             []
% 2.69/0.99  --abstr_ref_prep                        false
% 2.69/0.99  --abstr_ref_until_sat                   false
% 2.69/0.99  --abstr_ref_sig_restrict                funpre
% 2.69/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.99  --abstr_ref_under                       []
% 2.69/0.99  
% 2.69/0.99  ------ SAT Options
% 2.69/0.99  
% 2.69/0.99  --sat_mode                              false
% 2.69/0.99  --sat_fm_restart_options                ""
% 2.69/0.99  --sat_gr_def                            false
% 2.69/0.99  --sat_epr_types                         true
% 2.69/0.99  --sat_non_cyclic_types                  false
% 2.69/0.99  --sat_finite_models                     false
% 2.69/0.99  --sat_fm_lemmas                         false
% 2.69/0.99  --sat_fm_prep                           false
% 2.69/0.99  --sat_fm_uc_incr                        true
% 2.69/0.99  --sat_out_model                         small
% 2.69/0.99  --sat_out_clauses                       false
% 2.69/0.99  
% 2.69/0.99  ------ QBF Options
% 2.69/0.99  
% 2.69/0.99  --qbf_mode                              false
% 2.69/0.99  --qbf_elim_univ                         false
% 2.69/0.99  --qbf_dom_inst                          none
% 2.69/0.99  --qbf_dom_pre_inst                      false
% 2.69/0.99  --qbf_sk_in                             false
% 2.69/0.99  --qbf_pred_elim                         true
% 2.69/0.99  --qbf_split                             512
% 2.69/0.99  
% 2.69/0.99  ------ BMC1 Options
% 2.69/0.99  
% 2.69/0.99  --bmc1_incremental                      false
% 2.69/0.99  --bmc1_axioms                           reachable_all
% 2.69/0.99  --bmc1_min_bound                        0
% 2.69/0.99  --bmc1_max_bound                        -1
% 2.69/0.99  --bmc1_max_bound_default                -1
% 2.69/0.99  --bmc1_symbol_reachability              true
% 2.69/0.99  --bmc1_property_lemmas                  false
% 2.69/0.99  --bmc1_k_induction                      false
% 2.69/0.99  --bmc1_non_equiv_states                 false
% 2.69/0.99  --bmc1_deadlock                         false
% 2.69/0.99  --bmc1_ucm                              false
% 2.69/0.99  --bmc1_add_unsat_core                   none
% 2.69/0.99  --bmc1_unsat_core_children              false
% 2.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.99  --bmc1_out_stat                         full
% 2.69/0.99  --bmc1_ground_init                      false
% 2.69/0.99  --bmc1_pre_inst_next_state              false
% 2.69/0.99  --bmc1_pre_inst_state                   false
% 2.69/0.99  --bmc1_pre_inst_reach_state             false
% 2.69/0.99  --bmc1_out_unsat_core                   false
% 2.69/0.99  --bmc1_aig_witness_out                  false
% 2.69/0.99  --bmc1_verbose                          false
% 2.69/0.99  --bmc1_dump_clauses_tptp                false
% 2.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.99  --bmc1_dump_file                        -
% 2.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.99  --bmc1_ucm_extend_mode                  1
% 2.69/0.99  --bmc1_ucm_init_mode                    2
% 2.69/0.99  --bmc1_ucm_cone_mode                    none
% 2.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.99  --bmc1_ucm_relax_model                  4
% 2.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.99  --bmc1_ucm_layered_model                none
% 2.69/0.99  --bmc1_ucm_max_lemma_size               10
% 2.69/0.99  
% 2.69/0.99  ------ AIG Options
% 2.69/0.99  
% 2.69/0.99  --aig_mode                              false
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation Options
% 2.69/0.99  
% 2.69/0.99  --instantiation_flag                    true
% 2.69/0.99  --inst_sos_flag                         false
% 2.69/0.99  --inst_sos_phase                        true
% 2.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel_side                     num_symb
% 2.69/0.99  --inst_solver_per_active                1400
% 2.69/0.99  --inst_solver_calls_frac                1.
% 2.69/0.99  --inst_passive_queue_type               priority_queues
% 2.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.99  --inst_passive_queues_freq              [25;2]
% 2.69/0.99  --inst_dismatching                      true
% 2.69/0.99  --inst_eager_unprocessed_to_passive     true
% 2.69/0.99  --inst_prop_sim_given                   true
% 2.69/0.99  --inst_prop_sim_new                     false
% 2.69/0.99  --inst_subs_new                         false
% 2.69/0.99  --inst_eq_res_simp                      false
% 2.69/0.99  --inst_subs_given                       false
% 2.69/0.99  --inst_orphan_elimination               true
% 2.69/0.99  --inst_learning_loop_flag               true
% 2.69/0.99  --inst_learning_start                   3000
% 2.69/0.99  --inst_learning_factor                  2
% 2.69/0.99  --inst_start_prop_sim_after_learn       3
% 2.69/0.99  --inst_sel_renew                        solver
% 2.69/0.99  --inst_lit_activity_flag                true
% 2.69/0.99  --inst_restr_to_given                   false
% 2.69/0.99  --inst_activity_threshold               500
% 2.69/0.99  --inst_out_proof                        true
% 2.69/0.99  
% 2.69/0.99  ------ Resolution Options
% 2.69/0.99  
% 2.69/0.99  --resolution_flag                       true
% 2.69/0.99  --res_lit_sel                           adaptive
% 2.69/0.99  --res_lit_sel_side                      none
% 2.69/0.99  --res_ordering                          kbo
% 2.69/0.99  --res_to_prop_solver                    active
% 2.69/0.99  --res_prop_simpl_new                    false
% 2.69/0.99  --res_prop_simpl_given                  true
% 2.69/0.99  --res_passive_queue_type                priority_queues
% 2.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.99  --res_passive_queues_freq               [15;5]
% 2.69/0.99  --res_forward_subs                      full
% 2.69/0.99  --res_backward_subs                     full
% 2.69/0.99  --res_forward_subs_resolution           true
% 2.69/0.99  --res_backward_subs_resolution          true
% 2.69/0.99  --res_orphan_elimination                true
% 2.69/0.99  --res_time_limit                        2.
% 2.69/0.99  --res_out_proof                         true
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Options
% 2.69/0.99  
% 2.69/0.99  --superposition_flag                    true
% 2.69/0.99  --sup_passive_queue_type                priority_queues
% 2.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.99  --demod_completeness_check              fast
% 2.69/0.99  --demod_use_ground                      true
% 2.69/0.99  --sup_to_prop_solver                    passive
% 2.69/0.99  --sup_prop_simpl_new                    true
% 2.69/0.99  --sup_prop_simpl_given                  true
% 2.69/0.99  --sup_fun_splitting                     false
% 2.69/0.99  --sup_smt_interval                      50000
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Simplification Setup
% 2.69/0.99  
% 2.69/0.99  --sup_indices_passive                   []
% 2.69/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_full_bw                           [BwDemod]
% 2.69/0.99  --sup_immed_triv                        [TrivRules]
% 2.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_immed_bw_main                     []
% 2.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  
% 2.69/0.99  ------ Combination Options
% 2.69/0.99  
% 2.69/0.99  --comb_res_mult                         3
% 2.69/0.99  --comb_sup_mult                         2
% 2.69/0.99  --comb_inst_mult                        10
% 2.69/0.99  
% 2.69/0.99  ------ Debug Options
% 2.69/0.99  
% 2.69/0.99  --dbg_backtrace                         false
% 2.69/0.99  --dbg_dump_prop_clauses                 false
% 2.69/0.99  --dbg_dump_prop_clauses_file            -
% 2.69/0.99  --dbg_out_stat                          false
% 2.69/0.99  ------ Parsing...
% 2.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/0.99  ------ Proving...
% 2.69/0.99  ------ Problem Properties 
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  clauses                                 22
% 2.69/0.99  conjectures                             2
% 2.69/0.99  EPR                                     1
% 2.69/0.99  Horn                                    19
% 2.69/0.99  unary                                   13
% 2.69/0.99  binary                                  2
% 2.69/0.99  lits                                    41
% 2.69/0.99  lits eq                                 27
% 2.69/0.99  fd_pure                                 0
% 2.69/0.99  fd_pseudo                               0
% 2.69/0.99  fd_cond                                 0
% 2.69/0.99  fd_pseudo_cond                          6
% 2.69/0.99  AC symbols                              0
% 2.69/0.99  
% 2.69/0.99  ------ Schedule dynamic 5 is on 
% 2.69/0.99  
% 2.69/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  ------ 
% 2.69/0.99  Current options:
% 2.69/0.99  ------ 
% 2.69/0.99  
% 2.69/0.99  ------ Input Options
% 2.69/0.99  
% 2.69/0.99  --out_options                           all
% 2.69/0.99  --tptp_safe_out                         true
% 2.69/0.99  --problem_path                          ""
% 2.69/0.99  --include_path                          ""
% 2.69/0.99  --clausifier                            res/vclausify_rel
% 2.69/0.99  --clausifier_options                    --mode clausify
% 2.69/0.99  --stdin                                 false
% 2.69/0.99  --stats_out                             all
% 2.69/0.99  
% 2.69/0.99  ------ General Options
% 2.69/0.99  
% 2.69/0.99  --fof                                   false
% 2.69/0.99  --time_out_real                         305.
% 2.69/0.99  --time_out_virtual                      -1.
% 2.69/0.99  --symbol_type_check                     false
% 2.69/0.99  --clausify_out                          false
% 2.69/0.99  --sig_cnt_out                           false
% 2.69/0.99  --trig_cnt_out                          false
% 2.69/0.99  --trig_cnt_out_tolerance                1.
% 2.69/0.99  --trig_cnt_out_sk_spl                   false
% 2.69/0.99  --abstr_cl_out                          false
% 2.69/0.99  
% 2.69/0.99  ------ Global Options
% 2.69/0.99  
% 2.69/0.99  --schedule                              default
% 2.69/0.99  --add_important_lit                     false
% 2.69/0.99  --prop_solver_per_cl                    1000
% 2.69/0.99  --min_unsat_core                        false
% 2.69/0.99  --soft_assumptions                      false
% 2.69/0.99  --soft_lemma_size                       3
% 2.69/0.99  --prop_impl_unit_size                   0
% 2.69/0.99  --prop_impl_unit                        []
% 2.69/0.99  --share_sel_clauses                     true
% 2.69/0.99  --reset_solvers                         false
% 2.69/0.99  --bc_imp_inh                            [conj_cone]
% 2.69/0.99  --conj_cone_tolerance                   3.
% 2.69/0.99  --extra_neg_conj                        none
% 2.69/0.99  --large_theory_mode                     true
% 2.69/0.99  --prolific_symb_bound                   200
% 2.69/0.99  --lt_threshold                          2000
% 2.69/0.99  --clause_weak_htbl                      true
% 2.69/0.99  --gc_record_bc_elim                     false
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing Options
% 2.69/0.99  
% 2.69/0.99  --preprocessing_flag                    true
% 2.69/0.99  --time_out_prep_mult                    0.1
% 2.69/0.99  --splitting_mode                        input
% 2.69/0.99  --splitting_grd                         true
% 2.69/0.99  --splitting_cvd                         false
% 2.69/0.99  --splitting_cvd_svl                     false
% 2.69/0.99  --splitting_nvd                         32
% 2.69/0.99  --sub_typing                            true
% 2.69/0.99  --prep_gs_sim                           true
% 2.69/0.99  --prep_unflatten                        true
% 2.69/0.99  --prep_res_sim                          true
% 2.69/0.99  --prep_upred                            true
% 2.69/0.99  --prep_sem_filter                       exhaustive
% 2.69/0.99  --prep_sem_filter_out                   false
% 2.69/0.99  --pred_elim                             true
% 2.69/0.99  --res_sim_input                         true
% 2.69/0.99  --eq_ax_congr_red                       true
% 2.69/0.99  --pure_diseq_elim                       true
% 2.69/0.99  --brand_transform                       false
% 2.69/0.99  --non_eq_to_eq                          false
% 2.69/0.99  --prep_def_merge                        true
% 2.69/0.99  --prep_def_merge_prop_impl              false
% 2.69/0.99  --prep_def_merge_mbd                    true
% 2.69/0.99  --prep_def_merge_tr_red                 false
% 2.69/0.99  --prep_def_merge_tr_cl                  false
% 2.69/0.99  --smt_preprocessing                     true
% 2.69/0.99  --smt_ac_axioms                         fast
% 2.69/0.99  --preprocessed_out                      false
% 2.69/0.99  --preprocessed_stats                    false
% 2.69/0.99  
% 2.69/0.99  ------ Abstraction refinement Options
% 2.69/0.99  
% 2.69/0.99  --abstr_ref                             []
% 2.69/0.99  --abstr_ref_prep                        false
% 2.69/0.99  --abstr_ref_until_sat                   false
% 2.69/0.99  --abstr_ref_sig_restrict                funpre
% 2.69/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.99  --abstr_ref_under                       []
% 2.69/0.99  
% 2.69/0.99  ------ SAT Options
% 2.69/0.99  
% 2.69/0.99  --sat_mode                              false
% 2.69/0.99  --sat_fm_restart_options                ""
% 2.69/0.99  --sat_gr_def                            false
% 2.69/0.99  --sat_epr_types                         true
% 2.69/0.99  --sat_non_cyclic_types                  false
% 2.69/0.99  --sat_finite_models                     false
% 2.69/0.99  --sat_fm_lemmas                         false
% 2.69/0.99  --sat_fm_prep                           false
% 2.69/0.99  --sat_fm_uc_incr                        true
% 2.69/0.99  --sat_out_model                         small
% 2.69/0.99  --sat_out_clauses                       false
% 2.69/0.99  
% 2.69/0.99  ------ QBF Options
% 2.69/0.99  
% 2.69/0.99  --qbf_mode                              false
% 2.69/0.99  --qbf_elim_univ                         false
% 2.69/0.99  --qbf_dom_inst                          none
% 2.69/0.99  --qbf_dom_pre_inst                      false
% 2.69/0.99  --qbf_sk_in                             false
% 2.69/0.99  --qbf_pred_elim                         true
% 2.69/0.99  --qbf_split                             512
% 2.69/0.99  
% 2.69/0.99  ------ BMC1 Options
% 2.69/0.99  
% 2.69/0.99  --bmc1_incremental                      false
% 2.69/0.99  --bmc1_axioms                           reachable_all
% 2.69/0.99  --bmc1_min_bound                        0
% 2.69/0.99  --bmc1_max_bound                        -1
% 2.69/0.99  --bmc1_max_bound_default                -1
% 2.69/0.99  --bmc1_symbol_reachability              true
% 2.69/0.99  --bmc1_property_lemmas                  false
% 2.69/0.99  --bmc1_k_induction                      false
% 2.69/0.99  --bmc1_non_equiv_states                 false
% 2.69/0.99  --bmc1_deadlock                         false
% 2.69/0.99  --bmc1_ucm                              false
% 2.69/0.99  --bmc1_add_unsat_core                   none
% 2.69/0.99  --bmc1_unsat_core_children              false
% 2.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.99  --bmc1_out_stat                         full
% 2.69/0.99  --bmc1_ground_init                      false
% 2.69/0.99  --bmc1_pre_inst_next_state              false
% 2.69/0.99  --bmc1_pre_inst_state                   false
% 2.69/0.99  --bmc1_pre_inst_reach_state             false
% 2.69/0.99  --bmc1_out_unsat_core                   false
% 2.69/0.99  --bmc1_aig_witness_out                  false
% 2.69/0.99  --bmc1_verbose                          false
% 2.69/0.99  --bmc1_dump_clauses_tptp                false
% 2.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.99  --bmc1_dump_file                        -
% 2.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.99  --bmc1_ucm_extend_mode                  1
% 2.69/0.99  --bmc1_ucm_init_mode                    2
% 2.69/0.99  --bmc1_ucm_cone_mode                    none
% 2.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.99  --bmc1_ucm_relax_model                  4
% 2.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.99  --bmc1_ucm_layered_model                none
% 2.69/0.99  --bmc1_ucm_max_lemma_size               10
% 2.69/0.99  
% 2.69/0.99  ------ AIG Options
% 2.69/0.99  
% 2.69/0.99  --aig_mode                              false
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation Options
% 2.69/0.99  
% 2.69/0.99  --instantiation_flag                    true
% 2.69/0.99  --inst_sos_flag                         false
% 2.69/0.99  --inst_sos_phase                        true
% 2.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel_side                     none
% 2.69/0.99  --inst_solver_per_active                1400
% 2.69/0.99  --inst_solver_calls_frac                1.
% 2.69/0.99  --inst_passive_queue_type               priority_queues
% 2.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.99  --inst_passive_queues_freq              [25;2]
% 2.69/0.99  --inst_dismatching                      true
% 2.69/0.99  --inst_eager_unprocessed_to_passive     true
% 2.69/0.99  --inst_prop_sim_given                   true
% 2.69/0.99  --inst_prop_sim_new                     false
% 2.69/0.99  --inst_subs_new                         false
% 2.69/0.99  --inst_eq_res_simp                      false
% 2.69/0.99  --inst_subs_given                       false
% 2.69/0.99  --inst_orphan_elimination               true
% 2.69/0.99  --inst_learning_loop_flag               true
% 2.69/0.99  --inst_learning_start                   3000
% 2.69/0.99  --inst_learning_factor                  2
% 2.69/0.99  --inst_start_prop_sim_after_learn       3
% 2.69/0.99  --inst_sel_renew                        solver
% 2.69/0.99  --inst_lit_activity_flag                true
% 2.69/0.99  --inst_restr_to_given                   false
% 2.69/0.99  --inst_activity_threshold               500
% 2.69/0.99  --inst_out_proof                        true
% 2.69/0.99  
% 2.69/0.99  ------ Resolution Options
% 2.69/0.99  
% 2.69/0.99  --resolution_flag                       false
% 2.69/0.99  --res_lit_sel                           adaptive
% 2.69/0.99  --res_lit_sel_side                      none
% 2.69/0.99  --res_ordering                          kbo
% 2.69/0.99  --res_to_prop_solver                    active
% 2.69/0.99  --res_prop_simpl_new                    false
% 2.69/0.99  --res_prop_simpl_given                  true
% 2.69/0.99  --res_passive_queue_type                priority_queues
% 2.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.99  --res_passive_queues_freq               [15;5]
% 2.69/0.99  --res_forward_subs                      full
% 2.69/0.99  --res_backward_subs                     full
% 2.69/0.99  --res_forward_subs_resolution           true
% 2.69/0.99  --res_backward_subs_resolution          true
% 2.69/0.99  --res_orphan_elimination                true
% 2.69/0.99  --res_time_limit                        2.
% 2.69/0.99  --res_out_proof                         true
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Options
% 2.69/0.99  
% 2.69/0.99  --superposition_flag                    true
% 2.69/0.99  --sup_passive_queue_type                priority_queues
% 2.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.99  --demod_completeness_check              fast
% 2.69/0.99  --demod_use_ground                      true
% 2.69/0.99  --sup_to_prop_solver                    passive
% 2.69/0.99  --sup_prop_simpl_new                    true
% 2.69/0.99  --sup_prop_simpl_given                  true
% 2.69/0.99  --sup_fun_splitting                     false
% 2.69/0.99  --sup_smt_interval                      50000
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Simplification Setup
% 2.69/0.99  
% 2.69/0.99  --sup_indices_passive                   []
% 2.69/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_full_bw                           [BwDemod]
% 2.69/0.99  --sup_immed_triv                        [TrivRules]
% 2.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_immed_bw_main                     []
% 2.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  
% 2.69/0.99  ------ Combination Options
% 2.69/0.99  
% 2.69/0.99  --comb_res_mult                         3
% 2.69/0.99  --comb_sup_mult                         2
% 2.69/0.99  --comb_inst_mult                        10
% 2.69/0.99  
% 2.69/0.99  ------ Debug Options
% 2.69/0.99  
% 2.69/0.99  --dbg_backtrace                         false
% 2.69/0.99  --dbg_dump_prop_clauses                 false
% 2.69/0.99  --dbg_dump_prop_clauses_file            -
% 2.69/0.99  --dbg_out_stat                          false
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  ------ Proving...
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  % SZS status Theorem for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  fof(f8,axiom,(
% 2.69/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f23,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.69/0.99    inference(ennf_transformation,[],[f8])).
% 2.69/0.99  
% 2.69/0.99  fof(f25,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.69/0.99    inference(nnf_transformation,[],[f23])).
% 2.69/0.99  
% 2.69/0.99  fof(f26,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.69/0.99    inference(flattening,[],[f25])).
% 2.69/0.99  
% 2.69/0.99  fof(f27,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.69/0.99    inference(rectify,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f28,plain,(
% 2.69/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f29,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.69/0.99  
% 2.69/0.99  fof(f46,plain,(
% 2.69/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.69/0.99    inference(cnf_transformation,[],[f29])).
% 2.69/0.99  
% 2.69/0.99  fof(f14,axiom,(
% 2.69/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f59,plain,(
% 2.69/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f14])).
% 2.69/0.99  
% 2.69/0.99  fof(f77,plain,(
% 2.69/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.69/0.99    inference(definition_unfolding,[],[f46,f59])).
% 2.69/0.99  
% 2.69/0.99  fof(f88,plain,(
% 2.69/0.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 2.69/0.99    inference(equality_resolution,[],[f77])).
% 2.69/0.99  
% 2.69/0.99  fof(f89,plain,(
% 2.69/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 2.69/0.99    inference(equality_resolution,[],[f88])).
% 2.69/0.99  
% 2.69/0.99  fof(f2,axiom,(
% 2.69/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f20,plain,(
% 2.69/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.69/0.99    inference(rectify,[],[f2])).
% 2.69/0.99  
% 2.69/0.99  fof(f37,plain,(
% 2.69/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.69/0.99    inference(cnf_transformation,[],[f20])).
% 2.69/0.99  
% 2.69/0.99  fof(f5,axiom,(
% 2.69/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f40,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.69/0.99    inference(cnf_transformation,[],[f5])).
% 2.69/0.99  
% 2.69/0.99  fof(f71,plain,(
% 2.69/0.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.69/0.99    inference(definition_unfolding,[],[f37,f40])).
% 2.69/0.99  
% 2.69/0.99  fof(f4,axiom,(
% 2.69/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f39,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f4])).
% 2.69/0.99  
% 2.69/0.99  fof(f68,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f39,f40])).
% 2.69/0.99  
% 2.69/0.99  fof(f18,conjecture,(
% 2.69/0.99    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f19,negated_conjecture,(
% 2.69/0.99    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 2.69/0.99    inference(negated_conjecture,[],[f18])).
% 2.69/0.99  
% 2.69/0.99  fof(f24,plain,(
% 2.69/0.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 2.69/0.99    inference(ennf_transformation,[],[f19])).
% 2.69/0.99  
% 2.69/0.99  fof(f34,plain,(
% 2.69/0.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f35,plain,(
% 2.69/0.99    sK2 != sK3 & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 2.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f34])).
% 2.69/0.99  
% 2.69/0.99  fof(f63,plain,(
% 2.69/0.99    k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 2.69/0.99    inference(cnf_transformation,[],[f35])).
% 2.69/0.99  
% 2.69/0.99  fof(f12,axiom,(
% 2.69/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f57,plain,(
% 2.69/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f12])).
% 2.69/0.99  
% 2.69/0.99  fof(f13,axiom,(
% 2.69/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f58,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f13])).
% 2.69/0.99  
% 2.69/0.99  fof(f65,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f58,f59])).
% 2.69/0.99  
% 2.69/0.99  fof(f66,plain,(
% 2.69/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f57,f65])).
% 2.69/0.99  
% 2.69/0.99  fof(f87,plain,(
% 2.69/0.99    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2)),
% 2.69/0.99    inference(definition_unfolding,[],[f63,f40,f66,f66,f66])).
% 2.69/0.99  
% 2.69/0.99  fof(f3,axiom,(
% 2.69/0.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f38,plain,(
% 2.69/0.99    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.69/0.99    inference(cnf_transformation,[],[f3])).
% 2.69/0.99  
% 2.69/0.99  fof(f72,plain,(
% 2.69/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1))) )),
% 2.69/0.99    inference(definition_unfolding,[],[f38,f40])).
% 2.69/0.99  
% 2.69/0.99  fof(f1,axiom,(
% 2.69/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f21,plain,(
% 2.69/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.69/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.69/0.99  
% 2.69/0.99  fof(f22,plain,(
% 2.69/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.69/0.99    inference(ennf_transformation,[],[f21])).
% 2.69/0.99  
% 2.69/0.99  fof(f36,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f22])).
% 2.69/0.99  
% 2.69/0.99  fof(f70,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f36,f40])).
% 2.69/0.99  
% 2.69/0.99  fof(f6,axiom,(
% 2.69/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f41,plain,(
% 2.69/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.69/0.99    inference(cnf_transformation,[],[f6])).
% 2.69/0.99  
% 2.69/0.99  fof(f11,axiom,(
% 2.69/0.99    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f56,plain,(
% 2.69/0.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f11])).
% 2.69/0.99  
% 2.69/0.99  fof(f7,axiom,(
% 2.69/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f42,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f7])).
% 2.69/0.99  
% 2.69/0.99  fof(f69,plain,(
% 2.69/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f56,f42,f59,f66])).
% 2.69/0.99  
% 2.69/0.99  fof(f9,axiom,(
% 2.69/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f30,plain,(
% 2.69/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.69/0.99    inference(nnf_transformation,[],[f9])).
% 2.69/0.99  
% 2.69/0.99  fof(f31,plain,(
% 2.69/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.69/0.99    inference(rectify,[],[f30])).
% 2.69/0.99  
% 2.69/0.99  fof(f32,plain,(
% 2.69/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f33,plain,(
% 2.69/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 2.69/0.99  
% 2.69/0.99  fof(f51,plain,(
% 2.69/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.69/0.99    inference(cnf_transformation,[],[f33])).
% 2.69/0.99  
% 2.69/0.99  fof(f84,plain,(
% 2.69/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.69/0.99    inference(definition_unfolding,[],[f51,f66])).
% 2.69/0.99  
% 2.69/0.99  fof(f97,plain,(
% 2.69/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 2.69/0.99    inference(equality_resolution,[],[f84])).
% 2.69/0.99  
% 2.69/0.99  fof(f52,plain,(
% 2.69/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.69/0.99    inference(cnf_transformation,[],[f33])).
% 2.69/0.99  
% 2.69/0.99  fof(f83,plain,(
% 2.69/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.69/0.99    inference(definition_unfolding,[],[f52,f66])).
% 2.69/0.99  
% 2.69/0.99  fof(f95,plain,(
% 2.69/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 2.69/0.99    inference(equality_resolution,[],[f83])).
% 2.69/0.99  
% 2.69/0.99  fof(f96,plain,(
% 2.69/0.99    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 2.69/0.99    inference(equality_resolution,[],[f95])).
% 2.69/0.99  
% 2.69/0.99  fof(f64,plain,(
% 2.69/0.99    sK2 != sK3),
% 2.69/0.99    inference(cnf_transformation,[],[f35])).
% 2.69/0.99  
% 2.69/0.99  cnf(c_10,plain,
% 2.69/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 2.69/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_895,plain,
% 2.69/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3,plain,
% 2.69/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 2.69/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_0,plain,
% 2.69/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.69/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1243,plain,
% 2.69/0.99      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_21,negated_conjecture,
% 2.69/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 2.69/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1244,plain,
% 2.69/0.99      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_21,c_0]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1256,plain,
% 2.69/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 2.69/0.99      inference(demodulation,[status(thm)],[c_1243,c_1244]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_4,plain,
% 2.69/0.99      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
% 2.69/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_900,plain,
% 2.69/0.99      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2000,plain,
% 2.69/0.99      ( r1_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1256,c_900]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2027,plain,
% 2.69/0.99      ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
% 2.69/0.99      inference(demodulation,[status(thm)],[c_2000,c_3]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2,plain,
% 2.69/0.99      ( ~ r1_xboole_0(X0,X1)
% 2.69/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.69/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_901,plain,
% 2.69/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 2.69/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3181,plain,
% 2.69/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))) = k1_xboole_0 ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_2027,c_901]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3212,plain,
% 2.69/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_3181,c_0]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5,plain,
% 2.69/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.69/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3214,plain,
% 2.69/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 2.69/0.99      inference(demodulation,[status(thm)],[c_3212,c_5]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3215,plain,
% 2.69/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 2.69/0.99      inference(demodulation,[status(thm)],[c_3214,c_3181]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1,plain,
% 2.69/0.99      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
% 2.69/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1771,plain,
% 2.69/0.99      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK3,sK3,sK3,sK2) ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1256,c_1]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3275,plain,
% 2.69/0.99      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0) = k2_enumset1(sK3,sK3,sK3,sK2) ),
% 2.69/0.99      inference(demodulation,[status(thm)],[c_3215,c_1771]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3523,plain,
% 2.69/0.99      ( k2_enumset1(sK3,sK3,sK3,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_3275,c_5]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_17,plain,
% 2.69/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 2.69/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_888,plain,
% 2.69/0.99      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_4387,plain,
% 2.69/0.99      ( sK3 = X0
% 2.69/0.99      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK2)) != iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_3523,c_888]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5575,plain,
% 2.69/0.99      ( sK3 = sK2 ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_895,c_4387]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_650,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1018,plain,
% 2.69/0.99      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_650]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1019,plain,
% 2.69/0.99      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1018]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_16,plain,
% 2.69/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 2.69/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_28,plain,
% 2.69/0.99      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_25,plain,
% 2.69/0.99      ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_20,negated_conjecture,
% 2.69/0.99      ( sK2 != sK3 ),
% 2.69/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(contradiction,plain,
% 2.69/0.99      ( $false ),
% 2.69/0.99      inference(minisat,[status(thm)],[c_5575,c_1019,c_28,c_25,c_20]) ).
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  ------                               Statistics
% 2.69/0.99  
% 2.69/0.99  ------ General
% 2.69/0.99  
% 2.69/0.99  abstr_ref_over_cycles:                  0
% 2.69/0.99  abstr_ref_under_cycles:                 0
% 2.69/0.99  gc_basic_clause_elim:                   0
% 2.69/0.99  forced_gc_time:                         0
% 2.69/0.99  parsing_time:                           0.008
% 2.69/0.99  unif_index_cands_time:                  0.
% 2.69/0.99  unif_index_add_time:                    0.
% 2.69/0.99  orderings_time:                         0.
% 2.69/0.99  out_proof_time:                         0.007
% 2.69/0.99  total_time:                             0.277
% 2.69/0.99  num_of_symbols:                         42
% 2.69/0.99  num_of_terms:                           8892
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing
% 2.69/0.99  
% 2.69/0.99  num_of_splits:                          0
% 2.69/0.99  num_of_split_atoms:                     0
% 2.69/0.99  num_of_reused_defs:                     0
% 2.69/0.99  num_eq_ax_congr_red:                    26
% 2.69/0.99  num_of_sem_filtered_clauses:            1
% 2.69/0.99  num_of_subtypes:                        0
% 2.69/0.99  monotx_restored_types:                  0
% 2.69/0.99  sat_num_of_epr_types:                   0
% 2.69/0.99  sat_num_of_non_cyclic_types:            0
% 2.69/0.99  sat_guarded_non_collapsed_types:        0
% 2.69/0.99  num_pure_diseq_elim:                    0
% 2.69/0.99  simp_replaced_by:                       0
% 2.69/0.99  res_preprocessed:                       81
% 2.69/0.99  prep_upred:                             0
% 2.69/0.99  prep_unflattend:                        38
% 2.69/0.99  smt_new_axioms:                         0
% 2.69/0.99  pred_elim_cands:                        2
% 2.69/0.99  pred_elim:                              0
% 2.69/0.99  pred_elim_cl:                           0
% 2.69/0.99  pred_elim_cycles:                       2
% 2.69/0.99  merged_defs:                            0
% 2.69/0.99  merged_defs_ncl:                        0
% 2.69/0.99  bin_hyper_res:                          0
% 2.69/0.99  prep_cycles:                            3
% 2.69/0.99  pred_elim_time:                         0.007
% 2.69/0.99  splitting_time:                         0.
% 2.69/0.99  sem_filter_time:                        0.
% 2.69/0.99  monotx_time:                            0.001
% 2.69/0.99  subtype_inf_time:                       0.
% 2.69/0.99  
% 2.69/0.99  ------ Problem properties
% 2.69/0.99  
% 2.69/0.99  clauses:                                22
% 2.69/0.99  conjectures:                            2
% 2.69/0.99  epr:                                    1
% 2.69/0.99  horn:                                   19
% 2.69/0.99  ground:                                 2
% 2.69/0.99  unary:                                  13
% 2.69/0.99  binary:                                 2
% 2.69/0.99  lits:                                   41
% 2.69/0.99  lits_eq:                                27
% 2.69/0.99  fd_pure:                                0
% 2.69/0.99  fd_pseudo:                              0
% 2.69/0.99  fd_cond:                                0
% 2.69/0.99  fd_pseudo_cond:                         6
% 2.69/0.99  ac_symbols:                             0
% 2.69/0.99  
% 2.69/0.99  ------ Propositional Solver
% 2.69/0.99  
% 2.69/0.99  prop_solver_calls:                      23
% 2.69/0.99  prop_fast_solver_calls:                 509
% 2.69/0.99  smt_solver_calls:                       0
% 2.69/0.99  smt_fast_solver_calls:                  0
% 2.69/0.99  prop_num_of_clauses:                    2123
% 2.69/0.99  prop_preprocess_simplified:             6844
% 2.69/0.99  prop_fo_subsumed:                       0
% 2.69/0.99  prop_solver_time:                       0.
% 2.69/0.99  smt_solver_time:                        0.
% 2.69/0.99  smt_fast_solver_time:                   0.
% 2.69/0.99  prop_fast_solver_time:                  0.
% 2.69/0.99  prop_unsat_core_time:                   0.
% 2.69/0.99  
% 2.69/0.99  ------ QBF
% 2.69/0.99  
% 2.69/0.99  qbf_q_res:                              0
% 2.69/0.99  qbf_num_tautologies:                    0
% 2.69/0.99  qbf_prep_cycles:                        0
% 2.69/0.99  
% 2.69/0.99  ------ BMC1
% 2.69/0.99  
% 2.69/0.99  bmc1_current_bound:                     -1
% 2.69/0.99  bmc1_last_solved_bound:                 -1
% 2.69/0.99  bmc1_unsat_core_size:                   -1
% 2.69/0.99  bmc1_unsat_core_parents_size:           -1
% 2.69/0.99  bmc1_merge_next_fun:                    0
% 2.69/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation
% 2.69/0.99  
% 2.69/0.99  inst_num_of_clauses:                    694
% 2.69/0.99  inst_num_in_passive:                    425
% 2.69/0.99  inst_num_in_active:                     202
% 2.69/0.99  inst_num_in_unprocessed:                67
% 2.69/0.99  inst_num_of_loops:                      220
% 2.69/0.99  inst_num_of_learning_restarts:          0
% 2.69/0.99  inst_num_moves_active_passive:          17
% 2.69/0.99  inst_lit_activity:                      0
% 2.69/0.99  inst_lit_activity_moves:                0
% 2.69/0.99  inst_num_tautologies:                   0
% 2.69/0.99  inst_num_prop_implied:                  0
% 2.69/0.99  inst_num_existing_simplified:           0
% 2.69/0.99  inst_num_eq_res_simplified:             0
% 2.69/0.99  inst_num_child_elim:                    0
% 2.69/0.99  inst_num_of_dismatching_blockings:      387
% 2.69/0.99  inst_num_of_non_proper_insts:           631
% 2.69/0.99  inst_num_of_duplicates:                 0
% 2.69/0.99  inst_inst_num_from_inst_to_res:         0
% 2.69/0.99  inst_dismatching_checking_time:         0.
% 2.69/0.99  
% 2.69/0.99  ------ Resolution
% 2.69/0.99  
% 2.69/0.99  res_num_of_clauses:                     0
% 2.69/0.99  res_num_in_passive:                     0
% 2.69/0.99  res_num_in_active:                      0
% 2.69/0.99  res_num_of_loops:                       84
% 2.69/0.99  res_forward_subset_subsumed:            102
% 2.69/0.99  res_backward_subset_subsumed:           0
% 2.69/0.99  res_forward_subsumed:                   5
% 2.69/0.99  res_backward_subsumed:                  0
% 2.69/0.99  res_forward_subsumption_resolution:     0
% 2.69/0.99  res_backward_subsumption_resolution:    0
% 2.69/0.99  res_clause_to_clause_subsumption:       473
% 2.69/0.99  res_orphan_elimination:                 0
% 2.69/0.99  res_tautology_del:                      13
% 2.69/0.99  res_num_eq_res_simplified:              0
% 2.69/0.99  res_num_sel_changes:                    0
% 2.69/0.99  res_moves_from_active_to_pass:          0
% 2.69/0.99  
% 2.69/0.99  ------ Superposition
% 2.69/0.99  
% 2.69/0.99  sup_time_total:                         0.
% 2.69/0.99  sup_time_generating:                    0.
% 2.69/0.99  sup_time_sim_full:                      0.
% 2.69/0.99  sup_time_sim_immed:                     0.
% 2.69/0.99  
% 2.69/0.99  sup_num_of_clauses:                     69
% 2.69/0.99  sup_num_in_active:                      25
% 2.69/0.99  sup_num_in_passive:                     44
% 2.69/0.99  sup_num_of_loops:                       43
% 2.69/0.99  sup_fw_superposition:                   55
% 2.69/0.99  sup_bw_superposition:                   62
% 2.69/0.99  sup_immediate_simplified:               50
% 2.69/0.99  sup_given_eliminated:                   5
% 2.69/0.99  comparisons_done:                       0
% 2.69/0.99  comparisons_avoided:                    2
% 2.69/0.99  
% 2.69/0.99  ------ Simplifications
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  sim_fw_subset_subsumed:                 0
% 2.69/0.99  sim_bw_subset_subsumed:                 0
% 2.69/0.99  sim_fw_subsumed:                        13
% 2.69/0.99  sim_bw_subsumed:                        2
% 2.69/0.99  sim_fw_subsumption_res:                 0
% 2.69/0.99  sim_bw_subsumption_res:                 0
% 2.69/0.99  sim_tautology_del:                      0
% 2.69/0.99  sim_eq_tautology_del:                   5
% 2.69/0.99  sim_eq_res_simp:                        0
% 2.69/0.99  sim_fw_demodulated:                     21
% 2.69/0.99  sim_bw_demodulated:                     29
% 2.69/0.99  sim_light_normalised:                   22
% 2.69/0.99  sim_joinable_taut:                      0
% 2.69/0.99  sim_joinable_simp:                      0
% 2.69/0.99  sim_ac_normalised:                      0
% 2.69/0.99  sim_smt_subsumption:                    0
% 2.69/0.99  
%------------------------------------------------------------------------------
