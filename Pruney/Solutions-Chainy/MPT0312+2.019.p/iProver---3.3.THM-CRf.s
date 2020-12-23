%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:15 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  119 (2200 expanded)
%              Number of clauses        :   54 ( 398 expanded)
%              Number of leaves         :   18 ( 637 expanded)
%              Depth                    :   23
%              Number of atoms          :  245 (3019 expanded)
%              Number of equality atoms :  135 (2264 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f63])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f64])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f65])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k3_enumset1(X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)) != k2_zfmisc_1(sK2,sK4)
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)) != k2_zfmisc_1(sK2,sK4)
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f34])).

fof(f60,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f40,f65])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f77,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)))) = X0 ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))) ),
    inference(definition_unfolding,[],[f58,f65,f65,f65])).

fof(f61,plain,(
    k3_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)) != k2_zfmisc_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)),k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f59,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_469,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_870,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_15,c_14])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k3_enumset1(X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_486,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10,c_9,c_15])).

cnf(c_877,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_870,c_486])).

cnf(c_1168,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_14,c_877])).

cnf(c_1595,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k1_xboole_0) = X1 ),
    inference(superposition,[status(thm)],[c_15,c_1168])).

cnf(c_1719,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_877,c_1595])).

cnf(c_2214,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_1719,c_14])).

cnf(c_2242,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_2214,c_486])).

cnf(c_2243,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2242,c_14])).

cnf(c_8757,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = X2
    | r2_hidden(sK1(X1,X0,X2),X2) = iProver_top
    | r2_hidden(sK1(X1,X0,X2),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_469,c_2243])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_463,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_464,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_854,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_463,c_464])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_466,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2608,plain,
    ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK4,sK5),sK5)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_466])).

cnf(c_872,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_1171,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_872,c_877])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)))) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_12,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_497,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_13,c_12])).

cnf(c_861,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_14,c_497])).

cnf(c_866,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_861,c_15,c_486])).

cnf(c_1186,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1171,c_866])).

cnf(c_1268,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_877,c_1186])).

cnf(c_2617,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2608,c_1268])).

cnf(c_8762,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,sK4)))) = X1
    | r2_hidden(sK1(X0,sK4,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,sK4,X1),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_8757,c_2617])).

cnf(c_9606,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,sK4)))) = sK4
    | r2_hidden(sK1(X0,sK4,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_8762,c_2617])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_470,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10190,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = X2
    | r2_hidden(sK1(X1,X0,X2),X1) != iProver_top
    | r2_hidden(sK1(X1,X0,X2),X2) != iProver_top
    | r2_hidden(sK1(X1,X0,X2),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_470,c_2243])).

cnf(c_10216,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) = sK4
    | r2_hidden(sK1(sK5,sK4,sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9606,c_10190])).

cnf(c_11615,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) = sK4
    | r2_hidden(sK1(sK5,sK4,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_8757,c_10216])).

cnf(c_11622,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11615,c_10216])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X2),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)),k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_547,plain,
    ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,sK3),k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3))),k5_xboole_0(k5_xboole_0(sK5,sK4),k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_16,c_17])).

cnf(c_862,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK2,k5_xboole_0(sK3,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)))),k5_xboole_0(k5_xboole_0(sK5,sK4),k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_14,c_547])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_462,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_855,plain,
    ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_462,c_464])).

cnf(c_1141,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK2,k5_xboole_0(sK3,sK3)),k5_xboole_0(k5_xboole_0(sK5,sK4),k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
    inference(light_normalisation,[status(thm)],[c_862,c_855])).

cnf(c_1142,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(k5_xboole_0(sK5,sK4),k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_1141,c_15,c_866])).

cnf(c_5407,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK4,k5_xboole_0(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4))))) != k2_zfmisc_1(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_2243,c_1142])).

cnf(c_11987,plain,
    ( k2_zfmisc_1(sK2,sK4) != k2_zfmisc_1(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_11622,c_5407])).

cnf(c_11988,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_11987])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 4.06/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.06/0.99  
% 4.06/0.99  ------  iProver source info
% 4.06/0.99  
% 4.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.06/0.99  git: non_committed_changes: false
% 4.06/0.99  git: last_make_outside_of_git: false
% 4.06/0.99  
% 4.06/0.99  ------ 
% 4.06/0.99  
% 4.06/0.99  ------ Input Options
% 4.06/0.99  
% 4.06/0.99  --out_options                           all
% 4.06/0.99  --tptp_safe_out                         true
% 4.06/0.99  --problem_path                          ""
% 4.06/0.99  --include_path                          ""
% 4.06/0.99  --clausifier                            res/vclausify_rel
% 4.06/0.99  --clausifier_options                    --mode clausify
% 4.06/0.99  --stdin                                 false
% 4.06/0.99  --stats_out                             all
% 4.06/0.99  
% 4.06/0.99  ------ General Options
% 4.06/0.99  
% 4.06/0.99  --fof                                   false
% 4.06/0.99  --time_out_real                         305.
% 4.06/0.99  --time_out_virtual                      -1.
% 4.06/0.99  --symbol_type_check                     false
% 4.06/0.99  --clausify_out                          false
% 4.06/0.99  --sig_cnt_out                           false
% 4.06/0.99  --trig_cnt_out                          false
% 4.06/0.99  --trig_cnt_out_tolerance                1.
% 4.06/0.99  --trig_cnt_out_sk_spl                   false
% 4.06/0.99  --abstr_cl_out                          false
% 4.06/0.99  
% 4.06/0.99  ------ Global Options
% 4.06/0.99  
% 4.06/0.99  --schedule                              default
% 4.06/0.99  --add_important_lit                     false
% 4.06/0.99  --prop_solver_per_cl                    1000
% 4.06/0.99  --min_unsat_core                        false
% 4.06/0.99  --soft_assumptions                      false
% 4.06/0.99  --soft_lemma_size                       3
% 4.06/0.99  --prop_impl_unit_size                   0
% 4.06/0.99  --prop_impl_unit                        []
% 4.06/0.99  --share_sel_clauses                     true
% 4.06/0.99  --reset_solvers                         false
% 4.06/0.99  --bc_imp_inh                            [conj_cone]
% 4.06/0.99  --conj_cone_tolerance                   3.
% 4.06/0.99  --extra_neg_conj                        none
% 4.06/0.99  --large_theory_mode                     true
% 4.06/0.99  --prolific_symb_bound                   200
% 4.06/0.99  --lt_threshold                          2000
% 4.06/0.99  --clause_weak_htbl                      true
% 4.06/0.99  --gc_record_bc_elim                     false
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing Options
% 4.06/0.99  
% 4.06/0.99  --preprocessing_flag                    true
% 4.06/0.99  --time_out_prep_mult                    0.1
% 4.06/0.99  --splitting_mode                        input
% 4.06/0.99  --splitting_grd                         true
% 4.06/0.99  --splitting_cvd                         false
% 4.06/0.99  --splitting_cvd_svl                     false
% 4.06/0.99  --splitting_nvd                         32
% 4.06/0.99  --sub_typing                            true
% 4.06/0.99  --prep_gs_sim                           true
% 4.06/0.99  --prep_unflatten                        true
% 4.06/0.99  --prep_res_sim                          true
% 4.06/0.99  --prep_upred                            true
% 4.06/0.99  --prep_sem_filter                       exhaustive
% 4.06/0.99  --prep_sem_filter_out                   false
% 4.06/0.99  --pred_elim                             true
% 4.06/0.99  --res_sim_input                         true
% 4.06/0.99  --eq_ax_congr_red                       true
% 4.06/0.99  --pure_diseq_elim                       true
% 4.06/0.99  --brand_transform                       false
% 4.06/0.99  --non_eq_to_eq                          false
% 4.06/0.99  --prep_def_merge                        true
% 4.06/0.99  --prep_def_merge_prop_impl              false
% 4.06/0.99  --prep_def_merge_mbd                    true
% 4.06/0.99  --prep_def_merge_tr_red                 false
% 4.06/0.99  --prep_def_merge_tr_cl                  false
% 4.06/0.99  --smt_preprocessing                     true
% 4.06/0.99  --smt_ac_axioms                         fast
% 4.06/0.99  --preprocessed_out                      false
% 4.06/0.99  --preprocessed_stats                    false
% 4.06/0.99  
% 4.06/0.99  ------ Abstraction refinement Options
% 4.06/0.99  
% 4.06/0.99  --abstr_ref                             []
% 4.06/0.99  --abstr_ref_prep                        false
% 4.06/0.99  --abstr_ref_until_sat                   false
% 4.06/0.99  --abstr_ref_sig_restrict                funpre
% 4.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.06/0.99  --abstr_ref_under                       []
% 4.06/0.99  
% 4.06/0.99  ------ SAT Options
% 4.06/0.99  
% 4.06/0.99  --sat_mode                              false
% 4.06/0.99  --sat_fm_restart_options                ""
% 4.06/0.99  --sat_gr_def                            false
% 4.06/0.99  --sat_epr_types                         true
% 4.06/0.99  --sat_non_cyclic_types                  false
% 4.06/0.99  --sat_finite_models                     false
% 4.06/0.99  --sat_fm_lemmas                         false
% 4.06/0.99  --sat_fm_prep                           false
% 4.06/0.99  --sat_fm_uc_incr                        true
% 4.06/0.99  --sat_out_model                         small
% 4.06/0.99  --sat_out_clauses                       false
% 4.06/0.99  
% 4.06/0.99  ------ QBF Options
% 4.06/0.99  
% 4.06/0.99  --qbf_mode                              false
% 4.06/0.99  --qbf_elim_univ                         false
% 4.06/0.99  --qbf_dom_inst                          none
% 4.06/0.99  --qbf_dom_pre_inst                      false
% 4.06/0.99  --qbf_sk_in                             false
% 4.06/0.99  --qbf_pred_elim                         true
% 4.06/0.99  --qbf_split                             512
% 4.06/0.99  
% 4.06/0.99  ------ BMC1 Options
% 4.06/0.99  
% 4.06/0.99  --bmc1_incremental                      false
% 4.06/0.99  --bmc1_axioms                           reachable_all
% 4.06/0.99  --bmc1_min_bound                        0
% 4.06/0.99  --bmc1_max_bound                        -1
% 4.06/0.99  --bmc1_max_bound_default                -1
% 4.06/0.99  --bmc1_symbol_reachability              true
% 4.06/0.99  --bmc1_property_lemmas                  false
% 4.06/0.99  --bmc1_k_induction                      false
% 4.06/0.99  --bmc1_non_equiv_states                 false
% 4.06/0.99  --bmc1_deadlock                         false
% 4.06/0.99  --bmc1_ucm                              false
% 4.06/0.99  --bmc1_add_unsat_core                   none
% 4.06/0.99  --bmc1_unsat_core_children              false
% 4.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.06/0.99  --bmc1_out_stat                         full
% 4.06/0.99  --bmc1_ground_init                      false
% 4.06/0.99  --bmc1_pre_inst_next_state              false
% 4.06/0.99  --bmc1_pre_inst_state                   false
% 4.06/0.99  --bmc1_pre_inst_reach_state             false
% 4.06/0.99  --bmc1_out_unsat_core                   false
% 4.06/0.99  --bmc1_aig_witness_out                  false
% 4.06/0.99  --bmc1_verbose                          false
% 4.06/0.99  --bmc1_dump_clauses_tptp                false
% 4.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.06/0.99  --bmc1_dump_file                        -
% 4.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.06/0.99  --bmc1_ucm_extend_mode                  1
% 4.06/0.99  --bmc1_ucm_init_mode                    2
% 4.06/0.99  --bmc1_ucm_cone_mode                    none
% 4.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.06/0.99  --bmc1_ucm_relax_model                  4
% 4.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.06/0.99  --bmc1_ucm_layered_model                none
% 4.06/0.99  --bmc1_ucm_max_lemma_size               10
% 4.06/0.99  
% 4.06/0.99  ------ AIG Options
% 4.06/0.99  
% 4.06/0.99  --aig_mode                              false
% 4.06/0.99  
% 4.06/0.99  ------ Instantiation Options
% 4.06/0.99  
% 4.06/0.99  --instantiation_flag                    true
% 4.06/0.99  --inst_sos_flag                         false
% 4.06/0.99  --inst_sos_phase                        true
% 4.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.06/0.99  --inst_lit_sel_side                     num_symb
% 4.06/0.99  --inst_solver_per_active                1400
% 4.06/0.99  --inst_solver_calls_frac                1.
% 4.06/0.99  --inst_passive_queue_type               priority_queues
% 4.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.06/0.99  --inst_passive_queues_freq              [25;2]
% 4.06/0.99  --inst_dismatching                      true
% 4.06/0.99  --inst_eager_unprocessed_to_passive     true
% 4.06/0.99  --inst_prop_sim_given                   true
% 4.06/0.99  --inst_prop_sim_new                     false
% 4.06/0.99  --inst_subs_new                         false
% 4.06/0.99  --inst_eq_res_simp                      false
% 4.06/0.99  --inst_subs_given                       false
% 4.06/0.99  --inst_orphan_elimination               true
% 4.06/0.99  --inst_learning_loop_flag               true
% 4.06/0.99  --inst_learning_start                   3000
% 4.06/0.99  --inst_learning_factor                  2
% 4.06/0.99  --inst_start_prop_sim_after_learn       3
% 4.06/0.99  --inst_sel_renew                        solver
% 4.06/0.99  --inst_lit_activity_flag                true
% 4.06/0.99  --inst_restr_to_given                   false
% 4.06/0.99  --inst_activity_threshold               500
% 4.06/0.99  --inst_out_proof                        true
% 4.06/0.99  
% 4.06/0.99  ------ Resolution Options
% 4.06/0.99  
% 4.06/0.99  --resolution_flag                       true
% 4.06/0.99  --res_lit_sel                           adaptive
% 4.06/0.99  --res_lit_sel_side                      none
% 4.06/0.99  --res_ordering                          kbo
% 4.06/0.99  --res_to_prop_solver                    active
% 4.06/0.99  --res_prop_simpl_new                    false
% 4.06/0.99  --res_prop_simpl_given                  true
% 4.06/0.99  --res_passive_queue_type                priority_queues
% 4.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.06/0.99  --res_passive_queues_freq               [15;5]
% 4.06/0.99  --res_forward_subs                      full
% 4.06/0.99  --res_backward_subs                     full
% 4.06/0.99  --res_forward_subs_resolution           true
% 4.06/0.99  --res_backward_subs_resolution          true
% 4.06/0.99  --res_orphan_elimination                true
% 4.06/0.99  --res_time_limit                        2.
% 4.06/0.99  --res_out_proof                         true
% 4.06/0.99  
% 4.06/0.99  ------ Superposition Options
% 4.06/0.99  
% 4.06/0.99  --superposition_flag                    true
% 4.06/0.99  --sup_passive_queue_type                priority_queues
% 4.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.06/0.99  --demod_completeness_check              fast
% 4.06/0.99  --demod_use_ground                      true
% 4.06/0.99  --sup_to_prop_solver                    passive
% 4.06/0.99  --sup_prop_simpl_new                    true
% 4.06/0.99  --sup_prop_simpl_given                  true
% 4.06/0.99  --sup_fun_splitting                     false
% 4.06/0.99  --sup_smt_interval                      50000
% 4.06/0.99  
% 4.06/0.99  ------ Superposition Simplification Setup
% 4.06/0.99  
% 4.06/0.99  --sup_indices_passive                   []
% 4.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.06/0.99  --sup_full_bw                           [BwDemod]
% 4.06/0.99  --sup_immed_triv                        [TrivRules]
% 4.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.06/0.99  --sup_immed_bw_main                     []
% 4.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.06/0.99  
% 4.06/0.99  ------ Combination Options
% 4.06/0.99  
% 4.06/0.99  --comb_res_mult                         3
% 4.06/0.99  --comb_sup_mult                         2
% 4.06/0.99  --comb_inst_mult                        10
% 4.06/0.99  
% 4.06/0.99  ------ Debug Options
% 4.06/0.99  
% 4.06/0.99  --dbg_backtrace                         false
% 4.06/0.99  --dbg_dump_prop_clauses                 false
% 4.06/0.99  --dbg_dump_prop_clauses_file            -
% 4.06/0.99  --dbg_out_stat                          false
% 4.06/0.99  ------ Parsing...
% 4.06/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.06/0.99  ------ Proving...
% 4.06/0.99  ------ Problem Properties 
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  clauses                                 20
% 4.06/0.99  conjectures                             3
% 4.06/0.99  EPR                                     3
% 4.06/0.99  Horn                                    17
% 4.06/0.99  unary                                   10
% 4.06/0.99  binary                                  5
% 4.06/0.99  lits                                    36
% 4.06/0.99  lits eq                                 12
% 4.06/0.99  fd_pure                                 0
% 4.06/0.99  fd_pseudo                               0
% 4.06/0.99  fd_cond                                 0
% 4.06/0.99  fd_pseudo_cond                          3
% 4.06/0.99  AC symbols                              0
% 4.06/0.99  
% 4.06/0.99  ------ Schedule dynamic 5 is on 
% 4.06/0.99  
% 4.06/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  ------ 
% 4.06/0.99  Current options:
% 4.06/0.99  ------ 
% 4.06/0.99  
% 4.06/0.99  ------ Input Options
% 4.06/0.99  
% 4.06/0.99  --out_options                           all
% 4.06/0.99  --tptp_safe_out                         true
% 4.06/0.99  --problem_path                          ""
% 4.06/0.99  --include_path                          ""
% 4.06/0.99  --clausifier                            res/vclausify_rel
% 4.06/0.99  --clausifier_options                    --mode clausify
% 4.06/0.99  --stdin                                 false
% 4.06/0.99  --stats_out                             all
% 4.06/0.99  
% 4.06/0.99  ------ General Options
% 4.06/0.99  
% 4.06/0.99  --fof                                   false
% 4.06/0.99  --time_out_real                         305.
% 4.06/0.99  --time_out_virtual                      -1.
% 4.06/0.99  --symbol_type_check                     false
% 4.06/0.99  --clausify_out                          false
% 4.06/0.99  --sig_cnt_out                           false
% 4.06/0.99  --trig_cnt_out                          false
% 4.06/0.99  --trig_cnt_out_tolerance                1.
% 4.06/0.99  --trig_cnt_out_sk_spl                   false
% 4.06/0.99  --abstr_cl_out                          false
% 4.06/0.99  
% 4.06/0.99  ------ Global Options
% 4.06/0.99  
% 4.06/0.99  --schedule                              default
% 4.06/0.99  --add_important_lit                     false
% 4.06/0.99  --prop_solver_per_cl                    1000
% 4.06/0.99  --min_unsat_core                        false
% 4.06/0.99  --soft_assumptions                      false
% 4.06/0.99  --soft_lemma_size                       3
% 4.06/0.99  --prop_impl_unit_size                   0
% 4.06/0.99  --prop_impl_unit                        []
% 4.06/0.99  --share_sel_clauses                     true
% 4.06/0.99  --reset_solvers                         false
% 4.06/0.99  --bc_imp_inh                            [conj_cone]
% 4.06/0.99  --conj_cone_tolerance                   3.
% 4.06/0.99  --extra_neg_conj                        none
% 4.06/0.99  --large_theory_mode                     true
% 4.06/0.99  --prolific_symb_bound                   200
% 4.06/0.99  --lt_threshold                          2000
% 4.06/0.99  --clause_weak_htbl                      true
% 4.06/0.99  --gc_record_bc_elim                     false
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing Options
% 4.06/0.99  
% 4.06/0.99  --preprocessing_flag                    true
% 4.06/0.99  --time_out_prep_mult                    0.1
% 4.06/0.99  --splitting_mode                        input
% 4.06/0.99  --splitting_grd                         true
% 4.06/0.99  --splitting_cvd                         false
% 4.06/0.99  --splitting_cvd_svl                     false
% 4.06/0.99  --splitting_nvd                         32
% 4.06/0.99  --sub_typing                            true
% 4.06/0.99  --prep_gs_sim                           true
% 4.06/0.99  --prep_unflatten                        true
% 4.06/0.99  --prep_res_sim                          true
% 4.06/0.99  --prep_upred                            true
% 4.06/0.99  --prep_sem_filter                       exhaustive
% 4.06/0.99  --prep_sem_filter_out                   false
% 4.06/0.99  --pred_elim                             true
% 4.06/0.99  --res_sim_input                         true
% 4.06/0.99  --eq_ax_congr_red                       true
% 4.06/0.99  --pure_diseq_elim                       true
% 4.06/0.99  --brand_transform                       false
% 4.06/0.99  --non_eq_to_eq                          false
% 4.06/0.99  --prep_def_merge                        true
% 4.06/0.99  --prep_def_merge_prop_impl              false
% 4.06/0.99  --prep_def_merge_mbd                    true
% 4.06/0.99  --prep_def_merge_tr_red                 false
% 4.06/0.99  --prep_def_merge_tr_cl                  false
% 4.06/0.99  --smt_preprocessing                     true
% 4.06/0.99  --smt_ac_axioms                         fast
% 4.06/0.99  --preprocessed_out                      false
% 4.06/0.99  --preprocessed_stats                    false
% 4.06/0.99  
% 4.06/0.99  ------ Abstraction refinement Options
% 4.06/0.99  
% 4.06/0.99  --abstr_ref                             []
% 4.06/0.99  --abstr_ref_prep                        false
% 4.06/0.99  --abstr_ref_until_sat                   false
% 4.06/0.99  --abstr_ref_sig_restrict                funpre
% 4.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.06/0.99  --abstr_ref_under                       []
% 4.06/0.99  
% 4.06/0.99  ------ SAT Options
% 4.06/0.99  
% 4.06/0.99  --sat_mode                              false
% 4.06/0.99  --sat_fm_restart_options                ""
% 4.06/0.99  --sat_gr_def                            false
% 4.06/0.99  --sat_epr_types                         true
% 4.06/0.99  --sat_non_cyclic_types                  false
% 4.06/0.99  --sat_finite_models                     false
% 4.06/0.99  --sat_fm_lemmas                         false
% 4.06/0.99  --sat_fm_prep                           false
% 4.06/0.99  --sat_fm_uc_incr                        true
% 4.06/0.99  --sat_out_model                         small
% 4.06/0.99  --sat_out_clauses                       false
% 4.06/0.99  
% 4.06/0.99  ------ QBF Options
% 4.06/0.99  
% 4.06/0.99  --qbf_mode                              false
% 4.06/0.99  --qbf_elim_univ                         false
% 4.06/0.99  --qbf_dom_inst                          none
% 4.06/0.99  --qbf_dom_pre_inst                      false
% 4.06/0.99  --qbf_sk_in                             false
% 4.06/0.99  --qbf_pred_elim                         true
% 4.06/0.99  --qbf_split                             512
% 4.06/0.99  
% 4.06/0.99  ------ BMC1 Options
% 4.06/0.99  
% 4.06/0.99  --bmc1_incremental                      false
% 4.06/0.99  --bmc1_axioms                           reachable_all
% 4.06/0.99  --bmc1_min_bound                        0
% 4.06/0.99  --bmc1_max_bound                        -1
% 4.06/0.99  --bmc1_max_bound_default                -1
% 4.06/0.99  --bmc1_symbol_reachability              true
% 4.06/0.99  --bmc1_property_lemmas                  false
% 4.06/0.99  --bmc1_k_induction                      false
% 4.06/0.99  --bmc1_non_equiv_states                 false
% 4.06/0.99  --bmc1_deadlock                         false
% 4.06/0.99  --bmc1_ucm                              false
% 4.06/0.99  --bmc1_add_unsat_core                   none
% 4.06/0.99  --bmc1_unsat_core_children              false
% 4.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.06/0.99  --bmc1_out_stat                         full
% 4.06/0.99  --bmc1_ground_init                      false
% 4.06/0.99  --bmc1_pre_inst_next_state              false
% 4.06/0.99  --bmc1_pre_inst_state                   false
% 4.06/0.99  --bmc1_pre_inst_reach_state             false
% 4.06/0.99  --bmc1_out_unsat_core                   false
% 4.06/0.99  --bmc1_aig_witness_out                  false
% 4.06/0.99  --bmc1_verbose                          false
% 4.06/0.99  --bmc1_dump_clauses_tptp                false
% 4.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.06/0.99  --bmc1_dump_file                        -
% 4.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.06/0.99  --bmc1_ucm_extend_mode                  1
% 4.06/0.99  --bmc1_ucm_init_mode                    2
% 4.06/0.99  --bmc1_ucm_cone_mode                    none
% 4.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.06/0.99  --bmc1_ucm_relax_model                  4
% 4.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.06/0.99  --bmc1_ucm_layered_model                none
% 4.06/0.99  --bmc1_ucm_max_lemma_size               10
% 4.06/0.99  
% 4.06/0.99  ------ AIG Options
% 4.06/0.99  
% 4.06/0.99  --aig_mode                              false
% 4.06/0.99  
% 4.06/0.99  ------ Instantiation Options
% 4.06/0.99  
% 4.06/0.99  --instantiation_flag                    true
% 4.06/0.99  --inst_sos_flag                         false
% 4.06/0.99  --inst_sos_phase                        true
% 4.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.06/0.99  --inst_lit_sel_side                     none
% 4.06/0.99  --inst_solver_per_active                1400
% 4.06/0.99  --inst_solver_calls_frac                1.
% 4.06/0.99  --inst_passive_queue_type               priority_queues
% 4.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.06/0.99  --inst_passive_queues_freq              [25;2]
% 4.06/0.99  --inst_dismatching                      true
% 4.06/0.99  --inst_eager_unprocessed_to_passive     true
% 4.06/0.99  --inst_prop_sim_given                   true
% 4.06/0.99  --inst_prop_sim_new                     false
% 4.06/0.99  --inst_subs_new                         false
% 4.06/0.99  --inst_eq_res_simp                      false
% 4.06/0.99  --inst_subs_given                       false
% 4.06/0.99  --inst_orphan_elimination               true
% 4.06/0.99  --inst_learning_loop_flag               true
% 4.06/0.99  --inst_learning_start                   3000
% 4.06/0.99  --inst_learning_factor                  2
% 4.06/0.99  --inst_start_prop_sim_after_learn       3
% 4.06/0.99  --inst_sel_renew                        solver
% 4.06/0.99  --inst_lit_activity_flag                true
% 4.06/0.99  --inst_restr_to_given                   false
% 4.06/0.99  --inst_activity_threshold               500
% 4.06/0.99  --inst_out_proof                        true
% 4.06/0.99  
% 4.06/0.99  ------ Resolution Options
% 4.06/0.99  
% 4.06/0.99  --resolution_flag                       false
% 4.06/0.99  --res_lit_sel                           adaptive
% 4.06/0.99  --res_lit_sel_side                      none
% 4.06/0.99  --res_ordering                          kbo
% 4.06/0.99  --res_to_prop_solver                    active
% 4.06/0.99  --res_prop_simpl_new                    false
% 4.06/0.99  --res_prop_simpl_given                  true
% 4.06/0.99  --res_passive_queue_type                priority_queues
% 4.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.06/0.99  --res_passive_queues_freq               [15;5]
% 4.06/0.99  --res_forward_subs                      full
% 4.06/0.99  --res_backward_subs                     full
% 4.06/0.99  --res_forward_subs_resolution           true
% 4.06/0.99  --res_backward_subs_resolution          true
% 4.06/0.99  --res_orphan_elimination                true
% 4.06/0.99  --res_time_limit                        2.
% 4.06/0.99  --res_out_proof                         true
% 4.06/0.99  
% 4.06/0.99  ------ Superposition Options
% 4.06/0.99  
% 4.06/0.99  --superposition_flag                    true
% 4.06/0.99  --sup_passive_queue_type                priority_queues
% 4.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.06/0.99  --demod_completeness_check              fast
% 4.06/0.99  --demod_use_ground                      true
% 4.06/0.99  --sup_to_prop_solver                    passive
% 4.06/0.99  --sup_prop_simpl_new                    true
% 4.06/0.99  --sup_prop_simpl_given                  true
% 4.06/0.99  --sup_fun_splitting                     false
% 4.06/0.99  --sup_smt_interval                      50000
% 4.06/0.99  
% 4.06/0.99  ------ Superposition Simplification Setup
% 4.06/0.99  
% 4.06/0.99  --sup_indices_passive                   []
% 4.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.06/0.99  --sup_full_bw                           [BwDemod]
% 4.06/0.99  --sup_immed_triv                        [TrivRules]
% 4.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.06/0.99  --sup_immed_bw_main                     []
% 4.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.06/0.99  
% 4.06/0.99  ------ Combination Options
% 4.06/0.99  
% 4.06/0.99  --comb_res_mult                         3
% 4.06/0.99  --comb_sup_mult                         2
% 4.06/0.99  --comb_inst_mult                        10
% 4.06/0.99  
% 4.06/0.99  ------ Debug Options
% 4.06/0.99  
% 4.06/0.99  --dbg_backtrace                         false
% 4.06/0.99  --dbg_dump_prop_clauses                 false
% 4.06/0.99  --dbg_dump_prop_clauses_file            -
% 4.06/0.99  --dbg_out_stat                          false
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  ------ Proving...
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  % SZS status Theorem for theBenchmark.p
% 4.06/0.99  
% 4.06/0.99   Resolution empty clause
% 4.06/0.99  
% 4.06/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  fof(f2,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f29,plain,(
% 4.06/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.06/0.99    inference(nnf_transformation,[],[f2])).
% 4.06/0.99  
% 4.06/0.99  fof(f30,plain,(
% 4.06/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.06/0.99    inference(flattening,[],[f29])).
% 4.06/0.99  
% 4.06/0.99  fof(f31,plain,(
% 4.06/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.06/0.99    inference(rectify,[],[f30])).
% 4.06/0.99  
% 4.06/0.99  fof(f32,plain,(
% 4.06/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f33,plain,(
% 4.06/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 4.06/0.99  
% 4.06/0.99  fof(f43,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f33])).
% 4.06/0.99  
% 4.06/0.99  fof(f11,axiom,(
% 4.06/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f53,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f11])).
% 4.06/0.99  
% 4.06/0.99  fof(f15,axiom,(
% 4.06/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f57,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f15])).
% 4.06/0.99  
% 4.06/0.99  fof(f12,axiom,(
% 4.06/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f54,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f12])).
% 4.06/0.99  
% 4.06/0.99  fof(f13,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f55,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f13])).
% 4.06/0.99  
% 4.06/0.99  fof(f14,axiom,(
% 4.06/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f56,plain,(
% 4.06/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f14])).
% 4.06/0.99  
% 4.06/0.99  fof(f62,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.06/0.99    inference(definition_unfolding,[],[f55,f56])).
% 4.06/0.99  
% 4.06/0.99  fof(f63,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.06/0.99    inference(definition_unfolding,[],[f54,f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f64,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 4.06/0.99    inference(definition_unfolding,[],[f57,f63])).
% 4.06/0.99  
% 4.06/0.99  fof(f65,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 4.06/0.99    inference(definition_unfolding,[],[f53,f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f68,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 4.06/0.99    inference(definition_unfolding,[],[f43,f65])).
% 4.06/0.99  
% 4.06/0.99  fof(f10,axiom,(
% 4.06/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f52,plain,(
% 4.06/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 4.06/0.99    inference(cnf_transformation,[],[f10])).
% 4.06/0.99  
% 4.06/0.99  fof(f9,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f51,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f9])).
% 4.06/0.99  
% 4.06/0.99  fof(f4,axiom,(
% 4.06/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f20,plain,(
% 4.06/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.06/0.99    inference(rectify,[],[f4])).
% 4.06/0.99  
% 4.06/0.99  fof(f46,plain,(
% 4.06/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.06/0.99    inference(cnf_transformation,[],[f20])).
% 4.06/0.99  
% 4.06/0.99  fof(f74,plain,(
% 4.06/0.99    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k3_enumset1(X0,X0,X0,X0,X0))) = X0) )),
% 4.06/0.99    inference(definition_unfolding,[],[f46,f65])).
% 4.06/0.99  
% 4.06/0.99  fof(f3,axiom,(
% 4.06/0.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f19,plain,(
% 4.06/0.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.06/0.99    inference(rectify,[],[f3])).
% 4.06/0.99  
% 4.06/0.99  fof(f45,plain,(
% 4.06/0.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.06/0.99    inference(cnf_transformation,[],[f19])).
% 4.06/0.99  
% 4.06/0.99  fof(f73,plain,(
% 4.06/0.99    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 4.06/0.99    inference(definition_unfolding,[],[f45,f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f17,conjecture,(
% 4.06/0.99    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f18,negated_conjecture,(
% 4.06/0.99    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2))),
% 4.06/0.99    inference(negated_conjecture,[],[f17])).
% 4.06/0.99  
% 4.06/0.99  fof(f23,plain,(
% 4.06/0.99    ? [X0,X1,X2,X3] : (k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 4.06/0.99    inference(ennf_transformation,[],[f18])).
% 4.06/0.99  
% 4.06/0.99  fof(f24,plain,(
% 4.06/0.99    ? [X0,X1,X2,X3] : (k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 4.06/0.99    inference(flattening,[],[f23])).
% 4.06/0.99  
% 4.06/0.99  fof(f34,plain,(
% 4.06/0.99    ? [X0,X1,X2,X3] : (k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k3_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)) != k2_zfmisc_1(sK2,sK4) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3))),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f35,plain,(
% 4.06/0.99    k3_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)) != k2_zfmisc_1(sK2,sK4) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3)),
% 4.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f34])).
% 4.06/0.99  
% 4.06/0.99  fof(f60,plain,(
% 4.06/0.99    r1_tarski(sK4,sK5)),
% 4.06/0.99    inference(cnf_transformation,[],[f35])).
% 4.06/0.99  
% 4.06/0.99  fof(f6,axiom,(
% 4.06/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f22,plain,(
% 4.06/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.06/0.99    inference(ennf_transformation,[],[f6])).
% 4.06/0.99  
% 4.06/0.99  fof(f48,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f22])).
% 4.06/0.99  
% 4.06/0.99  fof(f75,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 4.06/0.99    inference(definition_unfolding,[],[f48,f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f40,plain,(
% 4.06/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 4.06/0.99    inference(cnf_transformation,[],[f33])).
% 4.06/0.99  
% 4.06/0.99  fof(f71,plain,(
% 4.06/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) != X2) )),
% 4.06/0.99    inference(definition_unfolding,[],[f40,f65])).
% 4.06/0.99  
% 4.06/0.99  fof(f81,plain,(
% 4.06/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) )),
% 4.06/0.99    inference(equality_resolution,[],[f71])).
% 4.06/0.99  
% 4.06/0.99  fof(f8,axiom,(
% 4.06/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f50,plain,(
% 4.06/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.06/0.99    inference(cnf_transformation,[],[f8])).
% 4.06/0.99  
% 4.06/0.99  fof(f5,axiom,(
% 4.06/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f47,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f5])).
% 4.06/0.99  
% 4.06/0.99  fof(f66,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) )),
% 4.06/0.99    inference(definition_unfolding,[],[f47,f65])).
% 4.06/0.99  
% 4.06/0.99  fof(f77,plain,(
% 4.06/0.99    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)))) = X0) )),
% 4.06/0.99    inference(definition_unfolding,[],[f50,f66])).
% 4.06/0.99  
% 4.06/0.99  fof(f7,axiom,(
% 4.06/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f49,plain,(
% 4.06/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.06/0.99    inference(cnf_transformation,[],[f7])).
% 4.06/0.99  
% 4.06/0.99  fof(f76,plain,(
% 4.06/0.99    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 4.06/0.99    inference(definition_unfolding,[],[f49,f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f44,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f33])).
% 4.06/0.99  
% 4.06/0.99  fof(f67,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 4.06/0.99    inference(definition_unfolding,[],[f44,f65])).
% 4.06/0.99  
% 4.06/0.99  fof(f16,axiom,(
% 4.06/0.99    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f58,plain,(
% 4.06/0.99    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f16])).
% 4.06/0.99  
% 4.06/0.99  fof(f78,plain,(
% 4.06/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))) )),
% 4.06/0.99    inference(definition_unfolding,[],[f58,f65,f65,f65])).
% 4.06/0.99  
% 4.06/0.99  fof(f61,plain,(
% 4.06/0.99    k3_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)) != k2_zfmisc_1(sK2,sK4)),
% 4.06/0.99    inference(cnf_transformation,[],[f35])).
% 4.06/0.99  
% 4.06/0.99  fof(f79,plain,(
% 4.06/0.99    k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)),k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)))) != k2_zfmisc_1(sK2,sK4)),
% 4.06/0.99    inference(definition_unfolding,[],[f61,f65])).
% 4.06/0.99  
% 4.06/0.99  fof(f59,plain,(
% 4.06/0.99    r1_tarski(sK2,sK3)),
% 4.06/0.99    inference(cnf_transformation,[],[f35])).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4,plain,
% 4.06/0.99      ( r2_hidden(sK1(X0,X1,X2),X1)
% 4.06/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 4.06/0.99      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2 ),
% 4.06/0.99      inference(cnf_transformation,[],[f68]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_469,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2
% 4.06/0.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 4.06/0.99      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15,plain,
% 4.06/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 4.06/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_870,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_15,c_14]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_10,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k3_enumset1(X0,X0,X0,X0,X0))) = X0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_9,plain,
% 4.06/0.99      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_486,plain,
% 4.06/0.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_10,c_9,c_15]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_877,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_870,c_486]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1168,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_14,c_877]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1595,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k1_xboole_0) = X1 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_15,c_1168]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1719,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_877,c_1595]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2214,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_1719,c_14]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2242,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_2214,c_486]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2243,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_2242,c_14]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_8757,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = X2
% 4.06/0.99      | r2_hidden(sK1(X1,X0,X2),X2) = iProver_top
% 4.06/0.99      | r2_hidden(sK1(X1,X0,X2),X0) = iProver_top ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_469,c_2243]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_18,negated_conjecture,
% 4.06/0.99      ( r1_tarski(sK4,sK5) ),
% 4.06/0.99      inference(cnf_transformation,[],[f60]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_463,plain,
% 4.06/0.99      ( r1_tarski(sK4,sK5) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_11,plain,
% 4.06/0.99      ( ~ r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
% 4.06/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_464,plain,
% 4.06/0.99      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
% 4.06/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_854,plain,
% 4.06/0.99      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = sK5 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_463,c_464]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7,plain,
% 4.06/0.99      ( r2_hidden(X0,X1)
% 4.06/0.99      | ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))) ),
% 4.06/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_466,plain,
% 4.06/0.99      ( r2_hidden(X0,X1) = iProver_top
% 4.06/0.99      | r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2608,plain,
% 4.06/0.99      ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK4,sK5),sK5)) != iProver_top
% 4.06/0.99      | r2_hidden(X0,sK5) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_854,c_466]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_872,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1171,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_872,c_877]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_13,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)))) = X0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_12,plain,
% 4.06/0.99      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_497,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) = X0 ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_13,c_12]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_861,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) = X0 ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_14,c_497]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_866,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_861,c_15,c_486]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1186,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_1171,c_866]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1268,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_877,c_1186]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2617,plain,
% 4.06/0.99      ( r2_hidden(X0,sK4) != iProver_top | r2_hidden(X0,sK5) = iProver_top ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_2608,c_1268]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_8762,plain,
% 4.06/0.99      ( k5_xboole_0(sK4,k5_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,sK4)))) = X1
% 4.06/0.99      | r2_hidden(sK1(X0,sK4,X1),X1) = iProver_top
% 4.06/0.99      | r2_hidden(sK1(X0,sK4,X1),sK5) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_8757,c_2617]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_9606,plain,
% 4.06/0.99      ( k5_xboole_0(sK4,k5_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,sK4)))) = sK4
% 4.06/0.99      | r2_hidden(sK1(X0,sK4,sK4),sK5) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_8762,c_2617]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3,plain,
% 4.06/0.99      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 4.06/0.99      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 4.06/0.99      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 4.06/0.99      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2 ),
% 4.06/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_470,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2
% 4.06/0.99      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
% 4.06/0.99      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 4.06/0.99      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_10190,plain,
% 4.06/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = X2
% 4.06/0.99      | r2_hidden(sK1(X1,X0,X2),X1) != iProver_top
% 4.06/0.99      | r2_hidden(sK1(X1,X0,X2),X2) != iProver_top
% 4.06/0.99      | r2_hidden(sK1(X1,X0,X2),X0) != iProver_top ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_470,c_2243]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_10216,plain,
% 4.06/0.99      ( k5_xboole_0(sK4,k5_xboole_0(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) = sK4
% 4.06/0.99      | r2_hidden(sK1(sK5,sK4,sK4),sK4) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_9606,c_10190]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_11615,plain,
% 4.06/0.99      ( k5_xboole_0(sK4,k5_xboole_0(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) = sK4
% 4.06/0.99      | r2_hidden(sK1(sK5,sK4,sK4),sK4) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_8757,c_10216]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_11622,plain,
% 4.06/0.99      ( k5_xboole_0(sK4,k5_xboole_0(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) = sK4 ),
% 4.06/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_11615,c_10216]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_16,plain,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X2),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)))) ),
% 4.06/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_17,negated_conjecture,
% 4.06/0.99      ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)),k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK3,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
% 4.06/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_547,plain,
% 4.06/0.99      ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,sK3),k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3))),k5_xboole_0(k5_xboole_0(sK5,sK4),k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_16,c_17]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_862,plain,
% 4.06/0.99      ( k2_zfmisc_1(k5_xboole_0(sK2,k5_xboole_0(sK3,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)))),k5_xboole_0(k5_xboole_0(sK5,sK4),k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_14,c_547]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_19,negated_conjecture,
% 4.06/0.99      ( r1_tarski(sK2,sK3) ),
% 4.06/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_462,plain,
% 4.06/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_855,plain,
% 4.06/0.99      ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)) = sK3 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_462,c_464]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1141,plain,
% 4.06/0.99      ( k2_zfmisc_1(k5_xboole_0(sK2,k5_xboole_0(sK3,sK3)),k5_xboole_0(k5_xboole_0(sK5,sK4),k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_862,c_855]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1142,plain,
% 4.06/0.99      ( k2_zfmisc_1(sK2,k5_xboole_0(k5_xboole_0(sK5,sK4),k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)))) != k2_zfmisc_1(sK2,sK4) ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_1141,c_15,c_866]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5407,plain,
% 4.06/0.99      ( k2_zfmisc_1(sK2,k5_xboole_0(sK4,k5_xboole_0(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4))))) != k2_zfmisc_1(sK2,sK4) ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_2243,c_1142]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_11987,plain,
% 4.06/0.99      ( k2_zfmisc_1(sK2,sK4) != k2_zfmisc_1(sK2,sK4) ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_11622,c_5407]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_11988,plain,
% 4.06/0.99      ( $false ),
% 4.06/0.99      inference(equality_resolution_simp,[status(thm)],[c_11987]) ).
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  ------                               Statistics
% 4.06/0.99  
% 4.06/0.99  ------ General
% 4.06/0.99  
% 4.06/0.99  abstr_ref_over_cycles:                  0
% 4.06/0.99  abstr_ref_under_cycles:                 0
% 4.06/0.99  gc_basic_clause_elim:                   0
% 4.06/0.99  forced_gc_time:                         0
% 4.06/0.99  parsing_time:                           0.009
% 4.06/0.99  unif_index_cands_time:                  0.
% 4.06/0.99  unif_index_add_time:                    0.
% 4.06/0.99  orderings_time:                         0.
% 4.06/0.99  out_proof_time:                         0.007
% 4.06/0.99  total_time:                             0.347
% 4.06/0.99  num_of_symbols:                         44
% 4.06/0.99  num_of_terms:                           15632
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing
% 4.06/0.99  
% 4.06/0.99  num_of_splits:                          0
% 4.06/0.99  num_of_split_atoms:                     0
% 4.06/0.99  num_of_reused_defs:                     0
% 4.06/0.99  num_eq_ax_congr_red:                    10
% 4.06/0.99  num_of_sem_filtered_clauses:            1
% 4.06/0.99  num_of_subtypes:                        0
% 4.06/0.99  monotx_restored_types:                  0
% 4.06/0.99  sat_num_of_epr_types:                   0
% 4.06/0.99  sat_num_of_non_cyclic_types:            0
% 4.06/0.99  sat_guarded_non_collapsed_types:        0
% 4.06/0.99  num_pure_diseq_elim:                    0
% 4.06/0.99  simp_replaced_by:                       0
% 4.06/0.99  res_preprocessed:                       77
% 4.06/0.99  prep_upred:                             0
% 4.06/0.99  prep_unflattend:                        12
% 4.06/0.99  smt_new_axioms:                         0
% 4.06/0.99  pred_elim_cands:                        2
% 4.06/0.99  pred_elim:                              0
% 4.06/0.99  pred_elim_cl:                           0
% 4.06/0.99  pred_elim_cycles:                       1
% 4.06/0.99  merged_defs:                            0
% 4.06/0.99  merged_defs_ncl:                        0
% 4.06/0.99  bin_hyper_res:                          0
% 4.06/0.99  prep_cycles:                            3
% 4.06/0.99  pred_elim_time:                         0.002
% 4.06/0.99  splitting_time:                         0.
% 4.06/0.99  sem_filter_time:                        0.
% 4.06/0.99  monotx_time:                            0.
% 4.06/0.99  subtype_inf_time:                       0.
% 4.06/0.99  
% 4.06/0.99  ------ Problem properties
% 4.06/0.99  
% 4.06/0.99  clauses:                                20
% 4.06/0.99  conjectures:                            3
% 4.06/0.99  epr:                                    3
% 4.06/0.99  horn:                                   17
% 4.06/0.99  ground:                                 3
% 4.06/0.99  unary:                                  10
% 4.06/0.99  binary:                                 5
% 4.06/0.99  lits:                                   36
% 4.06/0.99  lits_eq:                                12
% 4.06/0.99  fd_pure:                                0
% 4.06/0.99  fd_pseudo:                              0
% 4.06/0.99  fd_cond:                                0
% 4.06/0.99  fd_pseudo_cond:                         3
% 4.06/0.99  ac_symbols:                             1
% 4.06/0.99  
% 4.06/0.99  ------ Propositional Solver
% 4.06/0.99  
% 4.06/0.99  prop_solver_calls:                      25
% 4.06/0.99  prop_fast_solver_calls:                 503
% 4.06/0.99  smt_solver_calls:                       0
% 4.06/0.99  smt_fast_solver_calls:                  0
% 4.06/0.99  prop_num_of_clauses:                    3139
% 4.06/0.99  prop_preprocess_simplified:             5784
% 4.06/0.99  prop_fo_subsumed:                       0
% 4.06/0.99  prop_solver_time:                       0.
% 4.06/0.99  smt_solver_time:                        0.
% 4.06/0.99  smt_fast_solver_time:                   0.
% 4.06/0.99  prop_fast_solver_time:                  0.
% 4.06/0.99  prop_unsat_core_time:                   0.
% 4.06/0.99  
% 4.06/0.99  ------ QBF
% 4.06/0.99  
% 4.06/0.99  qbf_q_res:                              0
% 4.06/0.99  qbf_num_tautologies:                    0
% 4.06/0.99  qbf_prep_cycles:                        0
% 4.06/0.99  
% 4.06/0.99  ------ BMC1
% 4.06/0.99  
% 4.06/0.99  bmc1_current_bound:                     -1
% 4.06/0.99  bmc1_last_solved_bound:                 -1
% 4.06/0.99  bmc1_unsat_core_size:                   -1
% 4.06/0.99  bmc1_unsat_core_parents_size:           -1
% 4.06/0.99  bmc1_merge_next_fun:                    0
% 4.06/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.06/0.99  
% 4.06/0.99  ------ Instantiation
% 4.06/0.99  
% 4.06/0.99  inst_num_of_clauses:                    775
% 4.06/0.99  inst_num_in_passive:                    214
% 4.06/0.99  inst_num_in_active:                     324
% 4.06/0.99  inst_num_in_unprocessed:                237
% 4.06/0.99  inst_num_of_loops:                      430
% 4.06/0.99  inst_num_of_learning_restarts:          0
% 4.06/0.99  inst_num_moves_active_passive:          102
% 4.06/0.99  inst_lit_activity:                      0
% 4.06/0.99  inst_lit_activity_moves:                0
% 4.06/0.99  inst_num_tautologies:                   0
% 4.06/0.99  inst_num_prop_implied:                  0
% 4.06/0.99  inst_num_existing_simplified:           0
% 4.06/0.99  inst_num_eq_res_simplified:             0
% 4.06/0.99  inst_num_child_elim:                    0
% 4.06/0.99  inst_num_of_dismatching_blockings:      161
% 4.06/0.99  inst_num_of_non_proper_insts:           479
% 4.06/0.99  inst_num_of_duplicates:                 0
% 4.06/0.99  inst_inst_num_from_inst_to_res:         0
% 4.06/0.99  inst_dismatching_checking_time:         0.
% 4.06/0.99  
% 4.06/0.99  ------ Resolution
% 4.06/0.99  
% 4.06/0.99  res_num_of_clauses:                     0
% 4.06/0.99  res_num_in_passive:                     0
% 4.06/0.99  res_num_in_active:                      0
% 4.06/0.99  res_num_of_loops:                       80
% 4.06/0.99  res_forward_subset_subsumed:            39
% 4.06/0.99  res_backward_subset_subsumed:           0
% 4.06/0.99  res_forward_subsumed:                   0
% 4.06/0.99  res_backward_subsumed:                  0
% 4.06/0.99  res_forward_subsumption_resolution:     0
% 4.06/0.99  res_backward_subsumption_resolution:    0
% 4.06/0.99  res_clause_to_clause_subsumption:       11261
% 4.06/0.99  res_orphan_elimination:                 0
% 4.06/0.99  res_tautology_del:                      43
% 4.06/0.99  res_num_eq_res_simplified:              0
% 4.06/0.99  res_num_sel_changes:                    0
% 4.06/0.99  res_moves_from_active_to_pass:          0
% 4.06/0.99  
% 4.06/0.99  ------ Superposition
% 4.06/0.99  
% 4.06/0.99  sup_time_total:                         0.
% 4.06/0.99  sup_time_generating:                    0.
% 4.06/0.99  sup_time_sim_full:                      0.
% 4.06/0.99  sup_time_sim_immed:                     0.
% 4.06/0.99  
% 4.06/0.99  sup_num_of_clauses:                     629
% 4.06/0.99  sup_num_in_active:                      65
% 4.06/0.99  sup_num_in_passive:                     564
% 4.06/0.99  sup_num_of_loops:                       85
% 4.06/0.99  sup_fw_superposition:                   1927
% 4.06/0.99  sup_bw_superposition:                   1196
% 4.06/0.99  sup_immediate_simplified:               1089
% 4.06/0.99  sup_given_eliminated:                   5
% 4.06/0.99  comparisons_done:                       0
% 4.06/0.99  comparisons_avoided:                    0
% 4.06/0.99  
% 4.06/0.99  ------ Simplifications
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  sim_fw_subset_subsumed:                 0
% 4.06/0.99  sim_bw_subset_subsumed:                 4
% 4.06/0.99  sim_fw_subsumed:                        64
% 4.06/0.99  sim_bw_subsumed:                        4
% 4.06/0.99  sim_fw_subsumption_res:                 4
% 4.06/0.99  sim_bw_subsumption_res:                 0
% 4.06/0.99  sim_tautology_del:                      24
% 4.06/0.99  sim_eq_tautology_del:                   208
% 4.06/0.99  sim_eq_res_simp:                        14
% 4.06/0.99  sim_fw_demodulated:                     905
% 4.06/0.99  sim_bw_demodulated:                     39
% 4.06/0.99  sim_light_normalised:                   339
% 4.06/0.99  sim_joinable_taut:                      81
% 4.06/0.99  sim_joinable_simp:                      0
% 4.06/0.99  sim_ac_normalised:                      0
% 4.06/0.99  sim_smt_subsumption:                    0
% 4.06/0.99  
%------------------------------------------------------------------------------
