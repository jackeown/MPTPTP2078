%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:46 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  155 (2041 expanded)
%              Number of clauses        :   83 ( 382 expanded)
%              Number of leaves         :   23 ( 589 expanded)
%              Depth                    :   26
%              Number of atoms          :  347 (2736 expanded)
%              Number of equality atoms :  168 (1954 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
     => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
          & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
       => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f27,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f28,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
        & r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ~ r2_hidden(sK3,k2_zfmisc_1(k3_xboole_0(sK4,sK6),k3_xboole_0(sK5,sK7)))
      & r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
      & r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r2_hidden(sK3,k2_zfmisc_1(k3_xboole_0(sK4,sK6),k3_xboole_0(sK5,sK7)))
    & r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
    & r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f28,f39])).

fof(f75,plain,(
    r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK1(X0),sK2(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f37])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ~ r2_hidden(sK3,k2_zfmisc_1(k3_xboole_0(sK4,sK6),k3_xboole_0(sK5,sK7))) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f81])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f82])).

fof(f99,plain,(
    ~ r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK4,sK6),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))),k5_xboole_0(k5_xboole_0(sK5,sK7),k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) ),
    inference(definition_unfolding,[],[f76,f83,f83])).

fof(f74,plain,(
    r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f48,f83])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f82])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

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
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != X2 ) ),
    inference(definition_unfolding,[],[f42,f84])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ) ),
    inference(equality_resolution,[],[f89])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_508,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_500,plain,
    ( r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_505,plain,
    ( k4_tarski(sK1(X0),sK2(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10634,plain,
    ( k4_tarski(sK1(sK3),sK2(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_500,c_505])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_504,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12610,plain,
    ( r2_hidden(sK2(sK3),X0) != iProver_top
    | r2_hidden(sK1(sK3),X1) != iProver_top
    | r2_hidden(sK3,k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10634,c_504])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK4,sK6),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))),k5_xboole_0(k5_xboole_0(sK5,sK7),k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_501,plain,
    ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK4,sK6),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))),k5_xboole_0(k5_xboole_0(sK5,sK7),k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_774,plain,
    ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))),k5_xboole_0(k5_xboole_0(sK5,sK7),k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12,c_501])).

cnf(c_866,plain,
    ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))),k5_xboole_0(sK5,k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_774])).

cnf(c_14421,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) != iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12610,c_866])).

cnf(c_22424,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
    | r2_hidden(sK2(sK3),sK5) != iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_508,c_14421])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_27,plain,
    ( r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_675,plain,
    ( ~ r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
    | k4_tarski(sK1(sK3),sK2(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_204,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1136,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_209,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_734,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,k2_zfmisc_1(sK4,sK5))
    | X1 != k2_zfmisc_1(sK4,sK5)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_1135,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK3,k2_zfmisc_1(sK4,sK5))
    | X0 != sK3
    | k2_zfmisc_1(sK4,sK5) != k2_zfmisc_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_2566,plain,
    ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK3,k2_zfmisc_1(sK4,sK5))
    | k2_zfmisc_1(sK4,sK5) != k2_zfmisc_1(sK4,sK5)
    | k4_tarski(sK1(sK3),sK2(sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_2567,plain,
    ( k2_zfmisc_1(sK4,sK5) != k2_zfmisc_1(sK4,sK5)
    | k4_tarski(sK1(sK3),sK2(sK3)) != sK3
    | r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2566])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_7440,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(sK2(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_7441,plain,
    ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7440])).

cnf(c_23006,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22424,c_27,c_25,c_675,c_1136,c_2567,c_7441])).

cnf(c_23012,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top
    | r2_hidden(sK1(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_508,c_23006])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_777,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_13,c_12])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_538,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_6,c_13])).

cnf(c_784,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_777,c_538])).

cnf(c_2057,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_784])).

cnf(c_779,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_13])).

cnf(c_2060,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_779,c_784])).

cnf(c_2097,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2057,c_2060])).

cnf(c_2249,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2097,c_784])).

cnf(c_2259,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_2249])).

cnf(c_1707,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_779])).

cnf(c_2071,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_784,c_1707])).

cnf(c_2914,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2071,c_2097])).

cnf(c_3173,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_2914,c_12])).

cnf(c_3198,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_3173,c_538])).

cnf(c_3199,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_3198,c_12])).

cnf(c_7771,plain,
    ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))),k5_xboole_0(sK7,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3199,c_774])).

cnf(c_9062,plain,
    ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2259,c_7771])).

cnf(c_14424,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7))) != iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12610,c_9062])).

cnf(c_22425,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7))) != iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top
    | r2_hidden(sK1(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_508,c_14424])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7443,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(sK1(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_7444,plain,
    ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(sK1(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7443])).

cnf(c_23471,plain,
    ( r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top
    | r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22425,c_27,c_25,c_675,c_1136,c_2567,c_7444])).

cnf(c_23472,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7))) != iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_23471])).

cnf(c_23478,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) != iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2249,c_23472])).

cnf(c_23813,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
    | r2_hidden(sK2(sK3),sK5) != iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_508,c_23478])).

cnf(c_24007,plain,
    ( r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top
    | r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23012,c_27,c_25,c_675,c_1136,c_2567,c_7444])).

cnf(c_24008,plain,
    ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_24007])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_511,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2067,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
    inference(superposition,[status(thm)],[c_784,c_12])).

cnf(c_2076,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(light_normalisation,[status(thm)],[c_2067,c_12])).

cnf(c_3414,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_2076,c_784])).

cnf(c_35311,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_511,c_3199,c_3414])).

cnf(c_35319,plain,
    ( r2_hidden(sK2(sK3),sK7) != iProver_top
    | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_24008,c_35311])).

cnf(c_28,plain,
    ( r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1099,plain,
    ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_729,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
    | X1 != k2_zfmisc_1(sK6,sK7)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_1098,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7))
    | ~ r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
    | X0 != sK3
    | k2_zfmisc_1(sK6,sK7) != k2_zfmisc_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_2531,plain,
    ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7))
    | ~ r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
    | k2_zfmisc_1(sK6,sK7) != k2_zfmisc_1(sK6,sK7)
    | k4_tarski(sK1(sK3),sK2(sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_2532,plain,
    ( k2_zfmisc_1(sK6,sK7) != k2_zfmisc_1(sK6,sK7)
    | k4_tarski(sK1(sK3),sK2(sK3)) != sK3
    | r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2531])).

cnf(c_6628,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7))
    | r2_hidden(sK2(sK3),sK7) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6629,plain,
    ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7)) != iProver_top
    | r2_hidden(sK2(sK3),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6628])).

cnf(c_40091,plain,
    ( r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35319,c_25,c_28,c_675,c_1099,c_2532,c_6629])).

cnf(c_40099,plain,
    ( r2_hidden(sK1(sK3),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_40091,c_35311])).

cnf(c_6631,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7))
    | r2_hidden(sK1(sK3),sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_6632,plain,
    ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7)) != iProver_top
    | r2_hidden(sK1(sK3),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6631])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_40099,c_6632,c_2532,c_1099,c_675,c_28,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:48:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.74/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.49  
% 7.74/1.49  ------  iProver source info
% 7.74/1.49  
% 7.74/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.49  git: non_committed_changes: false
% 7.74/1.49  git: last_make_outside_of_git: false
% 7.74/1.49  
% 7.74/1.49  ------ 
% 7.74/1.49  ------ Parsing...
% 7.74/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.49  ------ Proving...
% 7.74/1.49  ------ Problem Properties 
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  clauses                                 27
% 7.74/1.49  conjectures                             3
% 7.74/1.49  EPR                                     0
% 7.74/1.49  Horn                                    20
% 7.74/1.49  unary                                   13
% 7.74/1.49  binary                                  5
% 7.74/1.49  lits                                    51
% 7.74/1.49  lits eq                                 14
% 7.74/1.49  fd_pure                                 0
% 7.74/1.49  fd_pseudo                               0
% 7.74/1.49  fd_cond                                 0
% 7.74/1.49  fd_pseudo_cond                          3
% 7.74/1.49  AC symbols                              0
% 7.74/1.49  
% 7.74/1.49  ------ Input Options Time Limit: Unbounded
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  ------ 
% 7.74/1.49  Current options:
% 7.74/1.49  ------ 
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  ------ Proving...
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  % SZS status Theorem for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  fof(f4,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f25,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 7.74/1.49    inference(ennf_transformation,[],[f4])).
% 7.74/1.49  
% 7.74/1.49  fof(f34,plain,(
% 7.74/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 7.74/1.49    inference(nnf_transformation,[],[f25])).
% 7.74/1.49  
% 7.74/1.49  fof(f51,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f34])).
% 7.74/1.49  
% 7.74/1.49  fof(f21,conjecture,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f22,negated_conjecture,(
% 7.74/1.49    ~! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 7.74/1.49    inference(negated_conjecture,[],[f21])).
% 7.74/1.49  
% 7.74/1.49  fof(f27,plain,(
% 7.74/1.49    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & (r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))))),
% 7.74/1.49    inference(ennf_transformation,[],[f22])).
% 7.74/1.49  
% 7.74/1.49  fof(f28,plain,(
% 7.74/1.49    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.74/1.49    inference(flattening,[],[f27])).
% 7.74/1.49  
% 7.74/1.49  fof(f39,plain,(
% 7.74/1.49    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => (~r2_hidden(sK3,k2_zfmisc_1(k3_xboole_0(sK4,sK6),k3_xboole_0(sK5,sK7))) & r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) & r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)))),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f40,plain,(
% 7.74/1.49    ~r2_hidden(sK3,k2_zfmisc_1(k3_xboole_0(sK4,sK6),k3_xboole_0(sK5,sK7))) & r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) & r2_hidden(sK3,k2_zfmisc_1(sK4,sK5))),
% 7.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f28,f39])).
% 7.74/1.49  
% 7.74/1.49  fof(f75,plain,(
% 7.74/1.49    r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))),
% 7.74/1.49    inference(cnf_transformation,[],[f40])).
% 7.74/1.49  
% 7.74/1.49  fof(f15,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f26,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.74/1.49    inference(ennf_transformation,[],[f15])).
% 7.74/1.49  
% 7.74/1.49  fof(f35,plain,(
% 7.74/1.49    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK1(X0),sK2(X0)) = X0)),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f36,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f63,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f36])).
% 7.74/1.49  
% 7.74/1.49  fof(f17,axiom,(
% 7.74/1.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f37,plain,(
% 7.74/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.74/1.49    inference(nnf_transformation,[],[f17])).
% 7.74/1.49  
% 7.74/1.49  fof(f38,plain,(
% 7.74/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.74/1.49    inference(flattening,[],[f37])).
% 7.74/1.49  
% 7.74/1.49  fof(f67,plain,(
% 7.74/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f38])).
% 7.74/1.49  
% 7.74/1.49  fof(f6,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f54,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f6])).
% 7.74/1.49  
% 7.74/1.49  fof(f76,plain,(
% 7.74/1.49    ~r2_hidden(sK3,k2_zfmisc_1(k3_xboole_0(sK4,sK6),k3_xboole_0(sK5,sK7)))),
% 7.74/1.49    inference(cnf_transformation,[],[f40])).
% 7.74/1.49  
% 7.74/1.49  fof(f8,axiom,(
% 7.74/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f56,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f8])).
% 7.74/1.49  
% 7.74/1.49  fof(f16,axiom,(
% 7.74/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f64,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f16])).
% 7.74/1.49  
% 7.74/1.49  fof(f9,axiom,(
% 7.74/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f57,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f9])).
% 7.74/1.49  
% 7.74/1.49  fof(f10,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f58,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f10])).
% 7.74/1.49  
% 7.74/1.49  fof(f11,axiom,(
% 7.74/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f59,plain,(
% 7.74/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f11])).
% 7.74/1.49  
% 7.74/1.49  fof(f12,axiom,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f60,plain,(
% 7.74/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f12])).
% 7.74/1.49  
% 7.74/1.49  fof(f13,axiom,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f61,plain,(
% 7.74/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f13])).
% 7.74/1.49  
% 7.74/1.49  fof(f14,axiom,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f62,plain,(
% 7.74/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f14])).
% 7.74/1.49  
% 7.74/1.49  fof(f77,plain,(
% 7.74/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.74/1.49    inference(definition_unfolding,[],[f61,f62])).
% 7.74/1.49  
% 7.74/1.49  fof(f78,plain,(
% 7.74/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.74/1.49    inference(definition_unfolding,[],[f60,f77])).
% 7.74/1.49  
% 7.74/1.49  fof(f79,plain,(
% 7.74/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.74/1.49    inference(definition_unfolding,[],[f59,f78])).
% 7.74/1.49  
% 7.74/1.49  fof(f80,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.74/1.49    inference(definition_unfolding,[],[f58,f79])).
% 7.74/1.49  
% 7.74/1.49  fof(f81,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.74/1.49    inference(definition_unfolding,[],[f57,f80])).
% 7.74/1.49  
% 7.74/1.49  fof(f82,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.74/1.49    inference(definition_unfolding,[],[f64,f81])).
% 7.74/1.49  
% 7.74/1.49  fof(f83,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.74/1.49    inference(definition_unfolding,[],[f56,f82])).
% 7.74/1.49  
% 7.74/1.49  fof(f99,plain,(
% 7.74/1.49    ~r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK4,sK6),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))),k5_xboole_0(k5_xboole_0(sK5,sK7),k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))))),
% 7.74/1.49    inference(definition_unfolding,[],[f76,f83,f83])).
% 7.74/1.49  
% 7.74/1.49  fof(f74,plain,(
% 7.74/1.49    r2_hidden(sK3,k2_zfmisc_1(sK4,sK5))),
% 7.74/1.49    inference(cnf_transformation,[],[f40])).
% 7.74/1.49  
% 7.74/1.49  fof(f66,plain,(
% 7.74/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f38])).
% 7.74/1.49  
% 7.74/1.49  fof(f7,axiom,(
% 7.74/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f55,plain,(
% 7.74/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.74/1.49    inference(cnf_transformation,[],[f7])).
% 7.74/1.49  
% 7.74/1.49  fof(f3,axiom,(
% 7.74/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f24,plain,(
% 7.74/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.74/1.49    inference(rectify,[],[f3])).
% 7.74/1.49  
% 7.74/1.49  fof(f48,plain,(
% 7.74/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.74/1.49    inference(cnf_transformation,[],[f24])).
% 7.74/1.49  
% 7.74/1.49  fof(f92,plain,(
% 7.74/1.49    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 7.74/1.49    inference(definition_unfolding,[],[f48,f83])).
% 7.74/1.49  
% 7.74/1.49  fof(f2,axiom,(
% 7.74/1.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f23,plain,(
% 7.74/1.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.74/1.49    inference(rectify,[],[f2])).
% 7.74/1.49  
% 7.74/1.49  fof(f47,plain,(
% 7.74/1.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.74/1.49    inference(cnf_transformation,[],[f23])).
% 7.74/1.49  
% 7.74/1.49  fof(f91,plain,(
% 7.74/1.49    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.74/1.49    inference(definition_unfolding,[],[f47,f82])).
% 7.74/1.49  
% 7.74/1.49  fof(f65,plain,(
% 7.74/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f38])).
% 7.74/1.49  
% 7.74/1.49  fof(f1,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f29,plain,(
% 7.74/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.74/1.49    inference(nnf_transformation,[],[f1])).
% 7.74/1.49  
% 7.74/1.49  fof(f30,plain,(
% 7.74/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.74/1.49    inference(flattening,[],[f29])).
% 7.74/1.49  
% 7.74/1.49  fof(f31,plain,(
% 7.74/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.74/1.49    inference(rectify,[],[f30])).
% 7.74/1.49  
% 7.74/1.49  fof(f32,plain,(
% 7.74/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f33,plain,(
% 7.74/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 7.74/1.49  
% 7.74/1.49  fof(f42,plain,(
% 7.74/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.74/1.49    inference(cnf_transformation,[],[f33])).
% 7.74/1.49  
% 7.74/1.49  fof(f5,axiom,(
% 7.74/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f53,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f5])).
% 7.74/1.49  
% 7.74/1.49  fof(f84,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 7.74/1.49    inference(definition_unfolding,[],[f53,f83])).
% 7.74/1.49  
% 7.74/1.49  fof(f89,plain,(
% 7.74/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != X2) )),
% 7.74/1.49    inference(definition_unfolding,[],[f42,f84])).
% 7.74/1.49  
% 7.74/1.49  fof(f101,plain,(
% 7.74/1.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 7.74/1.49    inference(equality_resolution,[],[f89])).
% 7.74/1.49  
% 7.74/1.49  cnf(c_9,plain,
% 7.74/1.49      ( ~ r2_hidden(X0,X1)
% 7.74/1.49      | r2_hidden(X0,X2)
% 7.74/1.49      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_508,plain,
% 7.74/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.74/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.74/1.49      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_25,negated_conjecture,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_500,plain,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_14,plain,
% 7.74/1.49      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 7.74/1.49      | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
% 7.74/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_505,plain,
% 7.74/1.49      ( k4_tarski(sK1(X0),sK2(X0)) = X0
% 7.74/1.49      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_10634,plain,
% 7.74/1.49      ( k4_tarski(sK1(sK3),sK2(sK3)) = sK3 ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_500,c_505]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_15,plain,
% 7.74/1.49      ( ~ r2_hidden(X0,X1)
% 7.74/1.49      | ~ r2_hidden(X2,X3)
% 7.74/1.49      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_504,plain,
% 7.74/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.74/1.49      | r2_hidden(X2,X3) != iProver_top
% 7.74/1.49      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_12610,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),X0) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),X1) != iProver_top
% 7.74/1.49      | r2_hidden(sK3,k2_zfmisc_1(X1,X0)) = iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_10634,c_504]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_12,plain,
% 7.74/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_24,negated_conjecture,
% 7.74/1.49      ( ~ r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK4,sK6),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))),k5_xboole_0(k5_xboole_0(sK5,sK7),k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) ),
% 7.74/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_501,plain,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK4,sK6),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))),k5_xboole_0(k5_xboole_0(sK5,sK7),k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_774,plain,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))),k5_xboole_0(k5_xboole_0(sK5,sK7),k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_12,c_501]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_866,plain,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))),k5_xboole_0(sK5,k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))))) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_12,c_774]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_14421,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))))) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_12610,c_866]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_22424,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
% 7.74/1.49      | r2_hidden(sK2(sK3),sK5) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))))) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_508,c_14421]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_26,negated_conjecture,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_27,plain,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_675,plain,
% 7.74/1.49      ( ~ r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
% 7.74/1.49      | k4_tarski(sK1(sK3),sK2(sK3)) = sK3 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_204,plain,( X0 = X0 ),theory(equality) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1136,plain,
% 7.74/1.49      ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK4,sK5) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_204]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_209,plain,
% 7.74/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.74/1.49      theory(equality) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_734,plain,
% 7.74/1.49      ( r2_hidden(X0,X1)
% 7.74/1.49      | ~ r2_hidden(sK3,k2_zfmisc_1(sK4,sK5))
% 7.74/1.49      | X1 != k2_zfmisc_1(sK4,sK5)
% 7.74/1.49      | X0 != sK3 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_209]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1135,plain,
% 7.74/1.49      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5))
% 7.74/1.49      | ~ r2_hidden(sK3,k2_zfmisc_1(sK4,sK5))
% 7.74/1.49      | X0 != sK3
% 7.74/1.49      | k2_zfmisc_1(sK4,sK5) != k2_zfmisc_1(sK4,sK5) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_734]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2566,plain,
% 7.74/1.49      ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5))
% 7.74/1.49      | ~ r2_hidden(sK3,k2_zfmisc_1(sK4,sK5))
% 7.74/1.49      | k2_zfmisc_1(sK4,sK5) != k2_zfmisc_1(sK4,sK5)
% 7.74/1.49      | k4_tarski(sK1(sK3),sK2(sK3)) != sK3 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_1135]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2567,plain,
% 7.74/1.49      ( k2_zfmisc_1(sK4,sK5) != k2_zfmisc_1(sK4,sK5)
% 7.74/1.49      | k4_tarski(sK1(sK3),sK2(sK3)) != sK3
% 7.74/1.49      | r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 7.74/1.49      | r2_hidden(sK3,k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_2566]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_16,plain,
% 7.74/1.49      ( r2_hidden(X0,X1)
% 7.74/1.49      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7440,plain,
% 7.74/1.49      ( ~ r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5))
% 7.74/1.49      | r2_hidden(sK2(sK3),sK5) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7441,plain,
% 7.74/1.49      ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 7.74/1.49      | r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_7440]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_23006,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))))) != iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_22424,c_27,c_25,c_675,c_1136,c_2567,c_7441]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_23012,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),sK4) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_508,c_23006]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_13,plain,
% 7.74/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.74/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_777,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_13,c_12]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7,plain,
% 7.74/1.49      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 7.74/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6,plain,
% 7.74/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.74/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_538,plain,
% 7.74/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_7,c_6,c_13]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_784,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_777,c_538]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2057,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_13,c_784]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_779,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_12,c_13]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2060,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_779,c_784]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2097,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_2057,c_2060]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2249,plain,
% 7.74/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_2097,c_784]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2259,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_12,c_2249]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1707,plain,
% 7.74/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_12,c_779]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2071,plain,
% 7.74/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_784,c_1707]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2914,plain,
% 7.74/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_2071,c_2097]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3173,plain,
% 7.74/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_2914,c_12]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3198,plain,
% 7.74/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_3173,c_538]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3199,plain,
% 7.74/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_3198,c_12]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7771,plain,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))),k5_xboole_0(sK7,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))))) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_3199,c_774]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_9062,plain,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7)))) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_2259,c_7771]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_14424,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7))) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK4,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6))))) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_12610,c_9062]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_22425,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7))) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),sK4) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_508,c_14424]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_17,plain,
% 7.74/1.49      ( r2_hidden(X0,X1)
% 7.74/1.49      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7443,plain,
% 7.74/1.49      ( ~ r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5))
% 7.74/1.49      | r2_hidden(sK1(sK3),sK4) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7444,plain,
% 7.74/1.49      ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),sK4) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_7443]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_23471,plain,
% 7.74/1.49      ( r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top
% 7.74/1.49      | r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7))) != iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_22425,c_27,c_25,c_675,c_1136,c_2567,c_7444]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_23472,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)),sK7))) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
% 7.74/1.49      inference(renaming,[status(thm)],[c_23471]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_23478,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK5,k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7))))) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_2249,c_23472]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_23813,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
% 7.74/1.49      | r2_hidden(sK2(sK3),sK5) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_508,c_23478]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_24007,plain,
% 7.74/1.49      ( r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top
% 7.74/1.49      | r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_23012,c_27,c_25,c_675,c_1136,c_2567,c_7444]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_24008,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),k5_xboole_0(sK7,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK7)))) = iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
% 7.74/1.49      inference(renaming,[status(thm)],[c_24007]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4,plain,
% 7.74/1.49      ( ~ r2_hidden(X0,X1)
% 7.74/1.49      | ~ r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) ),
% 7.74/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_511,plain,
% 7.74/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.74/1.49      | r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2067,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_784,c_12]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2076,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_2067,c_12]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3414,plain,
% 7.74/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_2076,c_784]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_35311,plain,
% 7.74/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.74/1.49      | r2_hidden(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_511,c_3199,c_3414]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_35319,plain,
% 7.74/1.49      ( r2_hidden(sK2(sK3),sK7) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_24008,c_35311]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_28,plain,
% 7.74/1.49      ( r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1099,plain,
% 7.74/1.49      ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK6,sK7) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_204]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_729,plain,
% 7.74/1.49      ( r2_hidden(X0,X1)
% 7.74/1.49      | ~ r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
% 7.74/1.49      | X1 != k2_zfmisc_1(sK6,sK7)
% 7.74/1.49      | X0 != sK3 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_209]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1098,plain,
% 7.74/1.49      ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7))
% 7.74/1.49      | ~ r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
% 7.74/1.49      | X0 != sK3
% 7.74/1.49      | k2_zfmisc_1(sK6,sK7) != k2_zfmisc_1(sK6,sK7) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_729]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2531,plain,
% 7.74/1.49      ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7))
% 7.74/1.49      | ~ r2_hidden(sK3,k2_zfmisc_1(sK6,sK7))
% 7.74/1.49      | k2_zfmisc_1(sK6,sK7) != k2_zfmisc_1(sK6,sK7)
% 7.74/1.49      | k4_tarski(sK1(sK3),sK2(sK3)) != sK3 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_1098]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2532,plain,
% 7.74/1.49      ( k2_zfmisc_1(sK6,sK7) != k2_zfmisc_1(sK6,sK7)
% 7.74/1.49      | k4_tarski(sK1(sK3),sK2(sK3)) != sK3
% 7.74/1.49      | r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7)) = iProver_top
% 7.74/1.49      | r2_hidden(sK3,k2_zfmisc_1(sK6,sK7)) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_2531]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6628,plain,
% 7.74/1.49      ( ~ r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7))
% 7.74/1.49      | r2_hidden(sK2(sK3),sK7) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6629,plain,
% 7.74/1.49      ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7)) != iProver_top
% 7.74/1.49      | r2_hidden(sK2(sK3),sK7) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_6628]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_40091,plain,
% 7.74/1.49      ( r2_hidden(sK1(sK3),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK6)))) = iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_35319,c_25,c_28,c_675,c_1099,c_2532,c_6629]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_40099,plain,
% 7.74/1.49      ( r2_hidden(sK1(sK3),sK6) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_40091,c_35311]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6631,plain,
% 7.74/1.49      ( ~ r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7))
% 7.74/1.49      | r2_hidden(sK1(sK3),sK6) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6632,plain,
% 7.74/1.49      ( r2_hidden(k4_tarski(sK1(sK3),sK2(sK3)),k2_zfmisc_1(sK6,sK7)) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(sK3),sK6) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_6631]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(contradiction,plain,
% 7.74/1.49      ( $false ),
% 7.74/1.49      inference(minisat,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_40099,c_6632,c_2532,c_1099,c_675,c_28,c_25]) ).
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  ------                               Statistics
% 7.74/1.49  
% 7.74/1.49  ------ Selected
% 7.74/1.49  
% 7.74/1.49  total_time:                             0.996
% 7.74/1.49  
%------------------------------------------------------------------------------
