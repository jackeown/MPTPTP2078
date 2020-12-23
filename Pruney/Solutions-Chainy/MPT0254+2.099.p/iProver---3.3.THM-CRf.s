%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:03 EST 2020

% Result     : Theorem 27.36s
% Output     : CNFRefutation 27.36s
% Verified   : 
% Statistics : Number of formulae       :  152 (1438 expanded)
%              Number of clauses        :   76 ( 400 expanded)
%              Number of leaves         :   29 ( 417 expanded)
%              Depth                    :   28
%              Number of atoms          :  234 (1530 expanded)
%              Number of equality atoms :  143 (1439 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f26])).

fof(f31,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f27])).

fof(f40,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK3),sK4) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f40])).

fof(f71,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f76])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f77])).

fof(f88,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f71,f72,f78])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f51,f51])).

fof(f8,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f72,f77])).

fof(f25,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f24,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_169,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_590,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)
    | X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_110082,plain,
    ( r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k1_xboole_0)
    | X0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_110084,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)),k1_xboole_0)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)) ),
    inference(instantiation,[status(thm)],[c_110082])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_160,negated_conjecture,
    ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_20,c_11,c_2])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_544,plain,
    ( k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_160,c_0])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_926,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_635,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_2])).

cnf(c_2009,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_926,c_635])).

cnf(c_3684,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) = k5_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_544,c_2009])).

cnf(c_3709,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_3684,c_9])).

cnf(c_2014,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_2009])).

cnf(c_4564,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2014,c_0])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_901,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_9842,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_4564,c_901])).

cnf(c_9866,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9842,c_12])).

cnf(c_35650,plain,
    ( k4_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3709,c_9866])).

cnf(c_2015,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_2,c_2009])).

cnf(c_2051,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_2015])).

cnf(c_35652,plain,
    ( k5_xboole_0(k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4),sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_3709,c_2051])).

cnf(c_35710,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k5_xboole_0(sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_35652,c_3709])).

cnf(c_35712,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35710,c_12])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_17,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_161,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(theory_normalisation,[status(thm)],[c_17,c_11,c_2])).

cnf(c_807,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_8,c_161])).

cnf(c_808,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(demodulation,[status(thm)],[c_807,c_9,c_12])).

cnf(c_811,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_817,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_811,c_9])).

cnf(c_4372,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_808,c_817])).

cnf(c_36028,plain,
    ( k3_tarski(k1_xboole_0) = sK3 ),
    inference(superposition,[status(thm)],[c_35712,c_4372])).

cnf(c_19,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36030,plain,
    ( sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_36028,c_19])).

cnf(c_36111,plain,
    ( k4_xboole_0(sK4,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_35650,c_36030])).

cnf(c_18,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36113,plain,
    ( k4_xboole_0(sK4,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_36111,c_18])).

cnf(c_35664,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_3709,c_1])).

cnf(c_36055,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK4) ),
    inference(light_normalisation,[status(thm)],[c_35664,c_36030])).

cnf(c_36057,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k1_zfmisc_1(k1_xboole_0))) = k4_xboole_0(k1_zfmisc_1(k1_xboole_0),sK4) ),
    inference(light_normalisation,[status(thm)],[c_36055,c_18])).

cnf(c_36116,plain,
    ( k4_xboole_0(k1_zfmisc_1(k1_xboole_0),sK4) = k4_xboole_0(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_36113,c_36057])).

cnf(c_36119,plain,
    ( k4_xboole_0(k1_zfmisc_1(k1_xboole_0),sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_36116,c_817])).

cnf(c_36097,plain,
    ( k5_xboole_0(k4_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK4),sK4) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_35652,c_36030])).

cnf(c_36099,plain,
    ( k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),sK4),sK4) = k1_zfmisc_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_36097,c_18])).

cnf(c_36123,plain,
    ( k5_xboole_0(sK4,sK4) = k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_36119,c_36099])).

cnf(c_36150,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36123,c_12])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_477,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_36532,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_36150,c_477])).

cnf(c_36542,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_36532])).

cnf(c_36544,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | r2_hidden(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_36542])).

cnf(c_164,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_761,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | k4_xboole_0(X2,k4_xboole_0(X2,X3)) != X1 ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_18642,plain,
    ( X0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | X0 != k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_18643,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)) != k1_xboole_0
    | sK3 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18642])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2924,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2926,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2924])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_485,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2818,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_485])).

cnf(c_1345,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_817,c_8])).

cnf(c_2833,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2818,c_1345])).

cnf(c_2868,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2833])).

cnf(c_2870,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | ~ r1_xboole_0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_903,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_916,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_37,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_110084,c_36544,c_36030,c_18643,c_2926,c_2870,c_916,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:17:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 27.36/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.36/4.00  
% 27.36/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.36/4.00  
% 27.36/4.00  ------  iProver source info
% 27.36/4.00  
% 27.36/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.36/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.36/4.00  git: non_committed_changes: false
% 27.36/4.00  git: last_make_outside_of_git: false
% 27.36/4.00  
% 27.36/4.00  ------ 
% 27.36/4.00  
% 27.36/4.00  ------ Input Options
% 27.36/4.00  
% 27.36/4.00  --out_options                           all
% 27.36/4.00  --tptp_safe_out                         true
% 27.36/4.00  --problem_path                          ""
% 27.36/4.00  --include_path                          ""
% 27.36/4.00  --clausifier                            res/vclausify_rel
% 27.36/4.00  --clausifier_options                    --mode clausify
% 27.36/4.00  --stdin                                 false
% 27.36/4.00  --stats_out                             sel
% 27.36/4.00  
% 27.36/4.00  ------ General Options
% 27.36/4.00  
% 27.36/4.00  --fof                                   false
% 27.36/4.00  --time_out_real                         604.99
% 27.36/4.00  --time_out_virtual                      -1.
% 27.36/4.00  --symbol_type_check                     false
% 27.36/4.00  --clausify_out                          false
% 27.36/4.00  --sig_cnt_out                           false
% 27.36/4.00  --trig_cnt_out                          false
% 27.36/4.00  --trig_cnt_out_tolerance                1.
% 27.36/4.00  --trig_cnt_out_sk_spl                   false
% 27.36/4.00  --abstr_cl_out                          false
% 27.36/4.00  
% 27.36/4.00  ------ Global Options
% 27.36/4.00  
% 27.36/4.00  --schedule                              none
% 27.36/4.00  --add_important_lit                     false
% 27.36/4.00  --prop_solver_per_cl                    1000
% 27.36/4.00  --min_unsat_core                        false
% 27.36/4.00  --soft_assumptions                      false
% 27.36/4.00  --soft_lemma_size                       3
% 27.36/4.00  --prop_impl_unit_size                   0
% 27.36/4.00  --prop_impl_unit                        []
% 27.36/4.00  --share_sel_clauses                     true
% 27.36/4.00  --reset_solvers                         false
% 27.36/4.00  --bc_imp_inh                            [conj_cone]
% 27.36/4.00  --conj_cone_tolerance                   3.
% 27.36/4.00  --extra_neg_conj                        none
% 27.36/4.00  --large_theory_mode                     true
% 27.36/4.00  --prolific_symb_bound                   200
% 27.36/4.00  --lt_threshold                          2000
% 27.36/4.00  --clause_weak_htbl                      true
% 27.36/4.00  --gc_record_bc_elim                     false
% 27.36/4.00  
% 27.36/4.00  ------ Preprocessing Options
% 27.36/4.00  
% 27.36/4.00  --preprocessing_flag                    true
% 27.36/4.00  --time_out_prep_mult                    0.1
% 27.36/4.00  --splitting_mode                        input
% 27.36/4.00  --splitting_grd                         true
% 27.36/4.00  --splitting_cvd                         false
% 27.36/4.00  --splitting_cvd_svl                     false
% 27.36/4.00  --splitting_nvd                         32
% 27.36/4.00  --sub_typing                            true
% 27.36/4.00  --prep_gs_sim                           false
% 27.36/4.00  --prep_unflatten                        true
% 27.36/4.00  --prep_res_sim                          true
% 27.36/4.00  --prep_upred                            true
% 27.36/4.00  --prep_sem_filter                       exhaustive
% 27.36/4.00  --prep_sem_filter_out                   false
% 27.36/4.00  --pred_elim                             false
% 27.36/4.00  --res_sim_input                         true
% 27.36/4.00  --eq_ax_congr_red                       true
% 27.36/4.00  --pure_diseq_elim                       true
% 27.36/4.00  --brand_transform                       false
% 27.36/4.00  --non_eq_to_eq                          false
% 27.36/4.00  --prep_def_merge                        true
% 27.36/4.00  --prep_def_merge_prop_impl              false
% 27.36/4.00  --prep_def_merge_mbd                    true
% 27.36/4.00  --prep_def_merge_tr_red                 false
% 27.36/4.00  --prep_def_merge_tr_cl                  false
% 27.36/4.00  --smt_preprocessing                     true
% 27.36/4.00  --smt_ac_axioms                         fast
% 27.36/4.00  --preprocessed_out                      false
% 27.36/4.00  --preprocessed_stats                    false
% 27.36/4.00  
% 27.36/4.00  ------ Abstraction refinement Options
% 27.36/4.00  
% 27.36/4.00  --abstr_ref                             []
% 27.36/4.00  --abstr_ref_prep                        false
% 27.36/4.00  --abstr_ref_until_sat                   false
% 27.36/4.00  --abstr_ref_sig_restrict                funpre
% 27.36/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.36/4.00  --abstr_ref_under                       []
% 27.36/4.00  
% 27.36/4.00  ------ SAT Options
% 27.36/4.00  
% 27.36/4.00  --sat_mode                              false
% 27.36/4.00  --sat_fm_restart_options                ""
% 27.36/4.00  --sat_gr_def                            false
% 27.36/4.00  --sat_epr_types                         true
% 27.36/4.00  --sat_non_cyclic_types                  false
% 27.36/4.00  --sat_finite_models                     false
% 27.36/4.00  --sat_fm_lemmas                         false
% 27.36/4.00  --sat_fm_prep                           false
% 27.36/4.00  --sat_fm_uc_incr                        true
% 27.36/4.00  --sat_out_model                         small
% 27.36/4.00  --sat_out_clauses                       false
% 27.36/4.00  
% 27.36/4.00  ------ QBF Options
% 27.36/4.00  
% 27.36/4.00  --qbf_mode                              false
% 27.36/4.00  --qbf_elim_univ                         false
% 27.36/4.00  --qbf_dom_inst                          none
% 27.36/4.00  --qbf_dom_pre_inst                      false
% 27.36/4.00  --qbf_sk_in                             false
% 27.36/4.00  --qbf_pred_elim                         true
% 27.36/4.00  --qbf_split                             512
% 27.36/4.00  
% 27.36/4.00  ------ BMC1 Options
% 27.36/4.00  
% 27.36/4.00  --bmc1_incremental                      false
% 27.36/4.00  --bmc1_axioms                           reachable_all
% 27.36/4.00  --bmc1_min_bound                        0
% 27.36/4.00  --bmc1_max_bound                        -1
% 27.36/4.00  --bmc1_max_bound_default                -1
% 27.36/4.00  --bmc1_symbol_reachability              true
% 27.36/4.00  --bmc1_property_lemmas                  false
% 27.36/4.00  --bmc1_k_induction                      false
% 27.36/4.00  --bmc1_non_equiv_states                 false
% 27.36/4.00  --bmc1_deadlock                         false
% 27.36/4.00  --bmc1_ucm                              false
% 27.36/4.00  --bmc1_add_unsat_core                   none
% 27.36/4.00  --bmc1_unsat_core_children              false
% 27.36/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.36/4.00  --bmc1_out_stat                         full
% 27.36/4.00  --bmc1_ground_init                      false
% 27.36/4.00  --bmc1_pre_inst_next_state              false
% 27.36/4.00  --bmc1_pre_inst_state                   false
% 27.36/4.00  --bmc1_pre_inst_reach_state             false
% 27.36/4.00  --bmc1_out_unsat_core                   false
% 27.36/4.00  --bmc1_aig_witness_out                  false
% 27.36/4.00  --bmc1_verbose                          false
% 27.36/4.00  --bmc1_dump_clauses_tptp                false
% 27.36/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.36/4.00  --bmc1_dump_file                        -
% 27.36/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.36/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.36/4.00  --bmc1_ucm_extend_mode                  1
% 27.36/4.00  --bmc1_ucm_init_mode                    2
% 27.36/4.00  --bmc1_ucm_cone_mode                    none
% 27.36/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.36/4.00  --bmc1_ucm_relax_model                  4
% 27.36/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.36/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.36/4.00  --bmc1_ucm_layered_model                none
% 27.36/4.00  --bmc1_ucm_max_lemma_size               10
% 27.36/4.00  
% 27.36/4.00  ------ AIG Options
% 27.36/4.00  
% 27.36/4.00  --aig_mode                              false
% 27.36/4.00  
% 27.36/4.00  ------ Instantiation Options
% 27.36/4.00  
% 27.36/4.00  --instantiation_flag                    true
% 27.36/4.00  --inst_sos_flag                         false
% 27.36/4.00  --inst_sos_phase                        true
% 27.36/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.36/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.36/4.00  --inst_lit_sel_side                     num_symb
% 27.36/4.00  --inst_solver_per_active                1400
% 27.36/4.00  --inst_solver_calls_frac                1.
% 27.36/4.00  --inst_passive_queue_type               priority_queues
% 27.36/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.36/4.00  --inst_passive_queues_freq              [25;2]
% 27.36/4.00  --inst_dismatching                      true
% 27.36/4.00  --inst_eager_unprocessed_to_passive     true
% 27.36/4.00  --inst_prop_sim_given                   true
% 27.36/4.00  --inst_prop_sim_new                     false
% 27.36/4.00  --inst_subs_new                         false
% 27.36/4.00  --inst_eq_res_simp                      false
% 27.36/4.00  --inst_subs_given                       false
% 27.36/4.00  --inst_orphan_elimination               true
% 27.36/4.00  --inst_learning_loop_flag               true
% 27.36/4.00  --inst_learning_start                   3000
% 27.36/4.00  --inst_learning_factor                  2
% 27.36/4.00  --inst_start_prop_sim_after_learn       3
% 27.36/4.00  --inst_sel_renew                        solver
% 27.36/4.00  --inst_lit_activity_flag                true
% 27.36/4.00  --inst_restr_to_given                   false
% 27.36/4.00  --inst_activity_threshold               500
% 27.36/4.00  --inst_out_proof                        true
% 27.36/4.00  
% 27.36/4.00  ------ Resolution Options
% 27.36/4.00  
% 27.36/4.00  --resolution_flag                       true
% 27.36/4.00  --res_lit_sel                           adaptive
% 27.36/4.00  --res_lit_sel_side                      none
% 27.36/4.00  --res_ordering                          kbo
% 27.36/4.00  --res_to_prop_solver                    active
% 27.36/4.00  --res_prop_simpl_new                    false
% 27.36/4.00  --res_prop_simpl_given                  true
% 27.36/4.00  --res_passive_queue_type                priority_queues
% 27.36/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.36/4.00  --res_passive_queues_freq               [15;5]
% 27.36/4.00  --res_forward_subs                      full
% 27.36/4.00  --res_backward_subs                     full
% 27.36/4.00  --res_forward_subs_resolution           true
% 27.36/4.00  --res_backward_subs_resolution          true
% 27.36/4.00  --res_orphan_elimination                true
% 27.36/4.00  --res_time_limit                        2.
% 27.36/4.00  --res_out_proof                         true
% 27.36/4.00  
% 27.36/4.00  ------ Superposition Options
% 27.36/4.00  
% 27.36/4.00  --superposition_flag                    true
% 27.36/4.00  --sup_passive_queue_type                priority_queues
% 27.36/4.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.36/4.00  --sup_passive_queues_freq               [1;4]
% 27.36/4.00  --demod_completeness_check              fast
% 27.36/4.00  --demod_use_ground                      true
% 27.36/4.00  --sup_to_prop_solver                    passive
% 27.36/4.00  --sup_prop_simpl_new                    true
% 27.36/4.00  --sup_prop_simpl_given                  true
% 27.36/4.00  --sup_fun_splitting                     false
% 27.36/4.00  --sup_smt_interval                      50000
% 27.36/4.00  
% 27.36/4.00  ------ Superposition Simplification Setup
% 27.36/4.00  
% 27.36/4.00  --sup_indices_passive                   []
% 27.36/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.36/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.00  --sup_full_bw                           [BwDemod]
% 27.36/4.00  --sup_immed_triv                        [TrivRules]
% 27.36/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.36/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.00  --sup_immed_bw_main                     []
% 27.36/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.36/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.36/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.36/4.00  
% 27.36/4.00  ------ Combination Options
% 27.36/4.00  
% 27.36/4.00  --comb_res_mult                         3
% 27.36/4.00  --comb_sup_mult                         2
% 27.36/4.00  --comb_inst_mult                        10
% 27.36/4.00  
% 27.36/4.00  ------ Debug Options
% 27.36/4.00  
% 27.36/4.00  --dbg_backtrace                         false
% 27.36/4.00  --dbg_dump_prop_clauses                 false
% 27.36/4.00  --dbg_dump_prop_clauses_file            -
% 27.36/4.00  --dbg_out_stat                          false
% 27.36/4.00  ------ Parsing...
% 27.36/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.36/4.00  
% 27.36/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 27.36/4.00  
% 27.36/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.36/4.00  
% 27.36/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.36/4.00  ------ Proving...
% 27.36/4.00  ------ Problem Properties 
% 27.36/4.00  
% 27.36/4.00  
% 27.36/4.00  clauses                                 21
% 27.36/4.00  conjectures                             1
% 27.36/4.00  EPR                                     1
% 27.36/4.00  Horn                                    18
% 27.36/4.00  unary                                   14
% 27.36/4.00  binary                                  5
% 27.36/4.00  lits                                    30
% 27.36/4.00  lits eq                                 14
% 27.36/4.00  fd_pure                                 0
% 27.36/4.00  fd_pseudo                               0
% 27.36/4.00  fd_cond                                 1
% 27.36/4.00  fd_pseudo_cond                          2
% 27.36/4.00  AC symbols                              1
% 27.36/4.00  
% 27.36/4.00  ------ Input Options Time Limit: Unbounded
% 27.36/4.00  
% 27.36/4.00  
% 27.36/4.00  ------ 
% 27.36/4.00  Current options:
% 27.36/4.00  ------ 
% 27.36/4.00  
% 27.36/4.00  ------ Input Options
% 27.36/4.00  
% 27.36/4.00  --out_options                           all
% 27.36/4.00  --tptp_safe_out                         true
% 27.36/4.00  --problem_path                          ""
% 27.36/4.00  --include_path                          ""
% 27.36/4.00  --clausifier                            res/vclausify_rel
% 27.36/4.00  --clausifier_options                    --mode clausify
% 27.36/4.00  --stdin                                 false
% 27.36/4.00  --stats_out                             sel
% 27.36/4.00  
% 27.36/4.00  ------ General Options
% 27.36/4.00  
% 27.36/4.00  --fof                                   false
% 27.36/4.00  --time_out_real                         604.99
% 27.36/4.00  --time_out_virtual                      -1.
% 27.36/4.00  --symbol_type_check                     false
% 27.36/4.00  --clausify_out                          false
% 27.36/4.00  --sig_cnt_out                           false
% 27.36/4.00  --trig_cnt_out                          false
% 27.36/4.00  --trig_cnt_out_tolerance                1.
% 27.36/4.00  --trig_cnt_out_sk_spl                   false
% 27.36/4.00  --abstr_cl_out                          false
% 27.36/4.00  
% 27.36/4.00  ------ Global Options
% 27.36/4.00  
% 27.36/4.00  --schedule                              none
% 27.36/4.00  --add_important_lit                     false
% 27.36/4.00  --prop_solver_per_cl                    1000
% 27.36/4.00  --min_unsat_core                        false
% 27.36/4.00  --soft_assumptions                      false
% 27.36/4.00  --soft_lemma_size                       3
% 27.36/4.00  --prop_impl_unit_size                   0
% 27.36/4.00  --prop_impl_unit                        []
% 27.36/4.00  --share_sel_clauses                     true
% 27.36/4.00  --reset_solvers                         false
% 27.36/4.00  --bc_imp_inh                            [conj_cone]
% 27.36/4.00  --conj_cone_tolerance                   3.
% 27.36/4.00  --extra_neg_conj                        none
% 27.36/4.00  --large_theory_mode                     true
% 27.36/4.00  --prolific_symb_bound                   200
% 27.36/4.00  --lt_threshold                          2000
% 27.36/4.00  --clause_weak_htbl                      true
% 27.36/4.00  --gc_record_bc_elim                     false
% 27.36/4.00  
% 27.36/4.00  ------ Preprocessing Options
% 27.36/4.00  
% 27.36/4.00  --preprocessing_flag                    true
% 27.36/4.00  --time_out_prep_mult                    0.1
% 27.36/4.00  --splitting_mode                        input
% 27.36/4.00  --splitting_grd                         true
% 27.36/4.00  --splitting_cvd                         false
% 27.36/4.00  --splitting_cvd_svl                     false
% 27.36/4.00  --splitting_nvd                         32
% 27.36/4.00  --sub_typing                            true
% 27.36/4.00  --prep_gs_sim                           false
% 27.36/4.00  --prep_unflatten                        true
% 27.36/4.00  --prep_res_sim                          true
% 27.36/4.00  --prep_upred                            true
% 27.36/4.00  --prep_sem_filter                       exhaustive
% 27.36/4.00  --prep_sem_filter_out                   false
% 27.36/4.00  --pred_elim                             false
% 27.36/4.00  --res_sim_input                         true
% 27.36/4.00  --eq_ax_congr_red                       true
% 27.36/4.00  --pure_diseq_elim                       true
% 27.36/4.00  --brand_transform                       false
% 27.36/4.00  --non_eq_to_eq                          false
% 27.36/4.00  --prep_def_merge                        true
% 27.36/4.00  --prep_def_merge_prop_impl              false
% 27.36/4.00  --prep_def_merge_mbd                    true
% 27.36/4.00  --prep_def_merge_tr_red                 false
% 27.36/4.00  --prep_def_merge_tr_cl                  false
% 27.36/4.00  --smt_preprocessing                     true
% 27.36/4.00  --smt_ac_axioms                         fast
% 27.36/4.00  --preprocessed_out                      false
% 27.36/4.00  --preprocessed_stats                    false
% 27.36/4.00  
% 27.36/4.00  ------ Abstraction refinement Options
% 27.36/4.00  
% 27.36/4.00  --abstr_ref                             []
% 27.36/4.00  --abstr_ref_prep                        false
% 27.36/4.00  --abstr_ref_until_sat                   false
% 27.36/4.00  --abstr_ref_sig_restrict                funpre
% 27.36/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.36/4.00  --abstr_ref_under                       []
% 27.36/4.00  
% 27.36/4.00  ------ SAT Options
% 27.36/4.00  
% 27.36/4.00  --sat_mode                              false
% 27.36/4.00  --sat_fm_restart_options                ""
% 27.36/4.00  --sat_gr_def                            false
% 27.36/4.00  --sat_epr_types                         true
% 27.36/4.00  --sat_non_cyclic_types                  false
% 27.36/4.00  --sat_finite_models                     false
% 27.36/4.00  --sat_fm_lemmas                         false
% 27.36/4.00  --sat_fm_prep                           false
% 27.36/4.00  --sat_fm_uc_incr                        true
% 27.36/4.00  --sat_out_model                         small
% 27.36/4.00  --sat_out_clauses                       false
% 27.36/4.00  
% 27.36/4.00  ------ QBF Options
% 27.36/4.00  
% 27.36/4.00  --qbf_mode                              false
% 27.36/4.00  --qbf_elim_univ                         false
% 27.36/4.00  --qbf_dom_inst                          none
% 27.36/4.00  --qbf_dom_pre_inst                      false
% 27.36/4.00  --qbf_sk_in                             false
% 27.36/4.00  --qbf_pred_elim                         true
% 27.36/4.00  --qbf_split                             512
% 27.36/4.00  
% 27.36/4.00  ------ BMC1 Options
% 27.36/4.00  
% 27.36/4.00  --bmc1_incremental                      false
% 27.36/4.00  --bmc1_axioms                           reachable_all
% 27.36/4.00  --bmc1_min_bound                        0
% 27.36/4.00  --bmc1_max_bound                        -1
% 27.36/4.00  --bmc1_max_bound_default                -1
% 27.36/4.00  --bmc1_symbol_reachability              true
% 27.36/4.00  --bmc1_property_lemmas                  false
% 27.36/4.00  --bmc1_k_induction                      false
% 27.36/4.00  --bmc1_non_equiv_states                 false
% 27.36/4.00  --bmc1_deadlock                         false
% 27.36/4.00  --bmc1_ucm                              false
% 27.36/4.00  --bmc1_add_unsat_core                   none
% 27.36/4.00  --bmc1_unsat_core_children              false
% 27.36/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.36/4.00  --bmc1_out_stat                         full
% 27.36/4.00  --bmc1_ground_init                      false
% 27.36/4.00  --bmc1_pre_inst_next_state              false
% 27.36/4.00  --bmc1_pre_inst_state                   false
% 27.36/4.00  --bmc1_pre_inst_reach_state             false
% 27.36/4.00  --bmc1_out_unsat_core                   false
% 27.36/4.00  --bmc1_aig_witness_out                  false
% 27.36/4.00  --bmc1_verbose                          false
% 27.36/4.00  --bmc1_dump_clauses_tptp                false
% 27.36/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.36/4.00  --bmc1_dump_file                        -
% 27.36/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.36/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.36/4.00  --bmc1_ucm_extend_mode                  1
% 27.36/4.00  --bmc1_ucm_init_mode                    2
% 27.36/4.00  --bmc1_ucm_cone_mode                    none
% 27.36/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.36/4.00  --bmc1_ucm_relax_model                  4
% 27.36/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.36/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.36/4.00  --bmc1_ucm_layered_model                none
% 27.36/4.00  --bmc1_ucm_max_lemma_size               10
% 27.36/4.00  
% 27.36/4.00  ------ AIG Options
% 27.36/4.00  
% 27.36/4.00  --aig_mode                              false
% 27.36/4.00  
% 27.36/4.00  ------ Instantiation Options
% 27.36/4.00  
% 27.36/4.00  --instantiation_flag                    true
% 27.36/4.00  --inst_sos_flag                         false
% 27.36/4.00  --inst_sos_phase                        true
% 27.36/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.36/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.36/4.00  --inst_lit_sel_side                     num_symb
% 27.36/4.00  --inst_solver_per_active                1400
% 27.36/4.00  --inst_solver_calls_frac                1.
% 27.36/4.00  --inst_passive_queue_type               priority_queues
% 27.36/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.36/4.00  --inst_passive_queues_freq              [25;2]
% 27.36/4.00  --inst_dismatching                      true
% 27.36/4.00  --inst_eager_unprocessed_to_passive     true
% 27.36/4.00  --inst_prop_sim_given                   true
% 27.36/4.00  --inst_prop_sim_new                     false
% 27.36/4.00  --inst_subs_new                         false
% 27.36/4.00  --inst_eq_res_simp                      false
% 27.36/4.00  --inst_subs_given                       false
% 27.36/4.00  --inst_orphan_elimination               true
% 27.36/4.00  --inst_learning_loop_flag               true
% 27.36/4.00  --inst_learning_start                   3000
% 27.36/4.00  --inst_learning_factor                  2
% 27.36/4.00  --inst_start_prop_sim_after_learn       3
% 27.36/4.00  --inst_sel_renew                        solver
% 27.36/4.00  --inst_lit_activity_flag                true
% 27.36/4.00  --inst_restr_to_given                   false
% 27.36/4.00  --inst_activity_threshold               500
% 27.36/4.00  --inst_out_proof                        true
% 27.36/4.00  
% 27.36/4.00  ------ Resolution Options
% 27.36/4.00  
% 27.36/4.00  --resolution_flag                       true
% 27.36/4.00  --res_lit_sel                           adaptive
% 27.36/4.00  --res_lit_sel_side                      none
% 27.36/4.00  --res_ordering                          kbo
% 27.36/4.00  --res_to_prop_solver                    active
% 27.36/4.00  --res_prop_simpl_new                    false
% 27.36/4.00  --res_prop_simpl_given                  true
% 27.36/4.00  --res_passive_queue_type                priority_queues
% 27.36/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.36/4.00  --res_passive_queues_freq               [15;5]
% 27.36/4.00  --res_forward_subs                      full
% 27.36/4.00  --res_backward_subs                     full
% 27.36/4.00  --res_forward_subs_resolution           true
% 27.36/4.00  --res_backward_subs_resolution          true
% 27.36/4.00  --res_orphan_elimination                true
% 27.36/4.00  --res_time_limit                        2.
% 27.36/4.00  --res_out_proof                         true
% 27.36/4.00  
% 27.36/4.00  ------ Superposition Options
% 27.36/4.00  
% 27.36/4.00  --superposition_flag                    true
% 27.36/4.00  --sup_passive_queue_type                priority_queues
% 27.36/4.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.36/4.00  --sup_passive_queues_freq               [1;4]
% 27.36/4.00  --demod_completeness_check              fast
% 27.36/4.00  --demod_use_ground                      true
% 27.36/4.00  --sup_to_prop_solver                    passive
% 27.36/4.00  --sup_prop_simpl_new                    true
% 27.36/4.00  --sup_prop_simpl_given                  true
% 27.36/4.00  --sup_fun_splitting                     false
% 27.36/4.00  --sup_smt_interval                      50000
% 27.36/4.00  
% 27.36/4.00  ------ Superposition Simplification Setup
% 27.36/4.00  
% 27.36/4.00  --sup_indices_passive                   []
% 27.36/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.36/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.00  --sup_full_bw                           [BwDemod]
% 27.36/4.00  --sup_immed_triv                        [TrivRules]
% 27.36/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.36/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.00  --sup_immed_bw_main                     []
% 27.36/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.36/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.36/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.36/4.00  
% 27.36/4.00  ------ Combination Options
% 27.36/4.00  
% 27.36/4.00  --comb_res_mult                         3
% 27.36/4.00  --comb_sup_mult                         2
% 27.36/4.00  --comb_inst_mult                        10
% 27.36/4.00  
% 27.36/4.00  ------ Debug Options
% 27.36/4.00  
% 27.36/4.00  --dbg_backtrace                         false
% 27.36/4.00  --dbg_dump_prop_clauses                 false
% 27.36/4.00  --dbg_dump_prop_clauses_file            -
% 27.36/4.00  --dbg_out_stat                          false
% 27.36/4.00  
% 27.36/4.00  
% 27.36/4.00  
% 27.36/4.00  
% 27.36/4.00  ------ Proving...
% 27.36/4.00  
% 27.36/4.00  
% 27.36/4.00  % SZS status Theorem for theBenchmark.p
% 27.36/4.00  
% 27.36/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.36/4.00  
% 27.36/4.00  fof(f26,conjecture,(
% 27.36/4.00    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f27,negated_conjecture,(
% 27.36/4.00    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 27.36/4.00    inference(negated_conjecture,[],[f26])).
% 27.36/4.00  
% 27.36/4.00  fof(f31,plain,(
% 27.36/4.00    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 27.36/4.00    inference(ennf_transformation,[],[f27])).
% 27.36/4.00  
% 27.36/4.00  fof(f40,plain,(
% 27.36/4.00    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK3),sK4)),
% 27.36/4.00    introduced(choice_axiom,[])).
% 27.36/4.00  
% 27.36/4.00  fof(f41,plain,(
% 27.36/4.00    k1_xboole_0 = k2_xboole_0(k1_tarski(sK3),sK4)),
% 27.36/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f40])).
% 27.36/4.00  
% 27.36/4.00  fof(f71,plain,(
% 27.36/4.00    k1_xboole_0 = k2_xboole_0(k1_tarski(sK3),sK4)),
% 27.36/4.00    inference(cnf_transformation,[],[f41])).
% 27.36/4.00  
% 27.36/4.00  fof(f14,axiom,(
% 27.36/4.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f56,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f14])).
% 27.36/4.00  
% 27.36/4.00  fof(f9,axiom,(
% 27.36/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f51,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.36/4.00    inference(cnf_transformation,[],[f9])).
% 27.36/4.00  
% 27.36/4.00  fof(f72,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 27.36/4.00    inference(definition_unfolding,[],[f56,f51])).
% 27.36/4.00  
% 27.36/4.00  fof(f15,axiom,(
% 27.36/4.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f57,plain,(
% 27.36/4.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f15])).
% 27.36/4.00  
% 27.36/4.00  fof(f16,axiom,(
% 27.36/4.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f58,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f16])).
% 27.36/4.00  
% 27.36/4.00  fof(f17,axiom,(
% 27.36/4.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f59,plain,(
% 27.36/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f17])).
% 27.36/4.00  
% 27.36/4.00  fof(f18,axiom,(
% 27.36/4.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f60,plain,(
% 27.36/4.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f18])).
% 27.36/4.00  
% 27.36/4.00  fof(f19,axiom,(
% 27.36/4.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f61,plain,(
% 27.36/4.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f19])).
% 27.36/4.00  
% 27.36/4.00  fof(f20,axiom,(
% 27.36/4.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f62,plain,(
% 27.36/4.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f20])).
% 27.36/4.00  
% 27.36/4.00  fof(f21,axiom,(
% 27.36/4.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f63,plain,(
% 27.36/4.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f21])).
% 27.36/4.00  
% 27.36/4.00  fof(f73,plain,(
% 27.36/4.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 27.36/4.00    inference(definition_unfolding,[],[f62,f63])).
% 27.36/4.00  
% 27.36/4.00  fof(f74,plain,(
% 27.36/4.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 27.36/4.00    inference(definition_unfolding,[],[f61,f73])).
% 27.36/4.00  
% 27.36/4.00  fof(f75,plain,(
% 27.36/4.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.36/4.00    inference(definition_unfolding,[],[f60,f74])).
% 27.36/4.00  
% 27.36/4.00  fof(f76,plain,(
% 27.36/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.36/4.00    inference(definition_unfolding,[],[f59,f75])).
% 27.36/4.00  
% 27.36/4.00  fof(f77,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.36/4.00    inference(definition_unfolding,[],[f58,f76])).
% 27.36/4.00  
% 27.36/4.00  fof(f78,plain,(
% 27.36/4.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 27.36/4.00    inference(definition_unfolding,[],[f57,f77])).
% 27.36/4.00  
% 27.36/4.00  fof(f88,plain,(
% 27.36/4.00    k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = k1_xboole_0),
% 27.36/4.00    inference(definition_unfolding,[],[f71,f72,f78])).
% 27.36/4.00  
% 27.36/4.00  fof(f12,axiom,(
% 27.36/4.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f54,plain,(
% 27.36/4.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f12])).
% 27.36/4.00  
% 27.36/4.00  fof(f2,axiom,(
% 27.36/4.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f43,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f2])).
% 27.36/4.00  
% 27.36/4.00  fof(f6,axiom,(
% 27.36/4.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f48,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f6])).
% 27.36/4.00  
% 27.36/4.00  fof(f79,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 27.36/4.00    inference(definition_unfolding,[],[f48,f51])).
% 27.36/4.00  
% 27.36/4.00  fof(f13,axiom,(
% 27.36/4.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f55,plain,(
% 27.36/4.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 27.36/4.00    inference(cnf_transformation,[],[f13])).
% 27.36/4.00  
% 27.36/4.00  fof(f10,axiom,(
% 27.36/4.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f52,plain,(
% 27.36/4.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.36/4.00    inference(cnf_transformation,[],[f10])).
% 27.36/4.00  
% 27.36/4.00  fof(f1,axiom,(
% 27.36/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f42,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f1])).
% 27.36/4.00  
% 27.36/4.00  fof(f80,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 27.36/4.00    inference(definition_unfolding,[],[f42,f51,f51])).
% 27.36/4.00  
% 27.36/4.00  fof(f8,axiom,(
% 27.36/4.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f50,plain,(
% 27.36/4.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 27.36/4.00    inference(cnf_transformation,[],[f8])).
% 27.36/4.00  
% 27.36/4.00  fof(f85,plain,(
% 27.36/4.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 27.36/4.00    inference(definition_unfolding,[],[f50,f51])).
% 27.36/4.00  
% 27.36/4.00  fof(f23,axiom,(
% 27.36/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f68,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 27.36/4.00    inference(cnf_transformation,[],[f23])).
% 27.36/4.00  
% 27.36/4.00  fof(f86,plain,(
% 27.36/4.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 27.36/4.00    inference(definition_unfolding,[],[f68,f72,f77])).
% 27.36/4.00  
% 27.36/4.00  fof(f25,axiom,(
% 27.36/4.00    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f70,plain,(
% 27.36/4.00    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 27.36/4.00    inference(cnf_transformation,[],[f25])).
% 27.36/4.00  
% 27.36/4.00  fof(f24,axiom,(
% 27.36/4.00    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f69,plain,(
% 27.36/4.00    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 27.36/4.00    inference(cnf_transformation,[],[f24])).
% 27.36/4.00  
% 27.36/4.00  fof(f87,plain,(
% 27.36/4.00    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 27.36/4.00    inference(definition_unfolding,[],[f69,f78])).
% 27.36/4.00  
% 27.36/4.00  fof(f22,axiom,(
% 27.36/4.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f36,plain,(
% 27.36/4.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 27.36/4.00    inference(nnf_transformation,[],[f22])).
% 27.36/4.00  
% 27.36/4.00  fof(f37,plain,(
% 27.36/4.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 27.36/4.00    inference(rectify,[],[f36])).
% 27.36/4.00  
% 27.36/4.00  fof(f38,plain,(
% 27.36/4.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 27.36/4.00    introduced(choice_axiom,[])).
% 27.36/4.00  
% 27.36/4.00  fof(f39,plain,(
% 27.36/4.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 27.36/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 27.36/4.00  
% 27.36/4.00  fof(f65,plain,(
% 27.36/4.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 27.36/4.00    inference(cnf_transformation,[],[f39])).
% 27.36/4.00  
% 27.36/4.00  fof(f89,plain,(
% 27.36/4.00    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 27.36/4.00    inference(equality_resolution,[],[f65])).
% 27.36/4.00  
% 27.36/4.00  fof(f7,axiom,(
% 27.36/4.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f49,plain,(
% 27.36/4.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f7])).
% 27.36/4.00  
% 27.36/4.00  fof(f84,plain,(
% 27.36/4.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 27.36/4.00    inference(definition_unfolding,[],[f49,f51])).
% 27.36/4.00  
% 27.36/4.00  fof(f3,axiom,(
% 27.36/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f28,plain,(
% 27.36/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.36/4.00    inference(rectify,[],[f3])).
% 27.36/4.00  
% 27.36/4.00  fof(f29,plain,(
% 27.36/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.36/4.00    inference(ennf_transformation,[],[f28])).
% 27.36/4.00  
% 27.36/4.00  fof(f32,plain,(
% 27.36/4.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 27.36/4.00    introduced(choice_axiom,[])).
% 27.36/4.00  
% 27.36/4.00  fof(f33,plain,(
% 27.36/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.36/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f32])).
% 27.36/4.00  
% 27.36/4.00  fof(f45,plain,(
% 27.36/4.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 27.36/4.00    inference(cnf_transformation,[],[f33])).
% 27.36/4.00  
% 27.36/4.00  fof(f81,plain,(
% 27.36/4.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.36/4.00    inference(definition_unfolding,[],[f45,f51])).
% 27.36/4.00  
% 27.36/4.00  fof(f11,axiom,(
% 27.36/4.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 27.36/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.00  
% 27.36/4.00  fof(f53,plain,(
% 27.36/4.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 27.36/4.00    inference(cnf_transformation,[],[f11])).
% 27.36/4.00  
% 27.36/4.00  cnf(c_169,plain,
% 27.36/4.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 27.36/4.00      theory(equality) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_590,plain,
% 27.36/4.00      ( r1_tarski(X0,X1)
% 27.36/4.00      | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)
% 27.36/4.00      | X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_169]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_110082,plain,
% 27.36/4.00      ( r1_tarski(X0,k1_xboole_0)
% 27.36/4.00      | ~ r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k1_xboole_0)
% 27.36/4.00      | X0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_590]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_110084,plain,
% 27.36/4.00      ( ~ r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)),k1_xboole_0)
% 27.36/4.00      | r1_tarski(sK3,k1_xboole_0)
% 27.36/4.00      | sK3 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)) ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_110082]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_20,negated_conjecture,
% 27.36/4.00      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = k1_xboole_0 ),
% 27.36/4.00      inference(cnf_transformation,[],[f88]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_11,plain,
% 27.36/4.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 27.36/4.00      inference(cnf_transformation,[],[f54]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2,plain,
% 27.36/4.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 27.36/4.00      inference(cnf_transformation,[],[f43]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_160,negated_conjecture,
% 27.36/4.00      ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))) = k1_xboole_0 ),
% 27.36/4.00      inference(theory_normalisation,[status(thm)],[c_20,c_11,c_2]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_0,plain,
% 27.36/4.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.36/4.00      inference(cnf_transformation,[],[f79]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_544,plain,
% 27.36/4.00      ( k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) = k1_xboole_0 ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_160,c_0]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_12,plain,
% 27.36/4.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.36/4.00      inference(cnf_transformation,[],[f55]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_926,plain,
% 27.36/4.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_9,plain,
% 27.36/4.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.36/4.00      inference(cnf_transformation,[],[f52]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_635,plain,
% 27.36/4.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_9,c_2]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2009,plain,
% 27.36/4.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_926,c_635]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_3684,plain,
% 27.36/4.00      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) = k5_xboole_0(sK4,k1_xboole_0) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_544,c_2009]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_3709,plain,
% 27.36/4.00      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) = sK4 ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_3684,c_9]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2014,plain,
% 27.36/4.00      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_0,c_2009]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_4564,plain,
% 27.36/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_2014,c_0]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_1,plain,
% 27.36/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.36/4.00      inference(cnf_transformation,[],[f80]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_901,plain,
% 27.36/4.00      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_9842,plain,
% 27.36/4.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_4564,c_901]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_9866,plain,
% 27.36/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_9842,c_12]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_35650,plain,
% 27.36/4.00      ( k4_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_3709,c_9866]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2015,plain,
% 27.36/4.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_2,c_2009]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2051,plain,
% 27.36/4.00      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_0,c_2015]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_35652,plain,
% 27.36/4.00      ( k5_xboole_0(k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4),sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_3709,c_2051]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_35710,plain,
% 27.36/4.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k5_xboole_0(sK4,sK4) ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_35652,c_3709]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_35712,plain,
% 27.36/4.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_35710,c_12]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_8,plain,
% 27.36/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.36/4.00      inference(cnf_transformation,[],[f85]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_17,plain,
% 27.36/4.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 27.36/4.00      inference(cnf_transformation,[],[f86]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_161,plain,
% 27.36/4.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 27.36/4.00      inference(theory_normalisation,[status(thm)],[c_17,c_11,c_2]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_807,plain,
% 27.36/4.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_8,c_161]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_808,plain,
% 27.36/4.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_807,c_9,c_12]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_811,plain,
% 27.36/4.00      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_817,plain,
% 27.36/4.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_811,c_9]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_4372,plain,
% 27.36/4.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_808,c_817]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36028,plain,
% 27.36/4.00      ( k3_tarski(k1_xboole_0) = sK3 ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_35712,c_4372]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_19,plain,
% 27.36/4.00      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 27.36/4.00      inference(cnf_transformation,[],[f70]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36030,plain,
% 27.36/4.00      ( sK3 = k1_xboole_0 ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_36028,c_19]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36111,plain,
% 27.36/4.00      ( k4_xboole_0(sK4,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_35650,c_36030]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_18,plain,
% 27.36/4.00      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 27.36/4.00      inference(cnf_transformation,[],[f87]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36113,plain,
% 27.36/4.00      ( k4_xboole_0(sK4,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_36111,c_18]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_35664,plain,
% 27.36/4.00      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_3709,c_1]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36055,plain,
% 27.36/4.00      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK4) ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_35664,c_36030]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36057,plain,
% 27.36/4.00      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k1_zfmisc_1(k1_xboole_0))) = k4_xboole_0(k1_zfmisc_1(k1_xboole_0),sK4) ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_36055,c_18]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36116,plain,
% 27.36/4.00      ( k4_xboole_0(k1_zfmisc_1(k1_xboole_0),sK4) = k4_xboole_0(sK4,k1_xboole_0) ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_36113,c_36057]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36119,plain,
% 27.36/4.00      ( k4_xboole_0(k1_zfmisc_1(k1_xboole_0),sK4) = sK4 ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_36116,c_817]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36097,plain,
% 27.36/4.00      ( k5_xboole_0(k4_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK4),sK4) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_35652,c_36030]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36099,plain,
% 27.36/4.00      ( k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),sK4),sK4) = k1_zfmisc_1(k1_xboole_0) ),
% 27.36/4.00      inference(light_normalisation,[status(thm)],[c_36097,c_18]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36123,plain,
% 27.36/4.00      ( k5_xboole_0(sK4,sK4) = k1_zfmisc_1(k1_xboole_0) ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_36119,c_36099]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36150,plain,
% 27.36/4.00      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_36123,c_12]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_15,plain,
% 27.36/4.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 27.36/4.00      inference(cnf_transformation,[],[f89]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_477,plain,
% 27.36/4.00      ( r1_tarski(X0,X1) != iProver_top
% 27.36/4.00      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 27.36/4.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36532,plain,
% 27.36/4.00      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 27.36/4.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_36150,c_477]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36542,plain,
% 27.36/4.00      ( ~ r1_tarski(X0,k1_xboole_0) | r2_hidden(X0,k1_xboole_0) ),
% 27.36/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_36532]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_36544,plain,
% 27.36/4.00      ( ~ r1_tarski(sK3,k1_xboole_0) | r2_hidden(sK3,k1_xboole_0) ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_36542]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_164,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_761,plain,
% 27.36/4.00      ( X0 != X1
% 27.36/4.00      | X0 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
% 27.36/4.00      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) != X1 ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_164]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_18642,plain,
% 27.36/4.00      ( X0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
% 27.36/4.00      | X0 != k1_xboole_0
% 27.36/4.00      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) != k1_xboole_0 ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_761]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_18643,plain,
% 27.36/4.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)) != k1_xboole_0
% 27.36/4.00      | sK3 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))
% 27.36/4.00      | sK3 != k1_xboole_0 ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_18642]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_7,plain,
% 27.36/4.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 27.36/4.00      inference(cnf_transformation,[],[f84]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2924,plain,
% 27.36/4.00      ( r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_7]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2926,plain,
% 27.36/4.00      ( r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)),k1_xboole_0) ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_2924]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_3,plain,
% 27.36/4.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 27.36/4.00      | ~ r1_xboole_0(X1,X2) ),
% 27.36/4.00      inference(cnf_transformation,[],[f81]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_485,plain,
% 27.36/4.00      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 27.36/4.00      | r1_xboole_0(X1,X2) != iProver_top ),
% 27.36/4.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2818,plain,
% 27.36/4.00      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
% 27.36/4.00      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_817,c_485]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_1345,plain,
% 27.36/4.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_817,c_8]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2833,plain,
% 27.36/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.36/4.00      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 27.36/4.00      inference(demodulation,[status(thm)],[c_2818,c_1345]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2868,plain,
% 27.36/4.00      ( ~ r2_hidden(X0,k1_xboole_0) | ~ r1_xboole_0(X1,k1_xboole_0) ),
% 27.36/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_2833]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_2870,plain,
% 27.36/4.00      ( ~ r2_hidden(sK3,k1_xboole_0) | ~ r1_xboole_0(sK3,k1_xboole_0) ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_2868]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_903,plain,
% 27.36/4.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 27.36/4.00      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_916,plain,
% 27.36/4.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_903]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_10,plain,
% 27.36/4.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 27.36/4.00      inference(cnf_transformation,[],[f53]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(c_37,plain,
% 27.36/4.00      ( r1_xboole_0(sK3,k1_xboole_0) ),
% 27.36/4.00      inference(instantiation,[status(thm)],[c_10]) ).
% 27.36/4.00  
% 27.36/4.00  cnf(contradiction,plain,
% 27.36/4.00      ( $false ),
% 27.36/4.00      inference(minisat,
% 27.36/4.00                [status(thm)],
% 27.36/4.00                [c_110084,c_36544,c_36030,c_18643,c_2926,c_2870,c_916,
% 27.36/4.00                 c_37]) ).
% 27.36/4.00  
% 27.36/4.00  
% 27.36/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.36/4.00  
% 27.36/4.00  ------                               Statistics
% 27.36/4.00  
% 27.36/4.00  ------ Selected
% 27.36/4.00  
% 27.36/4.00  total_time:                             3.134
% 27.36/4.00  
%------------------------------------------------------------------------------
