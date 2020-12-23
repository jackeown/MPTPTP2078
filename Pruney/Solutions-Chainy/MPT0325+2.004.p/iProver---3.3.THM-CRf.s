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
% DateTime   : Thu Dec  3 11:37:47 EST 2020

% Result     : Theorem 15.74s
% Output     : CNFRefutation 15.74s
% Verified   : 
% Statistics : Number of formulae       :  166 (1142 expanded)
%              Number of clauses        :   87 ( 258 expanded)
%              Number of leaves         :   29 ( 320 expanded)
%              Depth                    :   21
%              Number of atoms          :  314 (2005 expanded)
%              Number of equality atoms :  210 (1376 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK3,sK5)
        | ~ r1_tarski(sK2,sK4) )
      & k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
      & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tarski(sK3,sK5)
      | ~ r1_tarski(sK2,sK4) )
    & k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
    & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f39])).

fof(f68,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(cnf_transformation,[],[f20])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f74])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f61,f75])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3))))) ),
    inference(definition_unfolding,[],[f65,f48,f76,f48,f48])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f54,f75,f75])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,
    ( ~ r1_tarski(sK3,sK5)
    | ~ r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f69,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f34])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36864,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_36868,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_37091,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_36864,c_36868])).

cnf(c_16,plain,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37798,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_16,c_7])).

cnf(c_49246,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),sK3),k5_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3))) = k2_zfmisc_1(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),sK3) ),
    inference(superposition,[status(thm)],[c_37091,c_37798])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_49452,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_49246,c_10,c_11])).

cnf(c_49574,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),X0)),sK3),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),X0)),sK3) ),
    inference(superposition,[status(thm)],[c_49452,c_37798])).

cnf(c_12,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_8,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37272,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_8])).

cnf(c_39359,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_37272])).

cnf(c_40144,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39359,c_7])).

cnf(c_49613,plain,
    ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),X0)),sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_49574,c_10,c_11,c_40144])).

cnf(c_50374,plain,
    ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k1_xboole_0),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_49613])).

cnf(c_15,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_51242,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k1_xboole_0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_50374,c_15])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(sK2,sK4)
    | ~ r1_tarski(sK3,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2057,plain,
    ( r1_tarski(sK3,sK5)
    | k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_49565,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49452,c_15])).

cnf(c_36869,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_49841,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_49565,c_36869])).

cnf(c_50002,plain,
    ( r1_tarski(sK2,sK4)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_49841])).

cnf(c_37748,plain,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X1))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X3,X2))) ),
    inference(superposition,[status(thm)],[c_12,c_16])).

cnf(c_49584,plain,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k1_xboole_0)) = k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,X0))) ),
    inference(superposition,[status(thm)],[c_49452,c_37748])).

cnf(c_49586,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,X0))) = k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))) ),
    inference(demodulation,[status(thm)],[c_49584,c_37272])).

cnf(c_50463,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k5_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_37091,c_49586])).

cnf(c_50617,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_50463,c_11])).

cnf(c_50807,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_50617,c_15])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_182,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2062,plain,
    ( k2_zfmisc_1(sK2,sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_2096,plain,
    ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2062])).

cnf(c_2097,plain,
    ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2096])).

cnf(c_190,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2101,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(X0,X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_2102,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_3795,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_3796,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3795])).

cnf(c_181,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3995,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_182,c_181])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4027,plain,
    ( k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3995,c_13])).

cnf(c_4028,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4027])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5690,plain,
    ( r1_xboole_0(sK2,sK4)
    | k3_xboole_0(sK2,sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5691,plain,
    ( k3_xboole_0(sK2,sK4) != k1_xboole_0
    | r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5690])).

cnf(c_4916,plain,
    ( ~ r1_tarski(sK2,X0)
    | k3_xboole_0(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5712,plain,
    ( ~ r1_tarski(sK2,sK4)
    | k3_xboole_0(sK2,sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_4916])).

cnf(c_21128,plain,
    ( X0 != X1
    | k3_xboole_0(sK2,sK4) != X1
    | k3_xboole_0(sK2,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_24181,plain,
    ( X0 != sK2
    | k3_xboole_0(sK2,sK4) = X0
    | k3_xboole_0(sK2,sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_21128])).

cnf(c_24182,plain,
    ( k3_xboole_0(sK2,sK4) != sK2
    | k3_xboole_0(sK2,sK4) = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_24181])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36866,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_36872,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_41893,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37091,c_36872])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1406,plain,
    ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_20,c_4])).

cnf(c_1407,plain,
    ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

cnf(c_2750,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
    | k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) = k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2757,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))
    | k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2750])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4617,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | X1 != k2_zfmisc_1(sK2,sK3)
    | X0 != sK1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_4639,plain,
    ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),X0)
    | ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | X0 != k2_zfmisc_1(sK2,sK3)
    | sK1(k2_zfmisc_1(sK2,sK3)) != sK1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4617])).

cnf(c_4640,plain,
    ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),X0)
    | ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | X0 != k2_zfmisc_1(sK2,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_4639])).

cnf(c_5338,plain,
    ( ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0))
    | k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) != k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4640])).

cnf(c_5378,plain,
    ( ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))
    | k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5338])).

cnf(c_5379,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != k2_zfmisc_1(sK2,sK3)
    | r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) != iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5378])).

cnf(c_6473,plain,
    ( ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))
    | ~ r1_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6474,plain,
    ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6473])).

cnf(c_42052,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41893,c_21,c_1407,c_2757,c_5379,c_6474])).

cnf(c_42057,plain,
    ( r1_xboole_0(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_36866,c_42052])).

cnf(c_50874,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_50807,c_20,c_29,c_30,c_2097,c_2102,c_3796,c_4028,c_5691,c_5712,c_24182,c_42057,c_50002])).

cnf(c_51487,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_51242,c_20,c_19,c_29,c_30,c_2057,c_2097,c_2102,c_3796,c_4028,c_5691,c_5712,c_24182,c_42057,c_50002,c_50807])).

cnf(c_51559,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51487,c_20])).

cnf(c_51561,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51559,c_13])).

cnf(c_51562,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_51561])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.74/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.74/2.50  
% 15.74/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.74/2.50  
% 15.74/2.50  ------  iProver source info
% 15.74/2.50  
% 15.74/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.74/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.74/2.50  git: non_committed_changes: false
% 15.74/2.50  git: last_make_outside_of_git: false
% 15.74/2.50  
% 15.74/2.50  ------ 
% 15.74/2.50  ------ Parsing...
% 15.74/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  ------ Proving...
% 15.74/2.50  ------ Problem Properties 
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  clauses                                 22
% 15.74/2.50  conjectures                             3
% 15.74/2.50  EPR                                     1
% 15.74/2.50  Horn                                    19
% 15.74/2.50  unary                                   10
% 15.74/2.50  binary                                  11
% 15.74/2.50  lits                                    35
% 15.74/2.50  lits eq                                 18
% 15.74/2.50  fd_pure                                 0
% 15.74/2.50  fd_pseudo                               0
% 15.74/2.50  fd_cond                                 2
% 15.74/2.50  fd_pseudo_cond                          0
% 15.74/2.50  AC symbols                              0
% 15.74/2.50  
% 15.74/2.50  ------ Input Options Time Limit: Unbounded
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing...
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 15.74/2.50  Current options:
% 15.74/2.50  ------ 
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.74/2.50  
% 15.74/2.50  ------ Proving...
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  % SZS status Theorem for theBenchmark.p
% 15.74/2.50  
% 15.74/2.50   Resolution empty clause
% 15.74/2.50  
% 15.74/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.74/2.50  
% 15.74/2.50  fof(f9,axiom,(
% 15.74/2.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f52,plain,(
% 15.74/2.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.74/2.50    inference(cnf_transformation,[],[f9])).
% 15.74/2.50  
% 15.74/2.50  fof(f22,conjecture,(
% 15.74/2.50    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f23,negated_conjecture,(
% 15.74/2.50    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 15.74/2.50    inference(negated_conjecture,[],[f22])).
% 15.74/2.50  
% 15.74/2.50  fof(f29,plain,(
% 15.74/2.50    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 15.74/2.50    inference(ennf_transformation,[],[f23])).
% 15.74/2.50  
% 15.74/2.50  fof(f30,plain,(
% 15.74/2.50    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 15.74/2.50    inference(flattening,[],[f29])).
% 15.74/2.50  
% 15.74/2.50  fof(f39,plain,(
% 15.74/2.50    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)) & k1_xboole_0 != k2_zfmisc_1(sK2,sK3) & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))),
% 15.74/2.50    introduced(choice_axiom,[])).
% 15.74/2.50  
% 15.74/2.50  fof(f40,plain,(
% 15.74/2.50    (~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)) & k1_xboole_0 != k2_zfmisc_1(sK2,sK3) & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 15.74/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f39])).
% 15.74/2.50  
% 15.74/2.50  fof(f68,plain,(
% 15.74/2.50    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 15.74/2.50    inference(cnf_transformation,[],[f40])).
% 15.74/2.50  
% 15.74/2.50  fof(f8,axiom,(
% 15.74/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f27,plain,(
% 15.74/2.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.74/2.50    inference(ennf_transformation,[],[f8])).
% 15.74/2.50  
% 15.74/2.50  fof(f51,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f27])).
% 15.74/2.50  
% 15.74/2.50  fof(f20,axiom,(
% 15.74/2.50    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f65,plain,(
% 15.74/2.50    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))) )),
% 15.74/2.50    inference(cnf_transformation,[],[f20])).
% 15.74/2.50  
% 15.74/2.50  fof(f18,axiom,(
% 15.74/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f61,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.74/2.50    inference(cnf_transformation,[],[f18])).
% 15.74/2.50  
% 15.74/2.50  fof(f12,axiom,(
% 15.74/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f55,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f12])).
% 15.74/2.50  
% 15.74/2.50  fof(f13,axiom,(
% 15.74/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f56,plain,(
% 15.74/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f13])).
% 15.74/2.50  
% 15.74/2.50  fof(f14,axiom,(
% 15.74/2.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f57,plain,(
% 15.74/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f14])).
% 15.74/2.50  
% 15.74/2.50  fof(f15,axiom,(
% 15.74/2.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f58,plain,(
% 15.74/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f15])).
% 15.74/2.50  
% 15.74/2.50  fof(f16,axiom,(
% 15.74/2.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f59,plain,(
% 15.74/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f16])).
% 15.74/2.50  
% 15.74/2.50  fof(f17,axiom,(
% 15.74/2.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f60,plain,(
% 15.74/2.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f17])).
% 15.74/2.50  
% 15.74/2.50  fof(f71,plain,(
% 15.74/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 15.74/2.50    inference(definition_unfolding,[],[f59,f60])).
% 15.74/2.50  
% 15.74/2.50  fof(f72,plain,(
% 15.74/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 15.74/2.50    inference(definition_unfolding,[],[f58,f71])).
% 15.74/2.50  
% 15.74/2.50  fof(f73,plain,(
% 15.74/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 15.74/2.50    inference(definition_unfolding,[],[f57,f72])).
% 15.74/2.50  
% 15.74/2.50  fof(f74,plain,(
% 15.74/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 15.74/2.50    inference(definition_unfolding,[],[f56,f73])).
% 15.74/2.50  
% 15.74/2.50  fof(f75,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 15.74/2.50    inference(definition_unfolding,[],[f55,f74])).
% 15.74/2.50  
% 15.74/2.50  fof(f76,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 15.74/2.50    inference(definition_unfolding,[],[f61,f75])).
% 15.74/2.50  
% 15.74/2.50  fof(f5,axiom,(
% 15.74/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f48,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.74/2.50    inference(cnf_transformation,[],[f5])).
% 15.74/2.50  
% 15.74/2.50  fof(f82,plain,(
% 15.74/2.50    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3)))))) )),
% 15.74/2.50    inference(definition_unfolding,[],[f65,f48,f76,f48,f48])).
% 15.74/2.50  
% 15.74/2.50  fof(f6,axiom,(
% 15.74/2.50    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f49,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 15.74/2.50    inference(cnf_transformation,[],[f6])).
% 15.74/2.50  
% 15.74/2.50  fof(f79,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 15.74/2.50    inference(definition_unfolding,[],[f49,f76])).
% 15.74/2.50  
% 15.74/2.50  fof(f10,axiom,(
% 15.74/2.50    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f53,plain,(
% 15.74/2.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f10])).
% 15.74/2.50  
% 15.74/2.50  fof(f11,axiom,(
% 15.74/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f54,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f11])).
% 15.74/2.50  
% 15.74/2.50  fof(f81,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 15.74/2.50    inference(definition_unfolding,[],[f54,f75,f75])).
% 15.74/2.50  
% 15.74/2.50  fof(f7,axiom,(
% 15.74/2.50    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f50,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 15.74/2.50    inference(cnf_transformation,[],[f7])).
% 15.74/2.50  
% 15.74/2.50  fof(f80,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 15.74/2.50    inference(definition_unfolding,[],[f50,f76])).
% 15.74/2.50  
% 15.74/2.50  fof(f19,axiom,(
% 15.74/2.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f37,plain,(
% 15.74/2.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.74/2.50    inference(nnf_transformation,[],[f19])).
% 15.74/2.50  
% 15.74/2.50  fof(f38,plain,(
% 15.74/2.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.74/2.50    inference(flattening,[],[f37])).
% 15.74/2.50  
% 15.74/2.50  fof(f62,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f38])).
% 15.74/2.50  
% 15.74/2.50  fof(f70,plain,(
% 15.74/2.50    ~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)),
% 15.74/2.50    inference(cnf_transformation,[],[f40])).
% 15.74/2.50  
% 15.74/2.50  fof(f4,axiom,(
% 15.74/2.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f36,plain,(
% 15.74/2.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 15.74/2.50    inference(nnf_transformation,[],[f4])).
% 15.74/2.50  
% 15.74/2.50  fof(f46,plain,(
% 15.74/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f36])).
% 15.74/2.50  
% 15.74/2.50  fof(f78,plain,(
% 15.74/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.74/2.50    inference(definition_unfolding,[],[f46,f48])).
% 15.74/2.50  
% 15.74/2.50  fof(f69,plain,(
% 15.74/2.50    k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 15.74/2.50    inference(cnf_transformation,[],[f40])).
% 15.74/2.50  
% 15.74/2.50  fof(f63,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.74/2.50    inference(cnf_transformation,[],[f38])).
% 15.74/2.50  
% 15.74/2.50  fof(f84,plain,(
% 15.74/2.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.74/2.50    inference(equality_resolution,[],[f63])).
% 15.74/2.50  
% 15.74/2.50  fof(f64,plain,(
% 15.74/2.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.74/2.50    inference(cnf_transformation,[],[f38])).
% 15.74/2.50  
% 15.74/2.50  fof(f83,plain,(
% 15.74/2.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.74/2.50    inference(equality_resolution,[],[f64])).
% 15.74/2.50  
% 15.74/2.50  fof(f1,axiom,(
% 15.74/2.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f31,plain,(
% 15.74/2.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.74/2.50    inference(nnf_transformation,[],[f1])).
% 15.74/2.50  
% 15.74/2.50  fof(f42,plain,(
% 15.74/2.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.74/2.50    inference(cnf_transformation,[],[f31])).
% 15.74/2.50  
% 15.74/2.50  fof(f21,axiom,(
% 15.74/2.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f28,plain,(
% 15.74/2.50    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 15.74/2.50    inference(ennf_transformation,[],[f21])).
% 15.74/2.50  
% 15.74/2.50  fof(f66,plain,(
% 15.74/2.50    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 15.74/2.50    inference(cnf_transformation,[],[f28])).
% 15.74/2.50  
% 15.74/2.50  fof(f2,axiom,(
% 15.74/2.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f24,plain,(
% 15.74/2.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.74/2.50    inference(rectify,[],[f2])).
% 15.74/2.50  
% 15.74/2.50  fof(f25,plain,(
% 15.74/2.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.74/2.50    inference(ennf_transformation,[],[f24])).
% 15.74/2.50  
% 15.74/2.50  fof(f32,plain,(
% 15.74/2.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 15.74/2.50    introduced(choice_axiom,[])).
% 15.74/2.50  
% 15.74/2.50  fof(f33,plain,(
% 15.74/2.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.74/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f32])).
% 15.74/2.50  
% 15.74/2.50  fof(f44,plain,(
% 15.74/2.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 15.74/2.50    inference(cnf_transformation,[],[f33])).
% 15.74/2.50  
% 15.74/2.50  fof(f3,axiom,(
% 15.74/2.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 15.74/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.50  
% 15.74/2.50  fof(f26,plain,(
% 15.74/2.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 15.74/2.50    inference(ennf_transformation,[],[f3])).
% 15.74/2.50  
% 15.74/2.50  fof(f34,plain,(
% 15.74/2.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 15.74/2.50    introduced(choice_axiom,[])).
% 15.74/2.50  
% 15.74/2.50  fof(f35,plain,(
% 15.74/2.50    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 15.74/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f34])).
% 15.74/2.50  
% 15.74/2.50  fof(f45,plain,(
% 15.74/2.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 15.74/2.50    inference(cnf_transformation,[],[f35])).
% 15.74/2.50  
% 15.74/2.50  cnf(c_10,plain,
% 15.74/2.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_21,negated_conjecture,
% 15.74/2.50      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
% 15.74/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_36864,plain,
% 15.74/2.50      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 15.74/2.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_9,plain,
% 15.74/2.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f51]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_36868,plain,
% 15.74/2.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.74/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_37091,plain,
% 15.74/2.50      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK2,sK3) ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_36864,c_36868]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_16,plain,
% 15.74/2.50      ( k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k2_zfmisc_1(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
% 15.74/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_7,plain,
% 15.74/2.50      ( k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f79]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_37798,plain,
% 15.74/2.50      ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_16,c_7]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_49246,plain,
% 15.74/2.50      ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),sK3),k5_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3))) = k2_zfmisc_1(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),sK3) ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_37091,c_37798]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_11,plain,
% 15.74/2.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_49452,plain,
% 15.74/2.50      ( k2_zfmisc_1(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),sK3) = k1_xboole_0 ),
% 15.74/2.50      inference(demodulation,[status(thm)],[c_49246,c_10,c_11]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_49574,plain,
% 15.74/2.50      ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),X0)),sK3),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),X0)),sK3) ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_49452,c_37798]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_12,plain,
% 15.74/2.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 15.74/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_8,plain,
% 15.74/2.50      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_37272,plain,
% 15.74/2.50      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_10,c_8]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_39359,plain,
% 15.74/2.50      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_12,c_37272]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_40144,plain,
% 15.74/2.50      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_39359,c_7]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_49613,plain,
% 15.74/2.50      ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),X0)),sK3) = k1_xboole_0 ),
% 15.74/2.50      inference(demodulation,[status(thm)],[c_49574,c_10,c_11,c_40144]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_50374,plain,
% 15.74/2.50      ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k1_xboole_0),sK3) = k1_xboole_0 ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_10,c_49613]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_15,plain,
% 15.74/2.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.74/2.50      | k1_xboole_0 = X0
% 15.74/2.50      | k1_xboole_0 = X1 ),
% 15.74/2.50      inference(cnf_transformation,[],[f62]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_51242,plain,
% 15.74/2.50      ( k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),k1_xboole_0) = k1_xboole_0
% 15.74/2.50      | sK3 = k1_xboole_0 ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_50374,c_15]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_19,negated_conjecture,
% 15.74/2.50      ( ~ r1_tarski(sK2,sK4) | ~ r1_tarski(sK3,sK5) ),
% 15.74/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_6,plain,
% 15.74/2.50      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f78]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_2057,plain,
% 15.74/2.50      ( r1_tarski(sK3,sK5)
% 15.74/2.50      | k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)) != k1_xboole_0 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_49565,plain,
% 15.74/2.50      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k1_xboole_0
% 15.74/2.50      | sK3 = k1_xboole_0 ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_49452,c_15]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_36869,plain,
% 15.74/2.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 15.74/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.74/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_49841,plain,
% 15.74/2.50      ( sK3 = k1_xboole_0 | r1_tarski(sK2,sK4) = iProver_top ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_49565,c_36869]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_50002,plain,
% 15.74/2.50      ( r1_tarski(sK2,sK4) | sK3 = k1_xboole_0 ),
% 15.74/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_49841]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_37748,plain,
% 15.74/2.50      ( k3_tarski(k6_enumset1(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X1))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X3,X2))) ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_12,c_16]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_49584,plain,
% 15.74/2.50      ( k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))),k1_xboole_0)) = k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,X0))) ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_49452,c_37748]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_49586,plain,
% 15.74/2.50      ( k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,X0))) = k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))) ),
% 15.74/2.50      inference(demodulation,[status(thm)],[c_49584,c_37272]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_50463,plain,
% 15.74/2.50      ( k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k5_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)) ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_37091,c_49586]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_50617,plain,
% 15.74/2.50      ( k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k1_xboole_0 ),
% 15.74/2.50      inference(demodulation,[status(thm)],[c_50463,c_11]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_50807,plain,
% 15.74/2.50      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)) = k1_xboole_0
% 15.74/2.50      | sK2 = k1_xboole_0 ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_50617,c_15]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_20,negated_conjecture,
% 15.74/2.50      ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
% 15.74/2.50      inference(cnf_transformation,[],[f69]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_29,plain,
% 15.74/2.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.74/2.50      | k1_xboole_0 = k1_xboole_0 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_15]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_14,plain,
% 15.74/2.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f84]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_30,plain,
% 15.74/2.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_14]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_182,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_2062,plain,
% 15.74/2.50      ( k2_zfmisc_1(sK2,sK3) != X0
% 15.74/2.50      | k1_xboole_0 != X0
% 15.74/2.50      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_182]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_2096,plain,
% 15.74/2.50      ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(X0,X1)
% 15.74/2.50      | k1_xboole_0 != k2_zfmisc_1(X0,X1)
% 15.74/2.50      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_2062]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_2097,plain,
% 15.74/2.50      ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 15.74/2.50      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
% 15.74/2.50      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_2096]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_190,plain,
% 15.74/2.50      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 15.74/2.50      theory(equality) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_2101,plain,
% 15.74/2.50      ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(X0,X1) | sK2 != X0 | sK3 != X1 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_190]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_2102,plain,
% 15.74/2.50      ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 15.74/2.50      | sK2 != k1_xboole_0
% 15.74/2.50      | sK3 != k1_xboole_0 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_2101]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_3795,plain,
% 15.74/2.50      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_182]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_3796,plain,
% 15.74/2.50      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_3795]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_181,plain,( X0 = X0 ),theory(equality) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_3995,plain,
% 15.74/2.50      ( X0 != X1 | X1 = X0 ),
% 15.74/2.50      inference(resolution,[status(thm)],[c_182,c_181]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_13,plain,
% 15.74/2.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f83]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_4027,plain,
% 15.74/2.50      ( k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
% 15.74/2.50      inference(resolution,[status(thm)],[c_3995,c_13]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_4028,plain,
% 15.74/2.50      ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_4027]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_0,plain,
% 15.74/2.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f42]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_5690,plain,
% 15.74/2.50      ( r1_xboole_0(sK2,sK4) | k3_xboole_0(sK2,sK4) != k1_xboole_0 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_0]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_5691,plain,
% 15.74/2.50      ( k3_xboole_0(sK2,sK4) != k1_xboole_0
% 15.74/2.50      | r1_xboole_0(sK2,sK4) = iProver_top ),
% 15.74/2.50      inference(predicate_to_equality,[status(thm)],[c_5690]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_4916,plain,
% 15.74/2.50      ( ~ r1_tarski(sK2,X0) | k3_xboole_0(sK2,X0) = sK2 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_5712,plain,
% 15.74/2.50      ( ~ r1_tarski(sK2,sK4) | k3_xboole_0(sK2,sK4) = sK2 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_4916]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_21128,plain,
% 15.74/2.50      ( X0 != X1 | k3_xboole_0(sK2,sK4) != X1 | k3_xboole_0(sK2,sK4) = X0 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_182]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_24181,plain,
% 15.74/2.50      ( X0 != sK2 | k3_xboole_0(sK2,sK4) = X0 | k3_xboole_0(sK2,sK4) != sK2 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_21128]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_24182,plain,
% 15.74/2.50      ( k3_xboole_0(sK2,sK4) != sK2
% 15.74/2.50      | k3_xboole_0(sK2,sK4) = k1_xboole_0
% 15.74/2.50      | k1_xboole_0 != sK2 ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_24181]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_18,plain,
% 15.74/2.50      ( ~ r1_xboole_0(X0,X1)
% 15.74/2.50      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 15.74/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_36866,plain,
% 15.74/2.50      ( r1_xboole_0(X0,X1) != iProver_top
% 15.74/2.50      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 15.74/2.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_2,plain,
% 15.74/2.50      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 15.74/2.50      inference(cnf_transformation,[],[f44]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_36872,plain,
% 15.74/2.50      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 15.74/2.50      | r1_xboole_0(X1,X2) != iProver_top ),
% 15.74/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_41893,plain,
% 15.74/2.50      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) != iProver_top
% 15.74/2.50      | r1_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_37091,c_36872]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_4,plain,
% 15.74/2.50      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 15.74/2.50      inference(cnf_transformation,[],[f45]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_1406,plain,
% 15.74/2.50      ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) ),
% 15.74/2.50      inference(resolution,[status(thm)],[c_20,c_4]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_1407,plain,
% 15.74/2.50      ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 15.74/2.50      inference(predicate_to_equality,[status(thm)],[c_1406]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_2750,plain,
% 15.74/2.50      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
% 15.74/2.50      | k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) = k2_zfmisc_1(sK2,sK3) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_2757,plain,
% 15.74/2.50      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))
% 15.74/2.50      | k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK2,sK3) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_2750]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_185,plain,
% 15.74/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.74/2.50      theory(equality) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_4617,plain,
% 15.74/2.50      ( r2_hidden(X0,X1)
% 15.74/2.50      | ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
% 15.74/2.50      | X1 != k2_zfmisc_1(sK2,sK3)
% 15.74/2.50      | X0 != sK1(k2_zfmisc_1(sK2,sK3)) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_185]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_4639,plain,
% 15.74/2.50      ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),X0)
% 15.74/2.50      | ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
% 15.74/2.50      | X0 != k2_zfmisc_1(sK2,sK3)
% 15.74/2.50      | sK1(k2_zfmisc_1(sK2,sK3)) != sK1(k2_zfmisc_1(sK2,sK3)) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_4617]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_4640,plain,
% 15.74/2.50      ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),X0)
% 15.74/2.50      | ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
% 15.74/2.50      | X0 != k2_zfmisc_1(sK2,sK3) ),
% 15.74/2.50      inference(equality_resolution_simp,[status(thm)],[c_4639]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_5338,plain,
% 15.74/2.50      ( ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
% 15.74/2.50      | r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0))
% 15.74/2.50      | k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) != k2_zfmisc_1(sK2,sK3) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_4640]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_5378,plain,
% 15.74/2.50      ( ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
% 15.74/2.50      | r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))
% 15.74/2.50      | k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != k2_zfmisc_1(sK2,sK3) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_5338]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_5379,plain,
% 15.74/2.50      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != k2_zfmisc_1(sK2,sK3)
% 15.74/2.50      | r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) != iProver_top
% 15.74/2.50      | r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 15.74/2.50      inference(predicate_to_equality,[status(thm)],[c_5378]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_6473,plain,
% 15.74/2.50      ( ~ r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))
% 15.74/2.50      | ~ r1_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
% 15.74/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_6474,plain,
% 15.74/2.50      ( r2_hidden(sK1(k2_zfmisc_1(sK2,sK3)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) != iProver_top
% 15.74/2.50      | r1_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 15.74/2.50      inference(predicate_to_equality,[status(thm)],[c_6473]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_42052,plain,
% 15.74/2.50      ( r1_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 15.74/2.50      inference(global_propositional_subsumption,
% 15.74/2.50                [status(thm)],
% 15.74/2.50                [c_41893,c_21,c_1407,c_2757,c_5379,c_6474]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_42057,plain,
% 15.74/2.50      ( r1_xboole_0(sK2,sK4) != iProver_top ),
% 15.74/2.50      inference(superposition,[status(thm)],[c_36866,c_42052]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_50874,plain,
% 15.74/2.50      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 15.74/2.50      inference(global_propositional_subsumption,
% 15.74/2.50                [status(thm)],
% 15.74/2.50                [c_50807,c_20,c_29,c_30,c_2097,c_2102,c_3796,c_4028,c_5691,
% 15.74/2.50                 c_5712,c_24182,c_42057,c_50002]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_51487,plain,
% 15.74/2.50      ( sK3 = k1_xboole_0 ),
% 15.74/2.50      inference(global_propositional_subsumption,
% 15.74/2.50                [status(thm)],
% 15.74/2.50                [c_51242,c_20,c_19,c_29,c_30,c_2057,c_2097,c_2102,c_3796,
% 15.74/2.50                 c_4028,c_5691,c_5712,c_24182,c_42057,c_50002,c_50807]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_51559,plain,
% 15.74/2.50      ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0 ),
% 15.74/2.50      inference(demodulation,[status(thm)],[c_51487,c_20]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_51561,plain,
% 15.74/2.50      ( k1_xboole_0 != k1_xboole_0 ),
% 15.74/2.50      inference(demodulation,[status(thm)],[c_51559,c_13]) ).
% 15.74/2.50  
% 15.74/2.50  cnf(c_51562,plain,
% 15.74/2.50      ( $false ),
% 15.74/2.50      inference(equality_resolution_simp,[status(thm)],[c_51561]) ).
% 15.74/2.50  
% 15.74/2.50  
% 15.74/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.74/2.50  
% 15.74/2.50  ------                               Statistics
% 15.74/2.50  
% 15.74/2.50  ------ Selected
% 15.74/2.50  
% 15.74/2.50  total_time:                             1.904
% 15.74/2.50  
%------------------------------------------------------------------------------
