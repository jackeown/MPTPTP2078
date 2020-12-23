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
% DateTime   : Thu Dec  3 11:37:15 EST 2020

% Result     : Theorem 19.68s
% Output     : CNFRefutation 19.68s
% Verified   : 
% Statistics : Number of formulae       :  131 (2322 expanded)
%              Number of clauses        :   70 ( 458 expanded)
%              Number of leaves         :   19 ( 711 expanded)
%              Depth                    :   25
%              Number of atoms          :  161 (2395 expanded)
%              Number of equality atoms :  160 (2394 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   11 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f63,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f36,f58,f58,f59])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k3_xboole_0(X0,X1))
      & k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) ),
    inference(definition_unfolding,[],[f50,f59,f59])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) ),
    inference(definition_unfolding,[],[f48,f58,f58])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)),k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f51,f59,f59])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f58,f58])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
        & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) != k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      | k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) != k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
        | k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(k4_xboole_0(X0,X1),X2) )
   => ( k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) != k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1))
      | k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) != k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1))
    | k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).

fof(f52,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) != k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1))
    | k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f32,f59])).

fof(f68,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
    | k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) ),
    inference(definition_unfolding,[],[f52,f60,f60,f60,f60])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_38,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_6,c_4,c_0])).

cnf(c_319,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_38])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X2,X1),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),X1) ),
    inference(theory_normalisation,[status(thm)],[c_13,c_4,c_0])).

cnf(c_11,plain,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_55,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),X1) ),
    inference(light_normalisation,[status(thm)],[c_36,c_11])).

cnf(c_5529,plain,
    ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))))),X2) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,X1),X2),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),X2),k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X2))) ),
    inference(superposition,[status(thm)],[c_319,c_55])).

cnf(c_5534,plain,
    ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,X1),X2),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),X2),k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X2))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),X2) ),
    inference(demodulation,[status(thm)],[c_5529,c_319])).

cnf(c_62,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_61,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_843,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3,c_61])).

cnf(c_1156,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_62,c_843])).

cnf(c_60,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_1031,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_843,c_60])).

cnf(c_1177,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_1156,c_1031])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_232,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_159,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_239,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_232,c_159])).

cnf(c_530,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_239])).

cnf(c_592,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_239,c_530])).

cnf(c_650,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_592])).

cnf(c_1734,plain,
    ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X2),k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(superposition,[status(thm)],[c_55,c_650])).

cnf(c_5535,plain,
    ( k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X2) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,X0),X2),k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_5534,c_1177,c_1734])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_603,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_530,c_530])).

cnf(c_865,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_61,c_603])).

cnf(c_5536,plain,
    ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,X1),X2),k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X0,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5535,c_5,c_8,c_239,c_865])).

cnf(c_846,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_603,c_61])).

cnf(c_883,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_846,c_4])).

cnf(c_2686,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_4,c_883])).

cnf(c_45411,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k2_zfmisc_1(k5_xboole_0(X1,X2),X3)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(superposition,[status(thm)],[c_5536,c_2686])).

cnf(c_45458,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k2_zfmisc_1(k5_xboole_0(X1,X2),X3)),X0) = k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_45411,c_3])).

cnf(c_45459,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_45458,c_603])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_37,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X0,X2),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(theory_normalisation,[status(thm)],[c_12,c_4,c_0])).

cnf(c_10,plain,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_56,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(light_normalisation,[status(thm)],[c_37,c_10])).

cnf(c_2509,plain,
    ( k2_zfmisc_1(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(superposition,[status(thm)],[c_38,c_56])).

cnf(c_2539,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) ),
    inference(superposition,[status(thm)],[c_56,c_650])).

cnf(c_2562,plain,
    ( k2_zfmisc_1(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_2509,c_2539])).

cnf(c_2563,plain,
    ( k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))),k3_tarski(k6_enumset1(k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,X1)),k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_2562,c_1177])).

cnf(c_1159,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_62,c_239])).

cnf(c_2564,plain,
    ( k2_zfmisc_1(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_2563,c_1159,c_1177])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2565,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2564,c_5,c_7,c_38])).

cnf(c_867,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_61,c_239])).

cnf(c_22172,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2565,c_867])).

cnf(c_534,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_4,c_239])).

cnf(c_1240,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
    inference(superposition,[status(thm)],[c_4,c_534])).

cnf(c_22184,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k2_zfmisc_1(X2,k5_xboole_0(X3,X4)))),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,X4)) ),
    inference(superposition,[status(thm)],[c_2565,c_1240])).

cnf(c_662,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_592,c_4])).

cnf(c_684,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_4,c_603])).

cnf(c_2116,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_662,c_684])).

cnf(c_22195,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_22184,c_159,c_2116])).

cnf(c_23182,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k5_xboole_0(X1,X2))) = k2_zfmisc_1(X0,X2) ),
    inference(demodulation,[status(thm)],[c_22172,c_3,c_22195])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)
    | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2)
    | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_4,c_0])).

cnf(c_57,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2)
    | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(demodulation,[status(thm)],[c_35,c_10,c_11,c_55,c_56])).

cnf(c_527,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(demodulation,[status(thm)],[c_239,c_57])).

cnf(c_23618,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(demodulation,[status(thm)],[c_23182,c_527])).

cnf(c_23619,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(theory_normalisation,[status(thm)],[c_23618])).

cnf(c_943,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),X1)) = k5_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)) ),
    inference(superposition,[status(thm)],[c_55,c_239])).

cnf(c_23620,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(demodulation,[status(thm)],[c_23619,c_943])).

cnf(c_45466,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(demodulation,[status(thm)],[c_45459,c_23620])).

cnf(c_45467,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_45466])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:16:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 19.68/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.68/3.00  
% 19.68/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.68/3.00  
% 19.68/3.00  ------  iProver source info
% 19.68/3.00  
% 19.68/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.68/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.68/3.00  git: non_committed_changes: false
% 19.68/3.00  git: last_make_outside_of_git: false
% 19.68/3.00  
% 19.68/3.00  ------ 
% 19.68/3.00  
% 19.68/3.00  ------ Input Options
% 19.68/3.00  
% 19.68/3.00  --out_options                           all
% 19.68/3.00  --tptp_safe_out                         true
% 19.68/3.00  --problem_path                          ""
% 19.68/3.00  --include_path                          ""
% 19.68/3.00  --clausifier                            res/vclausify_rel
% 19.68/3.00  --clausifier_options                    ""
% 19.68/3.00  --stdin                                 false
% 19.68/3.00  --stats_out                             all
% 19.68/3.00  
% 19.68/3.00  ------ General Options
% 19.68/3.00  
% 19.68/3.00  --fof                                   false
% 19.68/3.00  --time_out_real                         305.
% 19.68/3.00  --time_out_virtual                      -1.
% 19.68/3.00  --symbol_type_check                     false
% 19.68/3.00  --clausify_out                          false
% 19.68/3.00  --sig_cnt_out                           false
% 19.68/3.00  --trig_cnt_out                          false
% 19.68/3.00  --trig_cnt_out_tolerance                1.
% 19.68/3.00  --trig_cnt_out_sk_spl                   false
% 19.68/3.00  --abstr_cl_out                          false
% 19.68/3.00  
% 19.68/3.00  ------ Global Options
% 19.68/3.00  
% 19.68/3.00  --schedule                              default
% 19.68/3.00  --add_important_lit                     false
% 19.68/3.00  --prop_solver_per_cl                    1000
% 19.68/3.00  --min_unsat_core                        false
% 19.68/3.00  --soft_assumptions                      false
% 19.68/3.00  --soft_lemma_size                       3
% 19.68/3.00  --prop_impl_unit_size                   0
% 19.68/3.00  --prop_impl_unit                        []
% 19.68/3.00  --share_sel_clauses                     true
% 19.68/3.00  --reset_solvers                         false
% 19.68/3.00  --bc_imp_inh                            [conj_cone]
% 19.68/3.00  --conj_cone_tolerance                   3.
% 19.68/3.00  --extra_neg_conj                        none
% 19.68/3.00  --large_theory_mode                     true
% 19.68/3.00  --prolific_symb_bound                   200
% 19.68/3.00  --lt_threshold                          2000
% 19.68/3.00  --clause_weak_htbl                      true
% 19.68/3.00  --gc_record_bc_elim                     false
% 19.68/3.00  
% 19.68/3.00  ------ Preprocessing Options
% 19.68/3.00  
% 19.68/3.00  --preprocessing_flag                    true
% 19.68/3.00  --time_out_prep_mult                    0.1
% 19.68/3.00  --splitting_mode                        input
% 19.68/3.00  --splitting_grd                         true
% 19.68/3.00  --splitting_cvd                         false
% 19.68/3.00  --splitting_cvd_svl                     false
% 19.68/3.00  --splitting_nvd                         32
% 19.68/3.00  --sub_typing                            true
% 19.68/3.00  --prep_gs_sim                           true
% 19.68/3.00  --prep_unflatten                        true
% 19.68/3.00  --prep_res_sim                          true
% 19.68/3.00  --prep_upred                            true
% 19.68/3.00  --prep_sem_filter                       exhaustive
% 19.68/3.00  --prep_sem_filter_out                   false
% 19.68/3.00  --pred_elim                             true
% 19.68/3.00  --res_sim_input                         true
% 19.68/3.00  --eq_ax_congr_red                       true
% 19.68/3.00  --pure_diseq_elim                       true
% 19.68/3.00  --brand_transform                       false
% 19.68/3.00  --non_eq_to_eq                          false
% 19.68/3.00  --prep_def_merge                        true
% 19.68/3.00  --prep_def_merge_prop_impl              false
% 19.68/3.00  --prep_def_merge_mbd                    true
% 19.68/3.00  --prep_def_merge_tr_red                 false
% 19.68/3.00  --prep_def_merge_tr_cl                  false
% 19.68/3.00  --smt_preprocessing                     true
% 19.68/3.00  --smt_ac_axioms                         fast
% 19.68/3.00  --preprocessed_out                      false
% 19.68/3.00  --preprocessed_stats                    false
% 19.68/3.00  
% 19.68/3.00  ------ Abstraction refinement Options
% 19.68/3.00  
% 19.68/3.00  --abstr_ref                             []
% 19.68/3.00  --abstr_ref_prep                        false
% 19.68/3.00  --abstr_ref_until_sat                   false
% 19.68/3.00  --abstr_ref_sig_restrict                funpre
% 19.68/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.68/3.00  --abstr_ref_under                       []
% 19.68/3.00  
% 19.68/3.00  ------ SAT Options
% 19.68/3.00  
% 19.68/3.00  --sat_mode                              false
% 19.68/3.00  --sat_fm_restart_options                ""
% 19.68/3.00  --sat_gr_def                            false
% 19.68/3.00  --sat_epr_types                         true
% 19.68/3.00  --sat_non_cyclic_types                  false
% 19.68/3.00  --sat_finite_models                     false
% 19.68/3.00  --sat_fm_lemmas                         false
% 19.68/3.00  --sat_fm_prep                           false
% 19.68/3.00  --sat_fm_uc_incr                        true
% 19.68/3.00  --sat_out_model                         small
% 19.68/3.00  --sat_out_clauses                       false
% 19.68/3.00  
% 19.68/3.00  ------ QBF Options
% 19.68/3.00  
% 19.68/3.00  --qbf_mode                              false
% 19.68/3.00  --qbf_elim_univ                         false
% 19.68/3.00  --qbf_dom_inst                          none
% 19.68/3.00  --qbf_dom_pre_inst                      false
% 19.68/3.00  --qbf_sk_in                             false
% 19.68/3.00  --qbf_pred_elim                         true
% 19.68/3.00  --qbf_split                             512
% 19.68/3.00  
% 19.68/3.00  ------ BMC1 Options
% 19.68/3.00  
% 19.68/3.00  --bmc1_incremental                      false
% 19.68/3.00  --bmc1_axioms                           reachable_all
% 19.68/3.00  --bmc1_min_bound                        0
% 19.68/3.00  --bmc1_max_bound                        -1
% 19.68/3.00  --bmc1_max_bound_default                -1
% 19.68/3.00  --bmc1_symbol_reachability              true
% 19.68/3.00  --bmc1_property_lemmas                  false
% 19.68/3.00  --bmc1_k_induction                      false
% 19.68/3.00  --bmc1_non_equiv_states                 false
% 19.68/3.00  --bmc1_deadlock                         false
% 19.68/3.00  --bmc1_ucm                              false
% 19.68/3.00  --bmc1_add_unsat_core                   none
% 19.68/3.00  --bmc1_unsat_core_children              false
% 19.68/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.68/3.00  --bmc1_out_stat                         full
% 19.68/3.00  --bmc1_ground_init                      false
% 19.68/3.00  --bmc1_pre_inst_next_state              false
% 19.68/3.00  --bmc1_pre_inst_state                   false
% 19.68/3.00  --bmc1_pre_inst_reach_state             false
% 19.68/3.00  --bmc1_out_unsat_core                   false
% 19.68/3.00  --bmc1_aig_witness_out                  false
% 19.68/3.00  --bmc1_verbose                          false
% 19.68/3.00  --bmc1_dump_clauses_tptp                false
% 19.68/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.68/3.00  --bmc1_dump_file                        -
% 19.68/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.68/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.68/3.00  --bmc1_ucm_extend_mode                  1
% 19.68/3.00  --bmc1_ucm_init_mode                    2
% 19.68/3.00  --bmc1_ucm_cone_mode                    none
% 19.68/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.68/3.00  --bmc1_ucm_relax_model                  4
% 19.68/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.68/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.68/3.00  --bmc1_ucm_layered_model                none
% 19.68/3.00  --bmc1_ucm_max_lemma_size               10
% 19.68/3.00  
% 19.68/3.00  ------ AIG Options
% 19.68/3.00  
% 19.68/3.00  --aig_mode                              false
% 19.68/3.00  
% 19.68/3.00  ------ Instantiation Options
% 19.68/3.00  
% 19.68/3.00  --instantiation_flag                    true
% 19.68/3.00  --inst_sos_flag                         true
% 19.68/3.00  --inst_sos_phase                        true
% 19.68/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.68/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.68/3.00  --inst_lit_sel_side                     num_symb
% 19.68/3.00  --inst_solver_per_active                1400
% 19.68/3.00  --inst_solver_calls_frac                1.
% 19.68/3.00  --inst_passive_queue_type               priority_queues
% 19.68/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.68/3.00  --inst_passive_queues_freq              [25;2]
% 19.68/3.00  --inst_dismatching                      true
% 19.68/3.00  --inst_eager_unprocessed_to_passive     true
% 19.68/3.00  --inst_prop_sim_given                   true
% 19.68/3.00  --inst_prop_sim_new                     false
% 19.68/3.00  --inst_subs_new                         false
% 19.68/3.00  --inst_eq_res_simp                      false
% 19.68/3.00  --inst_subs_given                       false
% 19.68/3.00  --inst_orphan_elimination               true
% 19.68/3.00  --inst_learning_loop_flag               true
% 19.68/3.00  --inst_learning_start                   3000
% 19.68/3.00  --inst_learning_factor                  2
% 19.68/3.00  --inst_start_prop_sim_after_learn       3
% 19.68/3.00  --inst_sel_renew                        solver
% 19.68/3.00  --inst_lit_activity_flag                true
% 19.68/3.00  --inst_restr_to_given                   false
% 19.68/3.00  --inst_activity_threshold               500
% 19.68/3.00  --inst_out_proof                        true
% 19.68/3.00  
% 19.68/3.00  ------ Resolution Options
% 19.68/3.00  
% 19.68/3.00  --resolution_flag                       true
% 19.68/3.00  --res_lit_sel                           adaptive
% 19.68/3.00  --res_lit_sel_side                      none
% 19.68/3.00  --res_ordering                          kbo
% 19.68/3.00  --res_to_prop_solver                    active
% 19.68/3.00  --res_prop_simpl_new                    false
% 19.68/3.00  --res_prop_simpl_given                  true
% 19.68/3.00  --res_passive_queue_type                priority_queues
% 19.68/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.68/3.00  --res_passive_queues_freq               [15;5]
% 19.68/3.00  --res_forward_subs                      full
% 19.68/3.00  --res_backward_subs                     full
% 19.68/3.00  --res_forward_subs_resolution           true
% 19.68/3.00  --res_backward_subs_resolution          true
% 19.68/3.00  --res_orphan_elimination                true
% 19.68/3.00  --res_time_limit                        2.
% 19.68/3.00  --res_out_proof                         true
% 19.68/3.00  
% 19.68/3.00  ------ Superposition Options
% 19.68/3.00  
% 19.68/3.00  --superposition_flag                    true
% 19.68/3.00  --sup_passive_queue_type                priority_queues
% 19.68/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.68/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.68/3.00  --demod_completeness_check              fast
% 19.68/3.00  --demod_use_ground                      true
% 19.68/3.00  --sup_to_prop_solver                    passive
% 19.68/3.00  --sup_prop_simpl_new                    true
% 19.68/3.00  --sup_prop_simpl_given                  true
% 19.68/3.00  --sup_fun_splitting                     true
% 19.68/3.00  --sup_smt_interval                      50000
% 19.68/3.00  
% 19.68/3.00  ------ Superposition Simplification Setup
% 19.68/3.00  
% 19.68/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.68/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.68/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.68/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.68/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.68/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.68/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.68/3.00  --sup_immed_triv                        [TrivRules]
% 19.68/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.00  --sup_immed_bw_main                     []
% 19.68/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.68/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.68/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.00  --sup_input_bw                          []
% 19.68/3.00  
% 19.68/3.00  ------ Combination Options
% 19.68/3.00  
% 19.68/3.00  --comb_res_mult                         3
% 19.68/3.00  --comb_sup_mult                         2
% 19.68/3.00  --comb_inst_mult                        10
% 19.68/3.00  
% 19.68/3.00  ------ Debug Options
% 19.68/3.00  
% 19.68/3.00  --dbg_backtrace                         false
% 19.68/3.00  --dbg_dump_prop_clauses                 false
% 19.68/3.00  --dbg_dump_prop_clauses_file            -
% 19.68/3.00  --dbg_out_stat                          false
% 19.68/3.00  ------ Parsing...
% 19.68/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.68/3.00  
% 19.68/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 19.68/3.00  
% 19.68/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.68/3.00  
% 19.68/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.68/3.00  ------ Proving...
% 19.68/3.00  ------ Problem Properties 
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  clauses                                 15
% 19.68/3.00  conjectures                             1
% 19.68/3.00  EPR                                     0
% 19.68/3.00  Horn                                    14
% 19.68/3.00  unary                                   13
% 19.68/3.00  binary                                  1
% 19.68/3.00  lits                                    18
% 19.68/3.00  lits eq                                 18
% 19.68/3.00  fd_pure                                 0
% 19.68/3.00  fd_pseudo                               0
% 19.68/3.00  fd_cond                                 1
% 19.68/3.00  fd_pseudo_cond                          0
% 19.68/3.00  AC symbols                              1
% 19.68/3.00  
% 19.68/3.00  ------ Schedule dynamic 5 is on 
% 19.68/3.00  
% 19.68/3.00  ------ pure equality problem: resolution off 
% 19.68/3.00  
% 19.68/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  ------ 
% 19.68/3.00  Current options:
% 19.68/3.00  ------ 
% 19.68/3.00  
% 19.68/3.00  ------ Input Options
% 19.68/3.00  
% 19.68/3.00  --out_options                           all
% 19.68/3.00  --tptp_safe_out                         true
% 19.68/3.00  --problem_path                          ""
% 19.68/3.00  --include_path                          ""
% 19.68/3.00  --clausifier                            res/vclausify_rel
% 19.68/3.00  --clausifier_options                    ""
% 19.68/3.00  --stdin                                 false
% 19.68/3.00  --stats_out                             all
% 19.68/3.00  
% 19.68/3.00  ------ General Options
% 19.68/3.00  
% 19.68/3.00  --fof                                   false
% 19.68/3.00  --time_out_real                         305.
% 19.68/3.00  --time_out_virtual                      -1.
% 19.68/3.00  --symbol_type_check                     false
% 19.68/3.00  --clausify_out                          false
% 19.68/3.00  --sig_cnt_out                           false
% 19.68/3.00  --trig_cnt_out                          false
% 19.68/3.00  --trig_cnt_out_tolerance                1.
% 19.68/3.00  --trig_cnt_out_sk_spl                   false
% 19.68/3.00  --abstr_cl_out                          false
% 19.68/3.00  
% 19.68/3.00  ------ Global Options
% 19.68/3.00  
% 19.68/3.00  --schedule                              default
% 19.68/3.00  --add_important_lit                     false
% 19.68/3.00  --prop_solver_per_cl                    1000
% 19.68/3.00  --min_unsat_core                        false
% 19.68/3.00  --soft_assumptions                      false
% 19.68/3.00  --soft_lemma_size                       3
% 19.68/3.00  --prop_impl_unit_size                   0
% 19.68/3.00  --prop_impl_unit                        []
% 19.68/3.00  --share_sel_clauses                     true
% 19.68/3.00  --reset_solvers                         false
% 19.68/3.00  --bc_imp_inh                            [conj_cone]
% 19.68/3.00  --conj_cone_tolerance                   3.
% 19.68/3.00  --extra_neg_conj                        none
% 19.68/3.00  --large_theory_mode                     true
% 19.68/3.00  --prolific_symb_bound                   200
% 19.68/3.00  --lt_threshold                          2000
% 19.68/3.00  --clause_weak_htbl                      true
% 19.68/3.00  --gc_record_bc_elim                     false
% 19.68/3.00  
% 19.68/3.00  ------ Preprocessing Options
% 19.68/3.00  
% 19.68/3.00  --preprocessing_flag                    true
% 19.68/3.00  --time_out_prep_mult                    0.1
% 19.68/3.00  --splitting_mode                        input
% 19.68/3.00  --splitting_grd                         true
% 19.68/3.00  --splitting_cvd                         false
% 19.68/3.00  --splitting_cvd_svl                     false
% 19.68/3.00  --splitting_nvd                         32
% 19.68/3.00  --sub_typing                            true
% 19.68/3.00  --prep_gs_sim                           true
% 19.68/3.00  --prep_unflatten                        true
% 19.68/3.00  --prep_res_sim                          true
% 19.68/3.00  --prep_upred                            true
% 19.68/3.00  --prep_sem_filter                       exhaustive
% 19.68/3.00  --prep_sem_filter_out                   false
% 19.68/3.00  --pred_elim                             true
% 19.68/3.00  --res_sim_input                         true
% 19.68/3.00  --eq_ax_congr_red                       true
% 19.68/3.00  --pure_diseq_elim                       true
% 19.68/3.00  --brand_transform                       false
% 19.68/3.00  --non_eq_to_eq                          false
% 19.68/3.00  --prep_def_merge                        true
% 19.68/3.00  --prep_def_merge_prop_impl              false
% 19.68/3.00  --prep_def_merge_mbd                    true
% 19.68/3.00  --prep_def_merge_tr_red                 false
% 19.68/3.00  --prep_def_merge_tr_cl                  false
% 19.68/3.00  --smt_preprocessing                     true
% 19.68/3.00  --smt_ac_axioms                         fast
% 19.68/3.00  --preprocessed_out                      false
% 19.68/3.00  --preprocessed_stats                    false
% 19.68/3.00  
% 19.68/3.00  ------ Abstraction refinement Options
% 19.68/3.00  
% 19.68/3.00  --abstr_ref                             []
% 19.68/3.00  --abstr_ref_prep                        false
% 19.68/3.00  --abstr_ref_until_sat                   false
% 19.68/3.00  --abstr_ref_sig_restrict                funpre
% 19.68/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.68/3.00  --abstr_ref_under                       []
% 19.68/3.00  
% 19.68/3.00  ------ SAT Options
% 19.68/3.00  
% 19.68/3.00  --sat_mode                              false
% 19.68/3.00  --sat_fm_restart_options                ""
% 19.68/3.00  --sat_gr_def                            false
% 19.68/3.00  --sat_epr_types                         true
% 19.68/3.00  --sat_non_cyclic_types                  false
% 19.68/3.00  --sat_finite_models                     false
% 19.68/3.00  --sat_fm_lemmas                         false
% 19.68/3.00  --sat_fm_prep                           false
% 19.68/3.00  --sat_fm_uc_incr                        true
% 19.68/3.00  --sat_out_model                         small
% 19.68/3.00  --sat_out_clauses                       false
% 19.68/3.00  
% 19.68/3.00  ------ QBF Options
% 19.68/3.00  
% 19.68/3.00  --qbf_mode                              false
% 19.68/3.00  --qbf_elim_univ                         false
% 19.68/3.00  --qbf_dom_inst                          none
% 19.68/3.00  --qbf_dom_pre_inst                      false
% 19.68/3.00  --qbf_sk_in                             false
% 19.68/3.00  --qbf_pred_elim                         true
% 19.68/3.00  --qbf_split                             512
% 19.68/3.00  
% 19.68/3.00  ------ BMC1 Options
% 19.68/3.00  
% 19.68/3.00  --bmc1_incremental                      false
% 19.68/3.00  --bmc1_axioms                           reachable_all
% 19.68/3.00  --bmc1_min_bound                        0
% 19.68/3.00  --bmc1_max_bound                        -1
% 19.68/3.00  --bmc1_max_bound_default                -1
% 19.68/3.00  --bmc1_symbol_reachability              true
% 19.68/3.00  --bmc1_property_lemmas                  false
% 19.68/3.00  --bmc1_k_induction                      false
% 19.68/3.00  --bmc1_non_equiv_states                 false
% 19.68/3.00  --bmc1_deadlock                         false
% 19.68/3.00  --bmc1_ucm                              false
% 19.68/3.00  --bmc1_add_unsat_core                   none
% 19.68/3.00  --bmc1_unsat_core_children              false
% 19.68/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.68/3.00  --bmc1_out_stat                         full
% 19.68/3.00  --bmc1_ground_init                      false
% 19.68/3.00  --bmc1_pre_inst_next_state              false
% 19.68/3.00  --bmc1_pre_inst_state                   false
% 19.68/3.00  --bmc1_pre_inst_reach_state             false
% 19.68/3.00  --bmc1_out_unsat_core                   false
% 19.68/3.00  --bmc1_aig_witness_out                  false
% 19.68/3.00  --bmc1_verbose                          false
% 19.68/3.00  --bmc1_dump_clauses_tptp                false
% 19.68/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.68/3.00  --bmc1_dump_file                        -
% 19.68/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.68/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.68/3.00  --bmc1_ucm_extend_mode                  1
% 19.68/3.00  --bmc1_ucm_init_mode                    2
% 19.68/3.00  --bmc1_ucm_cone_mode                    none
% 19.68/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.68/3.00  --bmc1_ucm_relax_model                  4
% 19.68/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.68/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.68/3.00  --bmc1_ucm_layered_model                none
% 19.68/3.00  --bmc1_ucm_max_lemma_size               10
% 19.68/3.00  
% 19.68/3.00  ------ AIG Options
% 19.68/3.00  
% 19.68/3.00  --aig_mode                              false
% 19.68/3.00  
% 19.68/3.00  ------ Instantiation Options
% 19.68/3.00  
% 19.68/3.00  --instantiation_flag                    true
% 19.68/3.00  --inst_sos_flag                         true
% 19.68/3.00  --inst_sos_phase                        true
% 19.68/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.68/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.68/3.00  --inst_lit_sel_side                     none
% 19.68/3.00  --inst_solver_per_active                1400
% 19.68/3.00  --inst_solver_calls_frac                1.
% 19.68/3.00  --inst_passive_queue_type               priority_queues
% 19.68/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.68/3.00  --inst_passive_queues_freq              [25;2]
% 19.68/3.00  --inst_dismatching                      true
% 19.68/3.00  --inst_eager_unprocessed_to_passive     true
% 19.68/3.00  --inst_prop_sim_given                   true
% 19.68/3.00  --inst_prop_sim_new                     false
% 19.68/3.00  --inst_subs_new                         false
% 19.68/3.00  --inst_eq_res_simp                      false
% 19.68/3.00  --inst_subs_given                       false
% 19.68/3.00  --inst_orphan_elimination               true
% 19.68/3.00  --inst_learning_loop_flag               true
% 19.68/3.00  --inst_learning_start                   3000
% 19.68/3.00  --inst_learning_factor                  2
% 19.68/3.00  --inst_start_prop_sim_after_learn       3
% 19.68/3.00  --inst_sel_renew                        solver
% 19.68/3.00  --inst_lit_activity_flag                true
% 19.68/3.00  --inst_restr_to_given                   false
% 19.68/3.00  --inst_activity_threshold               500
% 19.68/3.00  --inst_out_proof                        true
% 19.68/3.00  
% 19.68/3.00  ------ Resolution Options
% 19.68/3.00  
% 19.68/3.00  --resolution_flag                       false
% 19.68/3.00  --res_lit_sel                           adaptive
% 19.68/3.00  --res_lit_sel_side                      none
% 19.68/3.00  --res_ordering                          kbo
% 19.68/3.00  --res_to_prop_solver                    active
% 19.68/3.00  --res_prop_simpl_new                    false
% 19.68/3.00  --res_prop_simpl_given                  true
% 19.68/3.00  --res_passive_queue_type                priority_queues
% 19.68/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.68/3.00  --res_passive_queues_freq               [15;5]
% 19.68/3.00  --res_forward_subs                      full
% 19.68/3.00  --res_backward_subs                     full
% 19.68/3.00  --res_forward_subs_resolution           true
% 19.68/3.00  --res_backward_subs_resolution          true
% 19.68/3.00  --res_orphan_elimination                true
% 19.68/3.00  --res_time_limit                        2.
% 19.68/3.00  --res_out_proof                         true
% 19.68/3.00  
% 19.68/3.00  ------ Superposition Options
% 19.68/3.00  
% 19.68/3.00  --superposition_flag                    true
% 19.68/3.00  --sup_passive_queue_type                priority_queues
% 19.68/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.68/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.68/3.00  --demod_completeness_check              fast
% 19.68/3.00  --demod_use_ground                      true
% 19.68/3.00  --sup_to_prop_solver                    passive
% 19.68/3.00  --sup_prop_simpl_new                    true
% 19.68/3.00  --sup_prop_simpl_given                  true
% 19.68/3.00  --sup_fun_splitting                     true
% 19.68/3.00  --sup_smt_interval                      50000
% 19.68/3.00  
% 19.68/3.00  ------ Superposition Simplification Setup
% 19.68/3.00  
% 19.68/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.68/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.68/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.68/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.68/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.68/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.68/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.68/3.00  --sup_immed_triv                        [TrivRules]
% 19.68/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.00  --sup_immed_bw_main                     []
% 19.68/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.68/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.68/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.00  --sup_input_bw                          []
% 19.68/3.00  
% 19.68/3.00  ------ Combination Options
% 19.68/3.00  
% 19.68/3.00  --comb_res_mult                         3
% 19.68/3.00  --comb_sup_mult                         2
% 19.68/3.00  --comb_inst_mult                        10
% 19.68/3.00  
% 19.68/3.00  ------ Debug Options
% 19.68/3.00  
% 19.68/3.00  --dbg_backtrace                         false
% 19.68/3.00  --dbg_dump_prop_clauses                 false
% 19.68/3.00  --dbg_dump_prop_clauses_file            -
% 19.68/3.00  --dbg_out_stat                          false
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  ------ Proving...
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  % SZS status Theorem for theBenchmark.p
% 19.68/3.00  
% 19.68/3.00   Resolution empty clause
% 19.68/3.00  
% 19.68/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.68/3.00  
% 19.68/3.00  fof(f1,axiom,(
% 19.68/3.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f29,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f1])).
% 19.68/3.00  
% 19.68/3.00  fof(f8,axiom,(
% 19.68/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f36,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f8])).
% 19.68/3.00  
% 19.68/3.00  fof(f9,axiom,(
% 19.68/3.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f37,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f9])).
% 19.68/3.00  
% 19.68/3.00  fof(f16,axiom,(
% 19.68/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f44,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f16])).
% 19.68/3.00  
% 19.68/3.00  fof(f10,axiom,(
% 19.68/3.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f38,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f10])).
% 19.68/3.00  
% 19.68/3.00  fof(f11,axiom,(
% 19.68/3.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f39,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f11])).
% 19.68/3.00  
% 19.68/3.00  fof(f12,axiom,(
% 19.68/3.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f40,plain,(
% 19.68/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f12])).
% 19.68/3.00  
% 19.68/3.00  fof(f13,axiom,(
% 19.68/3.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f41,plain,(
% 19.68/3.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f13])).
% 19.68/3.00  
% 19.68/3.00  fof(f14,axiom,(
% 19.68/3.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f42,plain,(
% 19.68/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f14])).
% 19.68/3.00  
% 19.68/3.00  fof(f15,axiom,(
% 19.68/3.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f43,plain,(
% 19.68/3.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f15])).
% 19.68/3.00  
% 19.68/3.00  fof(f53,plain,(
% 19.68/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 19.68/3.00    inference(definition_unfolding,[],[f42,f43])).
% 19.68/3.00  
% 19.68/3.00  fof(f54,plain,(
% 19.68/3.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 19.68/3.00    inference(definition_unfolding,[],[f41,f53])).
% 19.68/3.00  
% 19.68/3.00  fof(f55,plain,(
% 19.68/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 19.68/3.00    inference(definition_unfolding,[],[f40,f54])).
% 19.68/3.00  
% 19.68/3.00  fof(f56,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.68/3.00    inference(definition_unfolding,[],[f39,f55])).
% 19.68/3.00  
% 19.68/3.00  fof(f57,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 19.68/3.00    inference(definition_unfolding,[],[f38,f56])).
% 19.68/3.00  
% 19.68/3.00  fof(f58,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.68/3.00    inference(definition_unfolding,[],[f44,f57])).
% 19.68/3.00  
% 19.68/3.00  fof(f59,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 19.68/3.00    inference(definition_unfolding,[],[f37,f58])).
% 19.68/3.00  
% 19.68/3.00  fof(f63,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 19.68/3.00    inference(definition_unfolding,[],[f36,f58,f58,f59])).
% 19.68/3.00  
% 19.68/3.00  fof(f6,axiom,(
% 19.68/3.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f34,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f6])).
% 19.68/3.00  
% 19.68/3.00  fof(f19,axiom,(
% 19.68/3.00    ! [X0,X1,X2] : (k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) & k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k3_xboole_0(X0,X1),X2))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f50,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f19])).
% 19.68/3.00  
% 19.68/3.00  fof(f67,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2)) )),
% 19.68/3.00    inference(definition_unfolding,[],[f50,f59,f59])).
% 19.68/3.00  
% 19.68/3.00  fof(f18,axiom,(
% 19.68/3.00    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f48,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f18])).
% 19.68/3.00  
% 19.68/3.00  fof(f65,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) )),
% 19.68/3.00    inference(definition_unfolding,[],[f48,f58,f58])).
% 19.68/3.00  
% 19.68/3.00  fof(f5,axiom,(
% 19.68/3.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f33,plain,(
% 19.68/3.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.68/3.00    inference(cnf_transformation,[],[f5])).
% 19.68/3.00  
% 19.68/3.00  fof(f7,axiom,(
% 19.68/3.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f35,plain,(
% 19.68/3.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 19.68/3.00    inference(cnf_transformation,[],[f7])).
% 19.68/3.00  
% 19.68/3.00  fof(f17,axiom,(
% 19.68/3.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f25,plain,(
% 19.68/3.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.68/3.00    inference(nnf_transformation,[],[f17])).
% 19.68/3.00  
% 19.68/3.00  fof(f26,plain,(
% 19.68/3.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.68/3.00    inference(flattening,[],[f25])).
% 19.68/3.00  
% 19.68/3.00  fof(f46,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 19.68/3.00    inference(cnf_transformation,[],[f26])).
% 19.68/3.00  
% 19.68/3.00  fof(f70,plain,(
% 19.68/3.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 19.68/3.00    inference(equality_resolution,[],[f46])).
% 19.68/3.00  
% 19.68/3.00  fof(f51,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k3_xboole_0(X0,X1))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f19])).
% 19.68/3.00  
% 19.68/3.00  fof(f66,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)),k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 19.68/3.00    inference(definition_unfolding,[],[f51,f59,f59])).
% 19.68/3.00  
% 19.68/3.00  fof(f49,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f18])).
% 19.68/3.00  
% 19.68/3.00  fof(f64,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 19.68/3.00    inference(definition_unfolding,[],[f49,f58,f58])).
% 19.68/3.00  
% 19.68/3.00  fof(f47,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 19.68/3.00    inference(cnf_transformation,[],[f26])).
% 19.68/3.00  
% 19.68/3.00  fof(f69,plain,(
% 19.68/3.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 19.68/3.00    inference(equality_resolution,[],[f47])).
% 19.68/3.00  
% 19.68/3.00  fof(f20,conjecture,(
% 19.68/3.00    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f21,negated_conjecture,(
% 19.68/3.00    ~! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 19.68/3.00    inference(negated_conjecture,[],[f20])).
% 19.68/3.00  
% 19.68/3.00  fof(f24,plain,(
% 19.68/3.00    ? [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) != k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) | k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 19.68/3.00    inference(ennf_transformation,[],[f21])).
% 19.68/3.00  
% 19.68/3.00  fof(f27,plain,(
% 19.68/3.00    ? [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) != k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) | k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) => (k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) != k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) | k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2))),
% 19.68/3.00    introduced(choice_axiom,[])).
% 19.68/3.00  
% 19.68/3.00  fof(f28,plain,(
% 19.68/3.00    k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) != k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) | k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2)),
% 19.68/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).
% 19.68/3.00  
% 19.68/3.00  fof(f52,plain,(
% 19.68/3.00    k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) != k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) | k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2)),
% 19.68/3.00    inference(cnf_transformation,[],[f28])).
% 19.68/3.00  
% 19.68/3.00  fof(f4,axiom,(
% 19.68/3.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f32,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f4])).
% 19.68/3.00  
% 19.68/3.00  fof(f60,plain,(
% 19.68/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 19.68/3.00    inference(definition_unfolding,[],[f32,f59])).
% 19.68/3.00  
% 19.68/3.00  fof(f68,plain,(
% 19.68/3.00    k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)),
% 19.68/3.00    inference(definition_unfolding,[],[f52,f60,f60,f60,f60])).
% 19.68/3.00  
% 19.68/3.00  cnf(c_0,plain,
% 19.68/3.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.68/3.00      inference(cnf_transformation,[],[f29]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_6,plain,
% 19.68/3.00      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 19.68/3.00      inference(cnf_transformation,[],[f63]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.68/3.00      inference(cnf_transformation,[],[f34]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_38,plain,
% 19.68/3.00      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 19.68/3.00      inference(theory_normalisation,[status(thm)],[c_6,c_4,c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_319,plain,
% 19.68/3.00      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_0,c_38]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_13,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f67]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_36,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X2,X1),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),X1) ),
% 19.68/3.00      inference(theory_normalisation,[status(thm)],[c_13,c_4,c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_11,plain,
% 19.68/3.00      ( k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f65]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_55,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),X1) ),
% 19.68/3.00      inference(light_normalisation,[status(thm)],[c_36,c_11]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5529,plain,
% 19.68/3.00      ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))))),X2) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,X1),X2),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),X2),k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X2))) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_319,c_55]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5534,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,X1),X2),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),X2),k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X2))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),X2) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_5529,c_319]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_62,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_3,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.68/3.00      inference(cnf_transformation,[],[f33]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_61,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_843,plain,
% 19.68/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_3,c_61]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1156,plain,
% 19.68/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_62,c_843]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_60,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1031,plain,
% 19.68/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_843,c_60]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1177,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 19.68/3.00      inference(light_normalisation,[status(thm)],[c_1156,c_1031]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5,plain,
% 19.68/3.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.68/3.00      inference(cnf_transformation,[],[f35]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_232,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_159,plain,
% 19.68/3.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_239,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_232,c_159]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_530,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_0,c_239]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_592,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_239,c_530]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_650,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X0,X1) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_4,c_592]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1734,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X2),k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_55,c_650]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5535,plain,
% 19.68/3.00      ( k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X2) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,X0),X2),k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_5534,c_1177,c_1734]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_8,plain,
% 19.68/3.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.68/3.00      inference(cnf_transformation,[],[f70]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_603,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_530,c_530]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_865,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X1,X0) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_61,c_603]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5536,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,X1),X2),k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X0,X2))) = k1_xboole_0 ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_5535,c_5,c_8,c_239,c_865]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_846,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_603,c_61]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_883,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 19.68/3.00      inference(light_normalisation,[status(thm)],[c_846,c_4]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2686,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,X2) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_4,c_883]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_45411,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,k2_zfmisc_1(k5_xboole_0(X1,X2),X3)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_5536,c_2686]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_45458,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,k2_zfmisc_1(k5_xboole_0(X1,X2),X3)),X0) = k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
% 19.68/3.00      inference(light_normalisation,[status(thm)],[c_45411,c_3]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_45459,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X2),X1) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_45458,c_603]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 19.68/3.00      inference(cnf_transformation,[],[f66]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_37,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X0,X2),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
% 19.68/3.00      inference(theory_normalisation,[status(thm)],[c_12,c_4,c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_10,plain,
% 19.68/3.00      ( k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 19.68/3.00      inference(cnf_transformation,[],[f64]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_56,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
% 19.68/3.00      inference(light_normalisation,[status(thm)],[c_37,c_10]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2509,plain,
% 19.68/3.00      ( k2_zfmisc_1(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_38,c_56]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2539,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_56,c_650]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2562,plain,
% 19.68/3.00      ( k2_zfmisc_1(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_2509,c_2539]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2563,plain,
% 19.68/3.00      ( k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))),k3_tarski(k6_enumset1(k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,X1),k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,X1)),k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X1))) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_2562,c_1177]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1159,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_62,c_239]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2564,plain,
% 19.68/3.00      ( k2_zfmisc_1(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_2563,c_1159,c_1177]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_7,plain,
% 19.68/3.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.68/3.00      inference(cnf_transformation,[],[f69]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2565,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k1_xboole_0 ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_2564,c_5,c_7,c_38]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_867,plain,
% 19.68/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_61,c_239]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_22172,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_xboole_0) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_2565,c_867]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_534,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_4,c_239]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1240,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_4,c_534]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_22184,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k2_zfmisc_1(X2,k5_xboole_0(X3,X4)))),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,X4)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_2565,c_1240]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_662,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_592,c_4]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_684,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_4,c_603]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2116,plain,
% 19.68/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_662,c_684]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_22195,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k5_xboole_0(X1,X2)) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_22184,c_159,c_2116]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_23182,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k5_xboole_0(X1,X2))) = k2_zfmisc_1(X0,X2) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_22172,c_3,c_22195]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_14,negated_conjecture,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)
% 19.68/3.00      | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) ),
% 19.68/3.00      inference(cnf_transformation,[],[f68]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_35,negated_conjecture,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2)
% 19.68/3.00      | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
% 19.68/3.00      inference(theory_normalisation,[status(thm)],[c_14,c_4,c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_57,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2)
% 19.68/3.00      | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_35,c_10,c_11,c_55,c_56]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_527,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
% 19.68/3.00      | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_239,c_57]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_23618,plain,
% 19.68/3.00      ( k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
% 19.68/3.00      | k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_23182,c_527]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_23619,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
% 19.68/3.00      inference(theory_normalisation,[status(thm)],[c_23618]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_943,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),X1)) = k5_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_55,c_239]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_23620,plain,
% 19.68/3.00      ( k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_23619,c_943]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_45466,plain,
% 19.68/3.00      ( k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_45459,c_23620]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_45467,plain,
% 19.68/3.00      ( $false ),
% 19.68/3.00      inference(equality_resolution_simp,[status(thm)],[c_45466]) ).
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.68/3.00  
% 19.68/3.00  ------                               Statistics
% 19.68/3.00  
% 19.68/3.00  ------ General
% 19.68/3.00  
% 19.68/3.00  abstr_ref_over_cycles:                  0
% 19.68/3.00  abstr_ref_under_cycles:                 0
% 19.68/3.00  gc_basic_clause_elim:                   0
% 19.68/3.00  forced_gc_time:                         0
% 19.68/3.00  parsing_time:                           0.011
% 19.68/3.00  unif_index_cands_time:                  0.
% 19.68/3.00  unif_index_add_time:                    0.
% 19.68/3.00  orderings_time:                         0.
% 19.68/3.00  out_proof_time:                         0.011
% 19.68/3.00  total_time:                             2.227
% 19.68/3.00  num_of_symbols:                         39
% 19.68/3.00  num_of_terms:                           101493
% 19.68/3.00  
% 19.68/3.00  ------ Preprocessing
% 19.68/3.00  
% 19.68/3.00  num_of_splits:                          0
% 19.68/3.00  num_of_split_atoms:                     0
% 19.68/3.00  num_of_reused_defs:                     0
% 19.68/3.00  num_eq_ax_congr_red:                    0
% 19.68/3.00  num_of_sem_filtered_clauses:            0
% 19.68/3.00  num_of_subtypes:                        0
% 19.68/3.00  monotx_restored_types:                  0
% 19.68/3.00  sat_num_of_epr_types:                   0
% 19.68/3.00  sat_num_of_non_cyclic_types:            0
% 19.68/3.00  sat_guarded_non_collapsed_types:        0
% 19.68/3.00  num_pure_diseq_elim:                    0
% 19.68/3.00  simp_replaced_by:                       0
% 19.68/3.00  res_preprocessed:                       36
% 19.68/3.00  prep_upred:                             0
% 19.68/3.00  prep_unflattend:                        0
% 19.68/3.00  smt_new_axioms:                         0
% 19.68/3.00  pred_elim_cands:                        0
% 19.68/3.00  pred_elim:                              0
% 19.68/3.00  pred_elim_cl:                           0
% 19.68/3.00  pred_elim_cycles:                       0
% 19.68/3.00  merged_defs:                            0
% 19.68/3.00  merged_defs_ncl:                        0
% 19.68/3.00  bin_hyper_res:                          0
% 19.68/3.00  prep_cycles:                            2
% 19.68/3.00  pred_elim_time:                         0.
% 19.68/3.00  splitting_time:                         0.
% 19.68/3.00  sem_filter_time:                        0.
% 19.68/3.00  monotx_time:                            0.
% 19.68/3.00  subtype_inf_time:                       0.
% 19.68/3.00  
% 19.68/3.00  ------ Problem properties
% 19.68/3.00  
% 19.68/3.00  clauses:                                15
% 19.68/3.00  conjectures:                            1
% 19.68/3.00  epr:                                    0
% 19.68/3.00  horn:                                   14
% 19.68/3.00  ground:                                 1
% 19.68/3.00  unary:                                  13
% 19.68/3.00  binary:                                 1
% 19.68/3.00  lits:                                   18
% 19.68/3.00  lits_eq:                                18
% 19.68/3.00  fd_pure:                                0
% 19.68/3.00  fd_pseudo:                              0
% 19.68/3.00  fd_cond:                                1
% 19.68/3.00  fd_pseudo_cond:                         0
% 19.68/3.00  ac_symbols:                             1
% 19.68/3.00  
% 19.68/3.00  ------ Propositional Solver
% 19.68/3.00  
% 19.68/3.00  prop_solver_calls:                      24
% 19.68/3.00  prop_fast_solver_calls:                 238
% 19.68/3.00  smt_solver_calls:                       0
% 19.68/3.00  smt_fast_solver_calls:                  0
% 19.68/3.00  prop_num_of_clauses:                    4279
% 19.68/3.00  prop_preprocess_simplified:             4768
% 19.68/3.00  prop_fo_subsumed:                       0
% 19.68/3.00  prop_solver_time:                       0.
% 19.68/3.00  smt_solver_time:                        0.
% 19.68/3.00  smt_fast_solver_time:                   0.
% 19.68/3.00  prop_fast_solver_time:                  0.
% 19.68/3.00  prop_unsat_core_time:                   0.
% 19.68/3.00  
% 19.68/3.00  ------ QBF
% 19.68/3.00  
% 19.68/3.00  qbf_q_res:                              0
% 19.68/3.00  qbf_num_tautologies:                    0
% 19.68/3.00  qbf_prep_cycles:                        0
% 19.68/3.00  
% 19.68/3.00  ------ BMC1
% 19.68/3.00  
% 19.68/3.00  bmc1_current_bound:                     -1
% 19.68/3.00  bmc1_last_solved_bound:                 -1
% 19.68/3.00  bmc1_unsat_core_size:                   -1
% 19.68/3.00  bmc1_unsat_core_parents_size:           -1
% 19.68/3.00  bmc1_merge_next_fun:                    0
% 19.68/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.68/3.00  
% 19.68/3.00  ------ Instantiation
% 19.68/3.00  
% 19.68/3.00  inst_num_of_clauses:                    1105
% 19.68/3.00  inst_num_in_passive:                    178
% 19.68/3.00  inst_num_in_active:                     485
% 19.68/3.00  inst_num_in_unprocessed:                442
% 19.68/3.00  inst_num_of_loops:                      530
% 19.68/3.00  inst_num_of_learning_restarts:          0
% 19.68/3.00  inst_num_moves_active_passive:          40
% 19.68/3.00  inst_lit_activity:                      0
% 19.68/3.00  inst_lit_activity_moves:                0
% 19.68/3.00  inst_num_tautologies:                   0
% 19.68/3.00  inst_num_prop_implied:                  0
% 19.68/3.00  inst_num_existing_simplified:           0
% 19.68/3.00  inst_num_eq_res_simplified:             0
% 19.68/3.00  inst_num_child_elim:                    0
% 19.68/3.00  inst_num_of_dismatching_blockings:      271
% 19.68/3.00  inst_num_of_non_proper_insts:           1292
% 19.68/3.00  inst_num_of_duplicates:                 0
% 19.68/3.00  inst_inst_num_from_inst_to_res:         0
% 19.68/3.00  inst_dismatching_checking_time:         0.
% 19.68/3.00  
% 19.68/3.00  ------ Resolution
% 19.68/3.00  
% 19.68/3.00  res_num_of_clauses:                     0
% 19.68/3.00  res_num_in_passive:                     0
% 19.68/3.00  res_num_in_active:                      0
% 19.68/3.00  res_num_of_loops:                       38
% 19.68/3.00  res_forward_subset_subsumed:            424
% 19.68/3.00  res_backward_subset_subsumed:           0
% 19.68/3.00  res_forward_subsumed:                   0
% 19.68/3.00  res_backward_subsumed:                  0
% 19.68/3.00  res_forward_subsumption_resolution:     0
% 19.68/3.00  res_backward_subsumption_resolution:    0
% 19.68/3.00  res_clause_to_clause_subsumption:       98324
% 19.68/3.00  res_orphan_elimination:                 0
% 19.68/3.00  res_tautology_del:                      144
% 19.68/3.00  res_num_eq_res_simplified:              0
% 19.68/3.00  res_num_sel_changes:                    0
% 19.68/3.00  res_moves_from_active_to_pass:          0
% 19.68/3.00  
% 19.68/3.00  ------ Superposition
% 19.68/3.00  
% 19.68/3.00  sup_time_total:                         0.
% 19.68/3.00  sup_time_generating:                    0.
% 19.68/3.00  sup_time_sim_full:                      0.
% 19.68/3.00  sup_time_sim_immed:                     0.
% 19.68/3.00  
% 19.68/3.00  sup_num_of_clauses:                     2161
% 19.68/3.00  sup_num_in_active:                      98
% 19.68/3.00  sup_num_in_passive:                     2063
% 19.68/3.00  sup_num_of_loops:                       105
% 19.68/3.00  sup_fw_superposition:                   15590
% 19.68/3.00  sup_bw_superposition:                   10725
% 19.68/3.00  sup_immediate_simplified:               11618
% 19.68/3.00  sup_given_eliminated:                   2
% 19.68/3.00  comparisons_done:                       0
% 19.68/3.00  comparisons_avoided:                    0
% 19.68/3.00  
% 19.68/3.00  ------ Simplifications
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  sim_fw_subset_subsumed:                 0
% 19.68/3.00  sim_bw_subset_subsumed:                 0
% 19.68/3.00  sim_fw_subsumed:                        476
% 19.68/3.00  sim_bw_subsumed:                        0
% 19.68/3.00  sim_fw_subsumption_res:                 0
% 19.68/3.00  sim_bw_subsumption_res:                 0
% 19.68/3.00  sim_tautology_del:                      0
% 19.68/3.00  sim_eq_tautology_del:                   2544
% 19.68/3.00  sim_eq_res_simp:                        0
% 19.68/3.00  sim_fw_demodulated:                     12045
% 19.68/3.00  sim_bw_demodulated:                     30
% 19.68/3.00  sim_light_normalised:                   2842
% 19.68/3.00  sim_joinable_taut:                      484
% 19.68/3.00  sim_joinable_simp:                      1
% 19.68/3.00  sim_ac_normalised:                      0
% 19.68/3.00  sim_smt_subsumption:                    0
% 19.68/3.00  
%------------------------------------------------------------------------------
