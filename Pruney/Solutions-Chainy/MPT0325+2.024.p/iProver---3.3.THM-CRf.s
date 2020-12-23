%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:49 EST 2020

% Result     : Theorem 51.72s
% Output     : CNFRefutation 51.72s
% Verified   : 
% Statistics : Number of formulae       :  145 (9272 expanded)
%              Number of clauses        :  100 (4307 expanded)
%              Number of leaves         :   15 (2379 expanded)
%              Depth                    :   31
%              Number of atoms          :  216 (10164 expanded)
%              Number of equality atoms :  178 (9409 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28])).

fof(f52,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f33])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3))),k3_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3))),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1)))) ),
    inference(definition_unfolding,[],[f51,f33,f55,f33,f33])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f34,f55])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f53,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_292,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_294,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_511,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_292,c_294])).

cnf(c_13,plain,
    ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k3_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_556,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_512,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_562,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_556,c_512])).

cnf(c_769,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_562])).

cnf(c_998,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X1))),k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X3,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X1) ),
    inference(superposition,[status(thm)],[c_13,c_769])).

cnf(c_26033,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1))),k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(superposition,[status(thm)],[c_511,c_998])).

cnf(c_303,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1666,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6,c_303])).

cnf(c_772,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_7,c_562])).

cnf(c_2936,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1666,c_772])).

cnf(c_2992,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_2936,c_6])).

cnf(c_5928,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2992,c_1666])).

cnf(c_1825,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_1666])).

cnf(c_7930,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
    inference(superposition,[status(thm)],[c_1825,c_7])).

cnf(c_304,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1929,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_304,c_1666])).

cnf(c_1942,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_304,c_1666])).

cnf(c_302,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1852,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1666,c_302])).

cnf(c_1953,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_1942,c_1852])).

cnf(c_1957,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_1929,c_1953])).

cnf(c_792,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_562,c_769])).

cnf(c_864,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_792])).

cnf(c_4339,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_0,c_864])).

cnf(c_6231,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
    inference(superposition,[status(thm)],[c_4339,c_7])).

cnf(c_870,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_792,c_7])).

cnf(c_4587,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_870,c_870])).

cnf(c_6299,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_6231,c_4587])).

cnf(c_7990,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3))) ),
    inference(demodulation,[status(thm)],[c_7930,c_1666,c_1957,c_6299])).

cnf(c_26201,plain,
    ( k5_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(demodulation,[status(thm)],[c_26033,c_8,c_5928,c_7990])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4586,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_870,c_3])).

cnf(c_29210,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k5_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)))) = k5_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) ),
    inference(superposition,[status(thm)],[c_26201,c_4586])).

cnf(c_29226,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) = k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) ),
    inference(superposition,[status(thm)],[c_26201,c_769])).

cnf(c_29241,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) = k5_xboole_0(X0,k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1))) ),
    inference(superposition,[status(thm)],[c_26201,c_864])).

cnf(c_2928,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
    inference(superposition,[status(thm)],[c_7,c_772])).

cnf(c_10723,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X3,X2)))) = X3 ),
    inference(superposition,[status(thm)],[c_0,c_2928])).

cnf(c_29264,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))))),k5_xboole_0(X0,k5_xboole_0(X1,k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)))) = k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) ),
    inference(superposition,[status(thm)],[c_26201,c_10723])).

cnf(c_10739,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_769,c_2928])).

cnf(c_29269,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) ),
    inference(demodulation,[status(thm)],[c_29264,c_10739])).

cnf(c_29779,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))))) = k5_xboole_0(k5_xboole_0(X0,k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) ),
    inference(light_normalisation,[status(thm)],[c_29241,c_29269])).

cnf(c_29223,plain,
    ( k5_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),X0)) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),X0) ),
    inference(superposition,[status(thm)],[c_26201,c_7])).

cnf(c_29805,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),X0)) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),X0) ),
    inference(demodulation,[status(thm)],[c_29223,c_29226])).

cnf(c_29817,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1))) = k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))))) ),
    inference(demodulation,[status(thm)],[c_29210,c_29226,c_29779,c_29805])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_29818,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29817,c_5,c_8,c_769])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31478,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_29818,c_12])).

cnf(c_1625,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_302,c_3])).

cnf(c_4791,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X2),X0))))) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_1625])).

cnf(c_14111,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X2,X1),X0))))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_4791])).

cnf(c_31707,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))))) = X0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_31478,c_14111])).

cnf(c_547,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_3])).

cnf(c_551,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_547,c_6,c_512])).

cnf(c_31773,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,X0))) = X0
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_31707,c_6,c_551])).

cnf(c_58152,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(X0,sK0))) = X0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_31773])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,plain,
    ( r1_tarski(sK0,sK2) != iProver_top
    | r1_tarski(sK1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_295,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_31664,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_31478,c_295])).

cnf(c_29821,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k1_xboole_0) = k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_29818,c_29226])).

cnf(c_29840,plain,
    ( k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29821,c_5,c_6])).

cnf(c_1000,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_13,c_3])).

cnf(c_33847,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[status(thm)],[c_29840,c_1000])).

cnf(c_34091,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    inference(demodulation,[status(thm)],[c_33847,c_512])).

cnf(c_34092,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34091,c_5,c_551])).

cnf(c_44620,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k1_xboole_0
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34092,c_12])).

cnf(c_643,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_512,c_3])).

cnf(c_646,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_643,c_6,c_551])).

cnf(c_986,plain,
    ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,X2)),k3_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,X2)),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(superposition,[status(thm)],[c_646,c_13])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1015,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1) ),
    inference(demodulation,[status(thm)],[c_986,c_6,c_8,c_10,c_512,c_551])).

cnf(c_55896,plain,
    ( k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),sK1) = k5_xboole_0(k2_zfmisc_1(X0,sK1),k3_xboole_0(k2_zfmisc_1(X0,sK1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_29818,c_1015])).

cnf(c_56165,plain,
    ( k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),sK1) = k2_zfmisc_1(X0,sK1) ),
    inference(demodulation,[status(thm)],[c_55896,c_5,c_6])).

cnf(c_85048,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(sK0,sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_44620,c_56165])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_85122,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_85048,c_11])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_21,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_112,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_317,plain,
    ( k2_zfmisc_1(sK0,sK1) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_318,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_85136,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_85122,c_15,c_20,c_21,c_318])).

cnf(c_85235,plain,
    ( r1_tarski(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_85136,c_295])).

cnf(c_106859,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_58152,c_18,c_31664,c_85235])).

cnf(c_107012,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_106859,c_15])).

cnf(c_107013,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_107012,c_10])).

cnf(c_107014,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_107013])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 51.72/6.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.72/6.99  
% 51.72/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.72/6.99  
% 51.72/6.99  ------  iProver source info
% 51.72/6.99  
% 51.72/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.72/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.72/6.99  git: non_committed_changes: false
% 51.72/6.99  git: last_make_outside_of_git: false
% 51.72/6.99  
% 51.72/6.99  ------ 
% 51.72/6.99  
% 51.72/6.99  ------ Input Options
% 51.72/6.99  
% 51.72/6.99  --out_options                           all
% 51.72/6.99  --tptp_safe_out                         true
% 51.72/6.99  --problem_path                          ""
% 51.72/6.99  --include_path                          ""
% 51.72/6.99  --clausifier                            res/vclausify_rel
% 51.72/6.99  --clausifier_options                    ""
% 51.72/6.99  --stdin                                 false
% 51.72/6.99  --stats_out                             all
% 51.72/6.99  
% 51.72/6.99  ------ General Options
% 51.72/6.99  
% 51.72/6.99  --fof                                   false
% 51.72/6.99  --time_out_real                         305.
% 51.72/6.99  --time_out_virtual                      -1.
% 51.72/6.99  --symbol_type_check                     false
% 51.72/6.99  --clausify_out                          false
% 51.72/6.99  --sig_cnt_out                           false
% 51.72/6.99  --trig_cnt_out                          false
% 51.72/6.99  --trig_cnt_out_tolerance                1.
% 51.72/6.99  --trig_cnt_out_sk_spl                   false
% 51.72/6.99  --abstr_cl_out                          false
% 51.72/6.99  
% 51.72/6.99  ------ Global Options
% 51.72/6.99  
% 51.72/6.99  --schedule                              default
% 51.72/6.99  --add_important_lit                     false
% 51.72/6.99  --prop_solver_per_cl                    1000
% 51.72/6.99  --min_unsat_core                        false
% 51.72/6.99  --soft_assumptions                      false
% 51.72/6.99  --soft_lemma_size                       3
% 51.72/6.99  --prop_impl_unit_size                   0
% 51.72/6.99  --prop_impl_unit                        []
% 51.72/6.99  --share_sel_clauses                     true
% 51.72/6.99  --reset_solvers                         false
% 51.72/6.99  --bc_imp_inh                            [conj_cone]
% 51.72/6.99  --conj_cone_tolerance                   3.
% 51.72/6.99  --extra_neg_conj                        none
% 51.72/6.99  --large_theory_mode                     true
% 51.72/6.99  --prolific_symb_bound                   200
% 51.72/6.99  --lt_threshold                          2000
% 51.72/6.99  --clause_weak_htbl                      true
% 51.72/6.99  --gc_record_bc_elim                     false
% 51.72/6.99  
% 51.72/6.99  ------ Preprocessing Options
% 51.72/6.99  
% 51.72/6.99  --preprocessing_flag                    true
% 51.72/6.99  --time_out_prep_mult                    0.1
% 51.72/6.99  --splitting_mode                        input
% 51.72/6.99  --splitting_grd                         true
% 51.72/6.99  --splitting_cvd                         false
% 51.72/6.99  --splitting_cvd_svl                     false
% 51.72/6.99  --splitting_nvd                         32
% 51.72/6.99  --sub_typing                            true
% 51.72/6.99  --prep_gs_sim                           true
% 51.72/6.99  --prep_unflatten                        true
% 51.72/6.99  --prep_res_sim                          true
% 51.72/6.99  --prep_upred                            true
% 51.72/6.99  --prep_sem_filter                       exhaustive
% 51.72/6.99  --prep_sem_filter_out                   false
% 51.72/6.99  --pred_elim                             true
% 51.72/6.99  --res_sim_input                         true
% 51.72/6.99  --eq_ax_congr_red                       true
% 51.72/6.99  --pure_diseq_elim                       true
% 51.72/6.99  --brand_transform                       false
% 51.72/6.99  --non_eq_to_eq                          false
% 51.72/6.99  --prep_def_merge                        true
% 51.72/6.99  --prep_def_merge_prop_impl              false
% 51.72/6.99  --prep_def_merge_mbd                    true
% 51.72/6.99  --prep_def_merge_tr_red                 false
% 51.72/6.99  --prep_def_merge_tr_cl                  false
% 51.72/6.99  --smt_preprocessing                     true
% 51.72/6.99  --smt_ac_axioms                         fast
% 51.72/6.99  --preprocessed_out                      false
% 51.72/6.99  --preprocessed_stats                    false
% 51.72/6.99  
% 51.72/6.99  ------ Abstraction refinement Options
% 51.72/6.99  
% 51.72/6.99  --abstr_ref                             []
% 51.72/6.99  --abstr_ref_prep                        false
% 51.72/6.99  --abstr_ref_until_sat                   false
% 51.72/6.99  --abstr_ref_sig_restrict                funpre
% 51.72/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.72/6.99  --abstr_ref_under                       []
% 51.72/6.99  
% 51.72/6.99  ------ SAT Options
% 51.72/6.99  
% 51.72/6.99  --sat_mode                              false
% 51.72/6.99  --sat_fm_restart_options                ""
% 51.72/6.99  --sat_gr_def                            false
% 51.72/6.99  --sat_epr_types                         true
% 51.72/6.99  --sat_non_cyclic_types                  false
% 51.72/6.99  --sat_finite_models                     false
% 51.72/6.99  --sat_fm_lemmas                         false
% 51.72/6.99  --sat_fm_prep                           false
% 51.72/6.99  --sat_fm_uc_incr                        true
% 51.72/6.99  --sat_out_model                         small
% 51.72/6.99  --sat_out_clauses                       false
% 51.72/6.99  
% 51.72/6.99  ------ QBF Options
% 51.72/6.99  
% 51.72/6.99  --qbf_mode                              false
% 51.72/6.99  --qbf_elim_univ                         false
% 51.72/6.99  --qbf_dom_inst                          none
% 51.72/6.99  --qbf_dom_pre_inst                      false
% 51.72/6.99  --qbf_sk_in                             false
% 51.72/6.99  --qbf_pred_elim                         true
% 51.72/6.99  --qbf_split                             512
% 51.72/6.99  
% 51.72/6.99  ------ BMC1 Options
% 51.72/6.99  
% 51.72/6.99  --bmc1_incremental                      false
% 51.72/6.99  --bmc1_axioms                           reachable_all
% 51.72/6.99  --bmc1_min_bound                        0
% 51.72/6.99  --bmc1_max_bound                        -1
% 51.72/6.99  --bmc1_max_bound_default                -1
% 51.72/6.99  --bmc1_symbol_reachability              true
% 51.72/6.99  --bmc1_property_lemmas                  false
% 51.72/6.99  --bmc1_k_induction                      false
% 51.72/6.99  --bmc1_non_equiv_states                 false
% 51.72/6.99  --bmc1_deadlock                         false
% 51.72/6.99  --bmc1_ucm                              false
% 51.72/6.99  --bmc1_add_unsat_core                   none
% 51.72/6.99  --bmc1_unsat_core_children              false
% 51.72/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.72/6.99  --bmc1_out_stat                         full
% 51.72/6.99  --bmc1_ground_init                      false
% 51.72/6.99  --bmc1_pre_inst_next_state              false
% 51.72/6.99  --bmc1_pre_inst_state                   false
% 51.72/6.99  --bmc1_pre_inst_reach_state             false
% 51.72/6.99  --bmc1_out_unsat_core                   false
% 51.72/6.99  --bmc1_aig_witness_out                  false
% 51.72/6.99  --bmc1_verbose                          false
% 51.72/6.99  --bmc1_dump_clauses_tptp                false
% 51.72/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.72/6.99  --bmc1_dump_file                        -
% 51.72/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.72/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.72/6.99  --bmc1_ucm_extend_mode                  1
% 51.72/6.99  --bmc1_ucm_init_mode                    2
% 51.72/6.99  --bmc1_ucm_cone_mode                    none
% 51.72/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.72/6.99  --bmc1_ucm_relax_model                  4
% 51.72/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.72/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.72/6.99  --bmc1_ucm_layered_model                none
% 51.72/6.99  --bmc1_ucm_max_lemma_size               10
% 51.72/6.99  
% 51.72/6.99  ------ AIG Options
% 51.72/6.99  
% 51.72/6.99  --aig_mode                              false
% 51.72/6.99  
% 51.72/6.99  ------ Instantiation Options
% 51.72/6.99  
% 51.72/6.99  --instantiation_flag                    true
% 51.72/6.99  --inst_sos_flag                         true
% 51.72/6.99  --inst_sos_phase                        true
% 51.72/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.72/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.72/6.99  --inst_lit_sel_side                     num_symb
% 51.72/6.99  --inst_solver_per_active                1400
% 51.72/6.99  --inst_solver_calls_frac                1.
% 51.72/6.99  --inst_passive_queue_type               priority_queues
% 51.72/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.72/6.99  --inst_passive_queues_freq              [25;2]
% 51.72/6.99  --inst_dismatching                      true
% 51.72/6.99  --inst_eager_unprocessed_to_passive     true
% 51.72/6.99  --inst_prop_sim_given                   true
% 51.72/6.99  --inst_prop_sim_new                     false
% 51.72/6.99  --inst_subs_new                         false
% 51.72/6.99  --inst_eq_res_simp                      false
% 51.72/6.99  --inst_subs_given                       false
% 51.72/6.99  --inst_orphan_elimination               true
% 51.72/6.99  --inst_learning_loop_flag               true
% 51.72/6.99  --inst_learning_start                   3000
% 51.72/6.99  --inst_learning_factor                  2
% 51.72/6.99  --inst_start_prop_sim_after_learn       3
% 51.72/6.99  --inst_sel_renew                        solver
% 51.72/6.99  --inst_lit_activity_flag                true
% 51.72/6.99  --inst_restr_to_given                   false
% 51.72/6.99  --inst_activity_threshold               500
% 51.72/6.99  --inst_out_proof                        true
% 51.72/6.99  
% 51.72/6.99  ------ Resolution Options
% 51.72/6.99  
% 51.72/6.99  --resolution_flag                       true
% 51.72/6.99  --res_lit_sel                           adaptive
% 51.72/6.99  --res_lit_sel_side                      none
% 51.72/6.99  --res_ordering                          kbo
% 51.72/6.99  --res_to_prop_solver                    active
% 51.72/6.99  --res_prop_simpl_new                    false
% 51.72/6.99  --res_prop_simpl_given                  true
% 51.72/6.99  --res_passive_queue_type                priority_queues
% 51.72/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.72/6.99  --res_passive_queues_freq               [15;5]
% 51.72/6.99  --res_forward_subs                      full
% 51.72/6.99  --res_backward_subs                     full
% 51.72/6.99  --res_forward_subs_resolution           true
% 51.72/6.99  --res_backward_subs_resolution          true
% 51.72/6.99  --res_orphan_elimination                true
% 51.72/6.99  --res_time_limit                        2.
% 51.72/6.99  --res_out_proof                         true
% 51.72/6.99  
% 51.72/6.99  ------ Superposition Options
% 51.72/6.99  
% 51.72/6.99  --superposition_flag                    true
% 51.72/6.99  --sup_passive_queue_type                priority_queues
% 51.72/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.72/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.72/6.99  --demod_completeness_check              fast
% 51.72/6.99  --demod_use_ground                      true
% 51.72/6.99  --sup_to_prop_solver                    passive
% 51.72/6.99  --sup_prop_simpl_new                    true
% 51.72/6.99  --sup_prop_simpl_given                  true
% 51.72/6.99  --sup_fun_splitting                     true
% 51.72/6.99  --sup_smt_interval                      50000
% 51.72/6.99  
% 51.72/6.99  ------ Superposition Simplification Setup
% 51.72/6.99  
% 51.72/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.72/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.72/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.72/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.72/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.72/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.72/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.72/6.99  --sup_immed_triv                        [TrivRules]
% 51.72/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.72/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.72/6.99  --sup_immed_bw_main                     []
% 51.72/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.72/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.72/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.72/6.99  --sup_input_bw                          []
% 51.72/6.99  
% 51.72/6.99  ------ Combination Options
% 51.72/6.99  
% 51.72/6.99  --comb_res_mult                         3
% 51.72/6.99  --comb_sup_mult                         2
% 51.72/6.99  --comb_inst_mult                        10
% 51.72/6.99  
% 51.72/6.99  ------ Debug Options
% 51.72/6.99  
% 51.72/6.99  --dbg_backtrace                         false
% 51.72/6.99  --dbg_dump_prop_clauses                 false
% 51.72/6.99  --dbg_dump_prop_clauses_file            -
% 51.72/6.99  --dbg_out_stat                          false
% 51.72/6.99  ------ Parsing...
% 51.72/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.72/6.99  
% 51.72/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.72/6.99  
% 51.72/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.72/6.99  
% 51.72/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.72/6.99  ------ Proving...
% 51.72/6.99  ------ Problem Properties 
% 51.72/6.99  
% 51.72/6.99  
% 51.72/6.99  clauses                                 17
% 51.72/6.99  conjectures                             3
% 51.72/6.99  EPR                                     1
% 51.72/6.99  Horn                                    16
% 51.72/6.99  unary                                   12
% 51.72/6.99  binary                                  4
% 51.72/6.99  lits                                    23
% 51.72/6.99  lits eq                                 17
% 51.72/6.99  fd_pure                                 0
% 51.72/6.99  fd_pseudo                               0
% 51.72/6.99  fd_cond                                 1
% 51.72/6.99  fd_pseudo_cond                          0
% 51.72/6.99  AC symbols                              1
% 51.72/6.99  
% 51.72/6.99  ------ Schedule dynamic 5 is on 
% 51.72/6.99  
% 51.72/6.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.72/6.99  
% 51.72/6.99  
% 51.72/6.99  ------ 
% 51.72/6.99  Current options:
% 51.72/6.99  ------ 
% 51.72/6.99  
% 51.72/6.99  ------ Input Options
% 51.72/6.99  
% 51.72/6.99  --out_options                           all
% 51.72/6.99  --tptp_safe_out                         true
% 51.72/6.99  --problem_path                          ""
% 51.72/6.99  --include_path                          ""
% 51.72/6.99  --clausifier                            res/vclausify_rel
% 51.72/6.99  --clausifier_options                    ""
% 51.72/6.99  --stdin                                 false
% 51.72/6.99  --stats_out                             all
% 51.72/6.99  
% 51.72/6.99  ------ General Options
% 51.72/6.99  
% 51.72/6.99  --fof                                   false
% 51.72/6.99  --time_out_real                         305.
% 51.72/6.99  --time_out_virtual                      -1.
% 51.72/6.99  --symbol_type_check                     false
% 51.72/6.99  --clausify_out                          false
% 51.72/6.99  --sig_cnt_out                           false
% 51.72/6.99  --trig_cnt_out                          false
% 51.72/6.99  --trig_cnt_out_tolerance                1.
% 51.72/6.99  --trig_cnt_out_sk_spl                   false
% 51.72/6.99  --abstr_cl_out                          false
% 51.72/6.99  
% 51.72/6.99  ------ Global Options
% 51.72/6.99  
% 51.72/6.99  --schedule                              default
% 51.72/6.99  --add_important_lit                     false
% 51.72/6.99  --prop_solver_per_cl                    1000
% 51.72/6.99  --min_unsat_core                        false
% 51.72/6.99  --soft_assumptions                      false
% 51.72/6.99  --soft_lemma_size                       3
% 51.72/6.99  --prop_impl_unit_size                   0
% 51.72/6.99  --prop_impl_unit                        []
% 51.72/6.99  --share_sel_clauses                     true
% 51.72/6.99  --reset_solvers                         false
% 51.72/6.99  --bc_imp_inh                            [conj_cone]
% 51.72/6.99  --conj_cone_tolerance                   3.
% 51.72/6.99  --extra_neg_conj                        none
% 51.72/6.99  --large_theory_mode                     true
% 51.72/6.99  --prolific_symb_bound                   200
% 51.72/6.99  --lt_threshold                          2000
% 51.72/6.99  --clause_weak_htbl                      true
% 51.72/6.99  --gc_record_bc_elim                     false
% 51.72/6.99  
% 51.72/6.99  ------ Preprocessing Options
% 51.72/6.99  
% 51.72/6.99  --preprocessing_flag                    true
% 51.72/6.99  --time_out_prep_mult                    0.1
% 51.72/6.99  --splitting_mode                        input
% 51.72/6.99  --splitting_grd                         true
% 51.72/6.99  --splitting_cvd                         false
% 51.72/6.99  --splitting_cvd_svl                     false
% 51.72/6.99  --splitting_nvd                         32
% 51.72/6.99  --sub_typing                            true
% 51.72/6.99  --prep_gs_sim                           true
% 51.72/6.99  --prep_unflatten                        true
% 51.72/6.99  --prep_res_sim                          true
% 51.72/6.99  --prep_upred                            true
% 51.72/6.99  --prep_sem_filter                       exhaustive
% 51.72/6.99  --prep_sem_filter_out                   false
% 51.72/6.99  --pred_elim                             true
% 51.72/6.99  --res_sim_input                         true
% 51.72/6.99  --eq_ax_congr_red                       true
% 51.72/6.99  --pure_diseq_elim                       true
% 51.72/6.99  --brand_transform                       false
% 51.72/6.99  --non_eq_to_eq                          false
% 51.72/6.99  --prep_def_merge                        true
% 51.72/6.99  --prep_def_merge_prop_impl              false
% 51.72/6.99  --prep_def_merge_mbd                    true
% 51.72/6.99  --prep_def_merge_tr_red                 false
% 51.72/6.99  --prep_def_merge_tr_cl                  false
% 51.72/6.99  --smt_preprocessing                     true
% 51.72/6.99  --smt_ac_axioms                         fast
% 51.72/6.99  --preprocessed_out                      false
% 51.72/6.99  --preprocessed_stats                    false
% 51.72/6.99  
% 51.72/6.99  ------ Abstraction refinement Options
% 51.72/6.99  
% 51.72/6.99  --abstr_ref                             []
% 51.72/6.99  --abstr_ref_prep                        false
% 51.72/6.99  --abstr_ref_until_sat                   false
% 51.72/6.99  --abstr_ref_sig_restrict                funpre
% 51.72/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.72/6.99  --abstr_ref_under                       []
% 51.72/6.99  
% 51.72/6.99  ------ SAT Options
% 51.72/6.99  
% 51.72/6.99  --sat_mode                              false
% 51.72/6.99  --sat_fm_restart_options                ""
% 51.72/6.99  --sat_gr_def                            false
% 51.72/6.99  --sat_epr_types                         true
% 51.72/6.99  --sat_non_cyclic_types                  false
% 51.72/6.99  --sat_finite_models                     false
% 51.72/6.99  --sat_fm_lemmas                         false
% 51.72/6.99  --sat_fm_prep                           false
% 51.72/6.99  --sat_fm_uc_incr                        true
% 51.72/6.99  --sat_out_model                         small
% 51.72/6.99  --sat_out_clauses                       false
% 51.72/6.99  
% 51.72/6.99  ------ QBF Options
% 51.72/6.99  
% 51.72/6.99  --qbf_mode                              false
% 51.72/6.99  --qbf_elim_univ                         false
% 51.72/6.99  --qbf_dom_inst                          none
% 51.72/6.99  --qbf_dom_pre_inst                      false
% 51.72/6.99  --qbf_sk_in                             false
% 51.72/6.99  --qbf_pred_elim                         true
% 51.72/6.99  --qbf_split                             512
% 51.72/6.99  
% 51.72/6.99  ------ BMC1 Options
% 51.72/6.99  
% 51.72/6.99  --bmc1_incremental                      false
% 51.72/6.99  --bmc1_axioms                           reachable_all
% 51.72/6.99  --bmc1_min_bound                        0
% 51.72/6.99  --bmc1_max_bound                        -1
% 51.72/6.99  --bmc1_max_bound_default                -1
% 51.72/6.99  --bmc1_symbol_reachability              true
% 51.72/6.99  --bmc1_property_lemmas                  false
% 51.72/6.99  --bmc1_k_induction                      false
% 51.72/6.99  --bmc1_non_equiv_states                 false
% 51.72/6.99  --bmc1_deadlock                         false
% 51.72/6.99  --bmc1_ucm                              false
% 51.72/6.99  --bmc1_add_unsat_core                   none
% 51.72/6.99  --bmc1_unsat_core_children              false
% 51.72/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.72/6.99  --bmc1_out_stat                         full
% 51.72/6.99  --bmc1_ground_init                      false
% 51.72/6.99  --bmc1_pre_inst_next_state              false
% 51.72/6.99  --bmc1_pre_inst_state                   false
% 51.72/6.99  --bmc1_pre_inst_reach_state             false
% 51.72/6.99  --bmc1_out_unsat_core                   false
% 51.72/6.99  --bmc1_aig_witness_out                  false
% 51.72/6.99  --bmc1_verbose                          false
% 51.72/6.99  --bmc1_dump_clauses_tptp                false
% 51.72/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.72/6.99  --bmc1_dump_file                        -
% 51.72/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.72/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.72/6.99  --bmc1_ucm_extend_mode                  1
% 51.72/6.99  --bmc1_ucm_init_mode                    2
% 51.72/6.99  --bmc1_ucm_cone_mode                    none
% 51.72/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.72/6.99  --bmc1_ucm_relax_model                  4
% 51.72/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.72/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.72/6.99  --bmc1_ucm_layered_model                none
% 51.72/6.99  --bmc1_ucm_max_lemma_size               10
% 51.72/6.99  
% 51.72/6.99  ------ AIG Options
% 51.72/6.99  
% 51.72/6.99  --aig_mode                              false
% 51.72/6.99  
% 51.72/6.99  ------ Instantiation Options
% 51.72/6.99  
% 51.72/6.99  --instantiation_flag                    true
% 51.72/6.99  --inst_sos_flag                         true
% 51.72/6.99  --inst_sos_phase                        true
% 51.72/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.72/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.72/6.99  --inst_lit_sel_side                     none
% 51.72/6.99  --inst_solver_per_active                1400
% 51.72/6.99  --inst_solver_calls_frac                1.
% 51.72/6.99  --inst_passive_queue_type               priority_queues
% 51.72/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.72/6.99  --inst_passive_queues_freq              [25;2]
% 51.72/6.99  --inst_dismatching                      true
% 51.72/6.99  --inst_eager_unprocessed_to_passive     true
% 51.72/6.99  --inst_prop_sim_given                   true
% 51.72/6.99  --inst_prop_sim_new                     false
% 51.72/6.99  --inst_subs_new                         false
% 51.72/6.99  --inst_eq_res_simp                      false
% 51.72/6.99  --inst_subs_given                       false
% 51.72/6.99  --inst_orphan_elimination               true
% 51.72/6.99  --inst_learning_loop_flag               true
% 51.72/6.99  --inst_learning_start                   3000
% 51.72/6.99  --inst_learning_factor                  2
% 51.72/6.99  --inst_start_prop_sim_after_learn       3
% 51.72/6.99  --inst_sel_renew                        solver
% 51.72/6.99  --inst_lit_activity_flag                true
% 51.72/6.99  --inst_restr_to_given                   false
% 51.72/6.99  --inst_activity_threshold               500
% 51.72/6.99  --inst_out_proof                        true
% 51.72/6.99  
% 51.72/6.99  ------ Resolution Options
% 51.72/6.99  
% 51.72/6.99  --resolution_flag                       false
% 51.72/6.99  --res_lit_sel                           adaptive
% 51.72/6.99  --res_lit_sel_side                      none
% 51.72/6.99  --res_ordering                          kbo
% 51.72/6.99  --res_to_prop_solver                    active
% 51.72/6.99  --res_prop_simpl_new                    false
% 51.72/6.99  --res_prop_simpl_given                  true
% 51.72/6.99  --res_passive_queue_type                priority_queues
% 51.72/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.72/6.99  --res_passive_queues_freq               [15;5]
% 51.72/6.99  --res_forward_subs                      full
% 51.72/6.99  --res_backward_subs                     full
% 51.72/6.99  --res_forward_subs_resolution           true
% 51.72/6.99  --res_backward_subs_resolution          true
% 51.72/6.99  --res_orphan_elimination                true
% 51.72/6.99  --res_time_limit                        2.
% 51.72/6.99  --res_out_proof                         true
% 51.72/6.99  
% 51.72/6.99  ------ Superposition Options
% 51.72/6.99  
% 51.72/6.99  --superposition_flag                    true
% 51.72/6.99  --sup_passive_queue_type                priority_queues
% 51.72/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.72/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.72/6.99  --demod_completeness_check              fast
% 51.72/6.99  --demod_use_ground                      true
% 51.72/6.99  --sup_to_prop_solver                    passive
% 51.72/6.99  --sup_prop_simpl_new                    true
% 51.72/6.99  --sup_prop_simpl_given                  true
% 51.72/6.99  --sup_fun_splitting                     true
% 51.72/6.99  --sup_smt_interval                      50000
% 51.72/6.99  
% 51.72/6.99  ------ Superposition Simplification Setup
% 51.72/6.99  
% 51.72/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.72/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.72/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.72/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.72/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.72/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.72/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.72/6.99  --sup_immed_triv                        [TrivRules]
% 51.72/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.72/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.72/6.99  --sup_immed_bw_main                     []
% 51.72/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.72/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.72/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.72/6.99  --sup_input_bw                          []
% 51.72/6.99  
% 51.72/6.99  ------ Combination Options
% 51.72/6.99  
% 51.72/6.99  --comb_res_mult                         3
% 51.72/6.99  --comb_sup_mult                         2
% 51.72/6.99  --comb_inst_mult                        10
% 51.72/6.99  
% 51.72/6.99  ------ Debug Options
% 51.72/6.99  
% 51.72/6.99  --dbg_backtrace                         false
% 51.72/6.99  --dbg_dump_prop_clauses                 false
% 51.72/6.99  --dbg_dump_prop_clauses_file            -
% 51.72/6.99  --dbg_out_stat                          false
% 51.72/6.99  
% 51.72/6.99  
% 51.72/6.99  
% 51.72/6.99  
% 51.72/6.99  ------ Proving...
% 51.72/6.99  
% 51.72/6.99  
% 51.72/6.99  % SZS status Theorem for theBenchmark.p
% 51.72/6.99  
% 51.72/6.99   Resolution empty clause
% 51.72/6.99  
% 51.72/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.72/6.99  
% 51.72/6.99  fof(f1,axiom,(
% 51.72/6.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 51.72/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/6.99  
% 51.72/6.99  fof(f30,plain,(
% 51.72/6.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 51.72/6.99    inference(cnf_transformation,[],[f1])).
% 51.72/6.99  
% 51.72/6.99  fof(f20,conjecture,(
% 51.72/6.99    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f21,negated_conjecture,(
% 51.72/7.00    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 51.72/7.00    inference(negated_conjecture,[],[f20])).
% 51.72/7.00  
% 51.72/7.00  fof(f23,plain,(
% 51.72/7.00    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 51.72/7.00    inference(ennf_transformation,[],[f21])).
% 51.72/7.00  
% 51.72/7.00  fof(f24,plain,(
% 51.72/7.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 51.72/7.00    inference(flattening,[],[f23])).
% 51.72/7.00  
% 51.72/7.00  fof(f28,plain,(
% 51.72/7.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 51.72/7.00    introduced(choice_axiom,[])).
% 51.72/7.00  
% 51.72/7.00  fof(f29,plain,(
% 51.72/7.00    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 51.72/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28])).
% 51.72/7.00  
% 51.72/7.00  fof(f52,plain,(
% 51.72/7.00    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 51.72/7.00    inference(cnf_transformation,[],[f29])).
% 51.72/7.00  
% 51.72/7.00  fof(f5,axiom,(
% 51.72/7.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f22,plain,(
% 51.72/7.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.72/7.00    inference(ennf_transformation,[],[f5])).
% 51.72/7.00  
% 51.72/7.00  fof(f35,plain,(
% 51.72/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.72/7.00    inference(cnf_transformation,[],[f22])).
% 51.72/7.00  
% 51.72/7.00  fof(f19,axiom,(
% 51.72/7.00    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f51,plain,(
% 51.72/7.00    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))) )),
% 51.72/7.00    inference(cnf_transformation,[],[f19])).
% 51.72/7.00  
% 51.72/7.00  fof(f10,axiom,(
% 51.72/7.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f40,plain,(
% 51.72/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 51.72/7.00    inference(cnf_transformation,[],[f10])).
% 51.72/7.00  
% 51.72/7.00  fof(f55,plain,(
% 51.72/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 51.72/7.00    inference(definition_unfolding,[],[f40,f33])).
% 51.72/7.00  
% 51.72/7.00  fof(f3,axiom,(
% 51.72/7.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f33,plain,(
% 51.72/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 51.72/7.00    inference(cnf_transformation,[],[f3])).
% 51.72/7.00  
% 51.72/7.00  fof(f65,plain,(
% 51.72/7.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3))),k3_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3))),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1))))) )),
% 51.72/7.00    inference(definition_unfolding,[],[f51,f33,f55,f33,f33])).
% 51.72/7.00  
% 51.72/7.00  fof(f9,axiom,(
% 51.72/7.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f39,plain,(
% 51.72/7.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 51.72/7.00    inference(cnf_transformation,[],[f9])).
% 51.72/7.00  
% 51.72/7.00  fof(f8,axiom,(
% 51.72/7.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f38,plain,(
% 51.72/7.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 51.72/7.00    inference(cnf_transformation,[],[f8])).
% 51.72/7.00  
% 51.72/7.00  fof(f7,axiom,(
% 51.72/7.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f37,plain,(
% 51.72/7.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.72/7.00    inference(cnf_transformation,[],[f7])).
% 51.72/7.00  
% 51.72/7.00  fof(f4,axiom,(
% 51.72/7.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f34,plain,(
% 51.72/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 51.72/7.00    inference(cnf_transformation,[],[f4])).
% 51.72/7.00  
% 51.72/7.00  fof(f63,plain,(
% 51.72/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 51.72/7.00    inference(definition_unfolding,[],[f34,f55])).
% 51.72/7.00  
% 51.72/7.00  fof(f6,axiom,(
% 51.72/7.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f36,plain,(
% 51.72/7.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 51.72/7.00    inference(cnf_transformation,[],[f6])).
% 51.72/7.00  
% 51.72/7.00  fof(f18,axiom,(
% 51.72/7.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f26,plain,(
% 51.72/7.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 51.72/7.00    inference(nnf_transformation,[],[f18])).
% 51.72/7.00  
% 51.72/7.00  fof(f27,plain,(
% 51.72/7.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 51.72/7.00    inference(flattening,[],[f26])).
% 51.72/7.00  
% 51.72/7.00  fof(f48,plain,(
% 51.72/7.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 51.72/7.00    inference(cnf_transformation,[],[f27])).
% 51.72/7.00  
% 51.72/7.00  fof(f54,plain,(
% 51.72/7.00    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 51.72/7.00    inference(cnf_transformation,[],[f29])).
% 51.72/7.00  
% 51.72/7.00  fof(f2,axiom,(
% 51.72/7.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 51.72/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.72/7.00  
% 51.72/7.00  fof(f25,plain,(
% 51.72/7.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 51.72/7.00    inference(nnf_transformation,[],[f2])).
% 51.72/7.00  
% 51.72/7.00  fof(f31,plain,(
% 51.72/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 51.72/7.00    inference(cnf_transformation,[],[f25])).
% 51.72/7.00  
% 51.72/7.00  fof(f62,plain,(
% 51.72/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0) )),
% 51.72/7.00    inference(definition_unfolding,[],[f31,f33])).
% 51.72/7.00  
% 51.72/7.00  fof(f50,plain,(
% 51.72/7.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 51.72/7.00    inference(cnf_transformation,[],[f27])).
% 51.72/7.00  
% 51.72/7.00  fof(f66,plain,(
% 51.72/7.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 51.72/7.00    inference(equality_resolution,[],[f50])).
% 51.72/7.00  
% 51.72/7.00  fof(f49,plain,(
% 51.72/7.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 51.72/7.00    inference(cnf_transformation,[],[f27])).
% 51.72/7.00  
% 51.72/7.00  fof(f67,plain,(
% 51.72/7.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 51.72/7.00    inference(equality_resolution,[],[f49])).
% 51.72/7.00  
% 51.72/7.00  fof(f53,plain,(
% 51.72/7.00    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 51.72/7.00    inference(cnf_transformation,[],[f29])).
% 51.72/7.00  
% 51.72/7.00  cnf(c_0,plain,
% 51.72/7.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 51.72/7.00      inference(cnf_transformation,[],[f30]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_16,negated_conjecture,
% 51.72/7.00      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
% 51.72/7.00      inference(cnf_transformation,[],[f52]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_292,plain,
% 51.72/7.00      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 51.72/7.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_4,plain,
% 51.72/7.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.72/7.00      inference(cnf_transformation,[],[f35]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_294,plain,
% 51.72/7.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.72/7.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_511,plain,
% 51.72/7.00      ( k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK0,sK1) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_292,c_294]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_13,plain,
% 51.72/7.00      ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k3_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
% 51.72/7.00      inference(cnf_transformation,[],[f65]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_8,plain,
% 51.72/7.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.72/7.00      inference(cnf_transformation,[],[f39]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_7,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 51.72/7.00      inference(cnf_transformation,[],[f38]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_556,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_6,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.72/7.00      inference(cnf_transformation,[],[f37]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_512,plain,
% 51.72/7.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_562,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_556,c_512]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_769,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_0,c_562]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_998,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X1))),k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X3,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X1) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_13,c_769]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_26033,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1))),k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_511,c_998]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_303,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1666,plain,
% 51.72/7.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_6,c_303]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_772,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_7,c_562]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_2936,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_1666,c_772]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_2992,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 51.72/7.00      inference(light_normalisation,[status(thm)],[c_2936,c_6]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_5928,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_2992,c_1666]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1825,plain,
% 51.72/7.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_7,c_1666]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_7930,plain,
% 51.72/7.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_1825,c_7]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_304,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1929,plain,
% 51.72/7.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_304,c_1666]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1942,plain,
% 51.72/7.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_304,c_1666]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_302,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1852,plain,
% 51.72/7.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_1666,c_302]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1953,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 51.72/7.00      inference(light_normalisation,[status(thm)],[c_1942,c_1852]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1957,plain,
% 51.72/7.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_1929,c_1953]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_792,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_562,c_769]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_864,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X0,X1) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_7,c_792]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_4339,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X0,X2) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_0,c_864]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_6231,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_4339,c_7]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_870,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_792,c_7]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_4587,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_870,c_870]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_6299,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 51.72/7.00      inference(light_normalisation,[status(thm)],[c_6231,c_4587]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_7990,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3))) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_7930,c_1666,c_1957,c_6299]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_26201,plain,
% 51.72/7.00      ( k5_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_26033,c_8,c_5928,c_7990]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_3,plain,
% 51.72/7.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 51.72/7.00      inference(cnf_transformation,[],[f63]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_4586,plain,
% 51.72/7.00      ( k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_870,c_3]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29210,plain,
% 51.72/7.00      ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k5_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)))) = k5_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_26201,c_4586]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29226,plain,
% 51.72/7.00      ( k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) = k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_26201,c_769]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29241,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) = k5_xboole_0(X0,k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1))) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_26201,c_864]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_2928,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_7,c_772]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_10723,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X3,X2)))) = X3 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_0,c_2928]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29264,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))))),k5_xboole_0(X0,k5_xboole_0(X1,k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)))) = k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_26201,c_10723]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_10739,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_769,c_2928]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29269,plain,
% 51.72/7.00      ( k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_29264,c_10739]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29779,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))))) = k5_xboole_0(k5_xboole_0(X0,k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))) ),
% 51.72/7.00      inference(light_normalisation,[status(thm)],[c_29241,c_29269]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29223,plain,
% 51.72/7.00      ( k5_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),X0)) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),X0) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_26201,c_7]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29805,plain,
% 51.72/7.00      ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),X0)) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),X0) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_29223,c_29226]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29817,plain,
% 51.72/7.00      ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1))) = k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))))) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_29210,c_29226,c_29779,c_29805]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_5,plain,
% 51.72/7.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 51.72/7.00      inference(cnf_transformation,[],[f36]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29818,plain,
% 51.72/7.00      ( k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k1_xboole_0 ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_29817,c_5,c_8,c_769]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_12,plain,
% 51.72/7.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 51.72/7.00      | k1_xboole_0 = X1
% 51.72/7.00      | k1_xboole_0 = X0 ),
% 51.72/7.00      inference(cnf_transformation,[],[f48]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_31478,plain,
% 51.72/7.00      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k1_xboole_0
% 51.72/7.00      | sK1 = k1_xboole_0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_29818,c_12]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1625,plain,
% 51.72/7.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_302,c_3]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_4791,plain,
% 51.72/7.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X2),X0))))) = X0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_7,c_1625]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_14111,plain,
% 51.72/7.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X2,X1),X0))))) = X0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_0,c_4791]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_31707,plain,
% 51.72/7.00      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))))) = X0
% 51.72/7.00      | sK1 = k1_xboole_0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_31478,c_14111]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_547,plain,
% 51.72/7.00      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_5,c_3]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_551,plain,
% 51.72/7.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 51.72/7.00      inference(light_normalisation,[status(thm)],[c_547,c_6,c_512]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_31773,plain,
% 51.72/7.00      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,X0))) = X0
% 51.72/7.00      | sK1 = k1_xboole_0 ),
% 51.72/7.00      inference(light_normalisation,[status(thm)],[c_31707,c_6,c_551]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_58152,plain,
% 51.72/7.00      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(X0,sK0))) = X0
% 51.72/7.00      | sK1 = k1_xboole_0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_0,c_31773]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_14,negated_conjecture,
% 51.72/7.00      ( ~ r1_tarski(sK0,sK2) | ~ r1_tarski(sK1,sK3) ),
% 51.72/7.00      inference(cnf_transformation,[],[f54]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_18,plain,
% 51.72/7.00      ( r1_tarski(sK0,sK2) != iProver_top | r1_tarski(sK1,sK3) != iProver_top ),
% 51.72/7.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_2,plain,
% 51.72/7.00      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 51.72/7.00      inference(cnf_transformation,[],[f62]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_295,plain,
% 51.72/7.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 51.72/7.00      | r1_tarski(X0,X1) = iProver_top ),
% 51.72/7.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_31664,plain,
% 51.72/7.00      ( sK1 = k1_xboole_0 | r1_tarski(sK0,sK2) = iProver_top ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_31478,c_295]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29821,plain,
% 51.72/7.00      ( k3_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k1_xboole_0) = k5_xboole_0(k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k1_xboole_0) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_29818,c_29226]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_29840,plain,
% 51.72/7.00      ( k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_29821,c_5,c_6]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1000,plain,
% 51.72/7.00      ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_13,c_3]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_33847,plain,
% 51.72/7.00      ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_29840,c_1000]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_34091,plain,
% 51.72/7.00      ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_33847,c_512]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_34092,plain,
% 51.72/7.00      ( k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_34091,c_5,c_551]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_44620,plain,
% 51.72/7.00      ( k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k1_xboole_0
% 51.72/7.00      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_34092,c_12]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_643,plain,
% 51.72/7.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_512,c_3]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_646,plain,
% 51.72/7.00      ( k3_xboole_0(X0,X0) = X0 ),
% 51.72/7.00      inference(light_normalisation,[status(thm)],[c_643,c_6,c_551]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_986,plain,
% 51.72/7.00      ( k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k5_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,X2)),k3_xboole_0(k2_zfmisc_1(X0,k5_xboole_0(X2,X2)),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_646,c_13]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_10,plain,
% 51.72/7.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 51.72/7.00      inference(cnf_transformation,[],[f66]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_1015,plain,
% 51.72/7.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_986,c_6,c_8,c_10,c_512,c_551]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_55896,plain,
% 51.72/7.00      ( k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),sK1) = k5_xboole_0(k2_zfmisc_1(X0,sK1),k3_xboole_0(k2_zfmisc_1(X0,sK1),k1_xboole_0)) ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_29818,c_1015]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_56165,plain,
% 51.72/7.00      ( k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),sK1) = k2_zfmisc_1(X0,sK1) ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_55896,c_5,c_6]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_85048,plain,
% 51.72/7.00      ( k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(sK0,sK1)
% 51.72/7.00      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_44620,c_56165]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_11,plain,
% 51.72/7.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 51.72/7.00      inference(cnf_transformation,[],[f67]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_85122,plain,
% 51.72/7.00      ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 51.72/7.00      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_85048,c_11]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_15,negated_conjecture,
% 51.72/7.00      ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
% 51.72/7.00      inference(cnf_transformation,[],[f53]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_20,plain,
% 51.72/7.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 51.72/7.00      | k1_xboole_0 = k1_xboole_0 ),
% 51.72/7.00      inference(instantiation,[status(thm)],[c_12]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_21,plain,
% 51.72/7.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 51.72/7.00      inference(instantiation,[status(thm)],[c_11]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_112,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_317,plain,
% 51.72/7.00      ( k2_zfmisc_1(sK0,sK1) != X0
% 51.72/7.00      | k1_xboole_0 != X0
% 51.72/7.00      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
% 51.72/7.00      inference(instantiation,[status(thm)],[c_112]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_318,plain,
% 51.72/7.00      ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
% 51.72/7.00      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 51.72/7.00      | k1_xboole_0 != k1_xboole_0 ),
% 51.72/7.00      inference(instantiation,[status(thm)],[c_317]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_85136,plain,
% 51.72/7.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 51.72/7.00      inference(global_propositional_subsumption,
% 51.72/7.00                [status(thm)],
% 51.72/7.00                [c_85122,c_15,c_20,c_21,c_318]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_85235,plain,
% 51.72/7.00      ( r1_tarski(sK1,sK3) = iProver_top ),
% 51.72/7.00      inference(superposition,[status(thm)],[c_85136,c_295]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_106859,plain,
% 51.72/7.00      ( sK1 = k1_xboole_0 ),
% 51.72/7.00      inference(global_propositional_subsumption,
% 51.72/7.00                [status(thm)],
% 51.72/7.00                [c_58152,c_18,c_31664,c_85235]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_107012,plain,
% 51.72/7.00      ( k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_106859,c_15]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_107013,plain,
% 51.72/7.00      ( k1_xboole_0 != k1_xboole_0 ),
% 51.72/7.00      inference(demodulation,[status(thm)],[c_107012,c_10]) ).
% 51.72/7.00  
% 51.72/7.00  cnf(c_107014,plain,
% 51.72/7.00      ( $false ),
% 51.72/7.00      inference(equality_resolution_simp,[status(thm)],[c_107013]) ).
% 51.72/7.00  
% 51.72/7.00  
% 51.72/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.72/7.00  
% 51.72/7.00  ------                               Statistics
% 51.72/7.00  
% 51.72/7.00  ------ General
% 51.72/7.00  
% 51.72/7.00  abstr_ref_over_cycles:                  0
% 51.72/7.00  abstr_ref_under_cycles:                 0
% 51.72/7.00  gc_basic_clause_elim:                   0
% 51.72/7.00  forced_gc_time:                         0
% 51.72/7.00  parsing_time:                           0.008
% 51.72/7.00  unif_index_cands_time:                  0.
% 51.72/7.00  unif_index_add_time:                    0.
% 51.72/7.00  orderings_time:                         0.
% 51.72/7.00  out_proof_time:                         0.015
% 51.72/7.00  total_time:                             6.457
% 51.72/7.00  num_of_symbols:                         42
% 51.72/7.00  num_of_terms:                           288763
% 51.72/7.00  
% 51.72/7.00  ------ Preprocessing
% 51.72/7.00  
% 51.72/7.00  num_of_splits:                          0
% 51.72/7.00  num_of_split_atoms:                     0
% 51.72/7.00  num_of_reused_defs:                     0
% 51.72/7.00  num_eq_ax_congr_red:                    16
% 51.72/7.00  num_of_sem_filtered_clauses:            1
% 51.72/7.00  num_of_subtypes:                        0
% 51.72/7.00  monotx_restored_types:                  0
% 51.72/7.00  sat_num_of_epr_types:                   0
% 51.72/7.00  sat_num_of_non_cyclic_types:            0
% 51.72/7.00  sat_guarded_non_collapsed_types:        0
% 51.72/7.00  num_pure_diseq_elim:                    0
% 51.72/7.00  simp_replaced_by:                       0
% 51.72/7.00  res_preprocessed:                       66
% 51.72/7.00  prep_upred:                             0
% 51.72/7.00  prep_unflattend:                        0
% 51.72/7.00  smt_new_axioms:                         0
% 51.72/7.00  pred_elim_cands:                        1
% 51.72/7.00  pred_elim:                              0
% 51.72/7.00  pred_elim_cl:                           0
% 51.72/7.00  pred_elim_cycles:                       1
% 51.72/7.00  merged_defs:                            6
% 51.72/7.00  merged_defs_ncl:                        0
% 51.72/7.00  bin_hyper_res:                          6
% 51.72/7.00  prep_cycles:                            3
% 51.72/7.00  pred_elim_time:                         0.
% 51.72/7.00  splitting_time:                         0.
% 51.72/7.00  sem_filter_time:                        0.
% 51.72/7.00  monotx_time:                            0.
% 51.72/7.00  subtype_inf_time:                       0.
% 51.72/7.00  
% 51.72/7.00  ------ Problem properties
% 51.72/7.00  
% 51.72/7.00  clauses:                                17
% 51.72/7.00  conjectures:                            3
% 51.72/7.00  epr:                                    1
% 51.72/7.00  horn:                                   16
% 51.72/7.00  ground:                                 3
% 51.72/7.00  unary:                                  12
% 51.72/7.00  binary:                                 4
% 51.72/7.00  lits:                                   23
% 51.72/7.00  lits_eq:                                17
% 51.72/7.00  fd_pure:                                0
% 51.72/7.00  fd_pseudo:                              0
% 51.72/7.00  fd_cond:                                1
% 51.72/7.00  fd_pseudo_cond:                         0
% 51.72/7.00  ac_symbols:                             1
% 51.72/7.00  
% 51.72/7.00  ------ Propositional Solver
% 51.72/7.00  
% 51.72/7.00  prop_solver_calls:                      33
% 51.72/7.00  prop_fast_solver_calls:                 718
% 51.72/7.00  smt_solver_calls:                       0
% 51.72/7.00  smt_fast_solver_calls:                  0
% 51.72/7.00  prop_num_of_clauses:                    30881
% 51.72/7.00  prop_preprocess_simplified:             18433
% 51.72/7.00  prop_fo_subsumed:                       2
% 51.72/7.00  prop_solver_time:                       0.
% 51.72/7.00  smt_solver_time:                        0.
% 51.72/7.00  smt_fast_solver_time:                   0.
% 51.72/7.00  prop_fast_solver_time:                  0.
% 51.72/7.00  prop_unsat_core_time:                   0.
% 51.72/7.00  
% 51.72/7.00  ------ QBF
% 51.72/7.00  
% 51.72/7.00  qbf_q_res:                              0
% 51.72/7.00  qbf_num_tautologies:                    0
% 51.72/7.00  qbf_prep_cycles:                        0
% 51.72/7.00  
% 51.72/7.00  ------ BMC1
% 51.72/7.00  
% 51.72/7.00  bmc1_current_bound:                     -1
% 51.72/7.00  bmc1_last_solved_bound:                 -1
% 51.72/7.00  bmc1_unsat_core_size:                   -1
% 51.72/7.00  bmc1_unsat_core_parents_size:           -1
% 51.72/7.00  bmc1_merge_next_fun:                    0
% 51.72/7.00  bmc1_unsat_core_clauses_time:           0.
% 51.72/7.00  
% 51.72/7.00  ------ Instantiation
% 51.72/7.00  
% 51.72/7.00  inst_num_of_clauses:                    5254
% 51.72/7.00  inst_num_in_passive:                    1405
% 51.72/7.00  inst_num_in_active:                     1677
% 51.72/7.00  inst_num_in_unprocessed:                2172
% 51.72/7.00  inst_num_of_loops:                      1710
% 51.72/7.00  inst_num_of_learning_restarts:          0
% 51.72/7.00  inst_num_moves_active_passive:          29
% 51.72/7.00  inst_lit_activity:                      0
% 51.72/7.00  inst_lit_activity_moves:                0
% 51.72/7.00  inst_num_tautologies:                   0
% 51.72/7.00  inst_num_prop_implied:                  0
% 51.72/7.00  inst_num_existing_simplified:           0
% 51.72/7.00  inst_num_eq_res_simplified:             0
% 51.72/7.00  inst_num_child_elim:                    0
% 51.72/7.00  inst_num_of_dismatching_blockings:      372
% 51.72/7.00  inst_num_of_non_proper_insts:           3665
% 51.72/7.00  inst_num_of_duplicates:                 0
% 51.72/7.00  inst_inst_num_from_inst_to_res:         0
% 51.72/7.00  inst_dismatching_checking_time:         0.
% 51.72/7.00  
% 51.72/7.00  ------ Resolution
% 51.72/7.00  
% 51.72/7.00  res_num_of_clauses:                     0
% 51.72/7.00  res_num_in_passive:                     0
% 51.72/7.00  res_num_in_active:                      0
% 51.72/7.00  res_num_of_loops:                       69
% 51.72/7.00  res_forward_subset_subsumed:            218
% 51.72/7.00  res_backward_subset_subsumed:           0
% 51.72/7.00  res_forward_subsumed:                   0
% 51.72/7.00  res_backward_subsumed:                  0
% 51.72/7.00  res_forward_subsumption_resolution:     0
% 51.72/7.00  res_backward_subsumption_resolution:    0
% 51.72/7.00  res_clause_to_clause_subsumption:       161084
% 51.72/7.00  res_orphan_elimination:                 0
% 51.72/7.00  res_tautology_del:                      127
% 51.72/7.00  res_num_eq_res_simplified:              0
% 51.72/7.00  res_num_sel_changes:                    0
% 51.72/7.00  res_moves_from_active_to_pass:          0
% 51.72/7.00  
% 51.72/7.00  ------ Superposition
% 51.72/7.00  
% 51.72/7.00  sup_time_total:                         0.
% 51.72/7.00  sup_time_generating:                    0.
% 51.72/7.00  sup_time_sim_full:                      0.
% 51.72/7.00  sup_time_sim_immed:                     0.
% 51.72/7.00  
% 51.72/7.00  sup_num_of_clauses:                     9573
% 51.72/7.00  sup_num_in_active:                      75
% 51.72/7.00  sup_num_in_passive:                     9498
% 51.72/7.00  sup_num_of_loops:                       341
% 51.72/7.00  sup_fw_superposition:                   21657
% 51.72/7.00  sup_bw_superposition:                   16954
% 51.72/7.00  sup_immediate_simplified:               25962
% 51.72/7.00  sup_given_eliminated:                   80
% 51.72/7.00  comparisons_done:                       0
% 51.72/7.00  comparisons_avoided:                    54
% 51.72/7.00  
% 51.72/7.00  ------ Simplifications
% 51.72/7.00  
% 51.72/7.00  
% 51.72/7.00  sim_fw_subset_subsumed:                 263
% 51.72/7.00  sim_bw_subset_subsumed:                 430
% 51.72/7.00  sim_fw_subsumed:                        2760
% 51.72/7.00  sim_bw_subsumed:                        294
% 51.72/7.00  sim_fw_subsumption_res:                 0
% 51.72/7.00  sim_bw_subsumption_res:                 0
% 51.72/7.00  sim_tautology_del:                      0
% 51.72/7.00  sim_eq_tautology_del:                   8945
% 51.72/7.00  sim_eq_res_simp:                        4437
% 51.72/7.00  sim_fw_demodulated:                     31124
% 51.72/7.00  sim_bw_demodulated:                     437
% 51.72/7.00  sim_light_normalised:                   8772
% 51.72/7.00  sim_joinable_taut:                      460
% 51.72/7.00  sim_joinable_simp:                      0
% 51.72/7.00  sim_ac_normalised:                      0
% 51.72/7.00  sim_smt_subsumption:                    0
% 51.72/7.00  
%------------------------------------------------------------------------------
