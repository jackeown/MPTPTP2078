%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:24 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 337 expanded)
%              Number of clauses        :   45 (  90 expanded)
%              Number of leaves         :   18 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  168 ( 533 expanded)
%              Number of equality atoms :   88 ( 315 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f28])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f36,f50,f50,f33])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f49,f49])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f37,f33,f50])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f48,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_401,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_394,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1339,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_394,c_396])).

cnf(c_2451,plain,
    ( r2_hidden(sK0(sK2,X0),sK1) = iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_401,c_1339])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_402,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3092,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2451,c_402])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_399,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4046,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_3092,c_399])).

cnf(c_5,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8896,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK2,sK2))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4046,c_5])).

cnf(c_10,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_397,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_407,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_397,c_9])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k2_enumset1(X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_395,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_697,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_395])).

cnf(c_2192,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k4_subset_1(sK1,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_394,c_697])).

cnf(c_8,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_398,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_602,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_398])).

cnf(c_2603,plain,
    ( r1_tarski(sK2,k4_subset_1(sK1,sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2192,c_602])).

cnf(c_2719,plain,
    ( k3_xboole_0(sK2,k4_subset_1(sK1,sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2603,c_399])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_712,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_2602,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k4_subset_1(sK1,sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2192,c_712])).

cnf(c_4113,plain,
    ( k5_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2719,c_2602])).

cnf(c_8898,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0)) = k4_subset_1(sK1,sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_8896,c_2192,c_4113])).

cnf(c_3,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8899,plain,
    ( k4_subset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_8898,c_3])).

cnf(c_696,plain,
    ( k3_tarski(k2_enumset1(sK2,sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_394,c_395])).

cnf(c_980,plain,
    ( k3_tarski(k2_enumset1(sK2,sK2,sK2,sK1)) = k4_subset_1(sK1,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_407,c_696])).

cnf(c_1109,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k4_subset_1(sK1,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_8,c_980])).

cnf(c_2599,plain,
    ( k4_subset_1(sK1,sK1,sK2) = k4_subset_1(sK1,sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_2192,c_1109])).

cnf(c_13,negated_conjecture,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_412,plain,
    ( k4_subset_1(sK1,sK2,sK1) != sK1 ),
    inference(demodulation,[status(thm)],[c_13,c_9])).

cnf(c_2730,plain,
    ( k4_subset_1(sK1,sK1,sK2) != sK1 ),
    inference(demodulation,[status(thm)],[c_2599,c_412])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8899,c_2730])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:20:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.06/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/1.01  
% 3.06/1.01  ------  iProver source info
% 3.06/1.01  
% 3.06/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.06/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/1.01  git: non_committed_changes: false
% 3.06/1.01  git: last_make_outside_of_git: false
% 3.06/1.01  
% 3.06/1.01  ------ 
% 3.06/1.01  
% 3.06/1.01  ------ Input Options
% 3.06/1.01  
% 3.06/1.01  --out_options                           all
% 3.06/1.01  --tptp_safe_out                         true
% 3.06/1.01  --problem_path                          ""
% 3.06/1.01  --include_path                          ""
% 3.06/1.01  --clausifier                            res/vclausify_rel
% 3.06/1.01  --clausifier_options                    --mode clausify
% 3.06/1.01  --stdin                                 false
% 3.06/1.01  --stats_out                             all
% 3.06/1.01  
% 3.06/1.01  ------ General Options
% 3.06/1.01  
% 3.06/1.01  --fof                                   false
% 3.06/1.01  --time_out_real                         305.
% 3.06/1.01  --time_out_virtual                      -1.
% 3.06/1.01  --symbol_type_check                     false
% 3.06/1.01  --clausify_out                          false
% 3.06/1.01  --sig_cnt_out                           false
% 3.06/1.01  --trig_cnt_out                          false
% 3.06/1.01  --trig_cnt_out_tolerance                1.
% 3.06/1.01  --trig_cnt_out_sk_spl                   false
% 3.06/1.01  --abstr_cl_out                          false
% 3.06/1.01  
% 3.06/1.01  ------ Global Options
% 3.06/1.01  
% 3.06/1.01  --schedule                              default
% 3.06/1.01  --add_important_lit                     false
% 3.06/1.01  --prop_solver_per_cl                    1000
% 3.06/1.01  --min_unsat_core                        false
% 3.06/1.01  --soft_assumptions                      false
% 3.06/1.01  --soft_lemma_size                       3
% 3.06/1.01  --prop_impl_unit_size                   0
% 3.06/1.01  --prop_impl_unit                        []
% 3.06/1.01  --share_sel_clauses                     true
% 3.06/1.01  --reset_solvers                         false
% 3.06/1.01  --bc_imp_inh                            [conj_cone]
% 3.06/1.01  --conj_cone_tolerance                   3.
% 3.06/1.01  --extra_neg_conj                        none
% 3.06/1.01  --large_theory_mode                     true
% 3.06/1.01  --prolific_symb_bound                   200
% 3.06/1.01  --lt_threshold                          2000
% 3.06/1.01  --clause_weak_htbl                      true
% 3.06/1.01  --gc_record_bc_elim                     false
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing Options
% 3.06/1.01  
% 3.06/1.01  --preprocessing_flag                    true
% 3.06/1.01  --time_out_prep_mult                    0.1
% 3.06/1.01  --splitting_mode                        input
% 3.06/1.01  --splitting_grd                         true
% 3.06/1.01  --splitting_cvd                         false
% 3.06/1.01  --splitting_cvd_svl                     false
% 3.06/1.01  --splitting_nvd                         32
% 3.06/1.01  --sub_typing                            true
% 3.06/1.01  --prep_gs_sim                           true
% 3.06/1.01  --prep_unflatten                        true
% 3.06/1.01  --prep_res_sim                          true
% 3.06/1.01  --prep_upred                            true
% 3.06/1.01  --prep_sem_filter                       exhaustive
% 3.06/1.01  --prep_sem_filter_out                   false
% 3.06/1.01  --pred_elim                             true
% 3.06/1.01  --res_sim_input                         true
% 3.06/1.01  --eq_ax_congr_red                       true
% 3.06/1.01  --pure_diseq_elim                       true
% 3.06/1.01  --brand_transform                       false
% 3.06/1.01  --non_eq_to_eq                          false
% 3.06/1.01  --prep_def_merge                        true
% 3.06/1.01  --prep_def_merge_prop_impl              false
% 3.06/1.01  --prep_def_merge_mbd                    true
% 3.06/1.01  --prep_def_merge_tr_red                 false
% 3.06/1.01  --prep_def_merge_tr_cl                  false
% 3.06/1.01  --smt_preprocessing                     true
% 3.06/1.01  --smt_ac_axioms                         fast
% 3.06/1.01  --preprocessed_out                      false
% 3.06/1.01  --preprocessed_stats                    false
% 3.06/1.01  
% 3.06/1.01  ------ Abstraction refinement Options
% 3.06/1.01  
% 3.06/1.01  --abstr_ref                             []
% 3.06/1.01  --abstr_ref_prep                        false
% 3.06/1.01  --abstr_ref_until_sat                   false
% 3.06/1.01  --abstr_ref_sig_restrict                funpre
% 3.06/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.01  --abstr_ref_under                       []
% 3.06/1.01  
% 3.06/1.01  ------ SAT Options
% 3.06/1.01  
% 3.06/1.01  --sat_mode                              false
% 3.06/1.01  --sat_fm_restart_options                ""
% 3.06/1.01  --sat_gr_def                            false
% 3.06/1.01  --sat_epr_types                         true
% 3.06/1.01  --sat_non_cyclic_types                  false
% 3.06/1.01  --sat_finite_models                     false
% 3.06/1.01  --sat_fm_lemmas                         false
% 3.06/1.01  --sat_fm_prep                           false
% 3.06/1.01  --sat_fm_uc_incr                        true
% 3.06/1.01  --sat_out_model                         small
% 3.06/1.01  --sat_out_clauses                       false
% 3.06/1.01  
% 3.06/1.01  ------ QBF Options
% 3.06/1.01  
% 3.06/1.01  --qbf_mode                              false
% 3.06/1.01  --qbf_elim_univ                         false
% 3.06/1.01  --qbf_dom_inst                          none
% 3.06/1.01  --qbf_dom_pre_inst                      false
% 3.06/1.01  --qbf_sk_in                             false
% 3.06/1.01  --qbf_pred_elim                         true
% 3.06/1.01  --qbf_split                             512
% 3.06/1.01  
% 3.06/1.01  ------ BMC1 Options
% 3.06/1.01  
% 3.06/1.01  --bmc1_incremental                      false
% 3.06/1.01  --bmc1_axioms                           reachable_all
% 3.06/1.01  --bmc1_min_bound                        0
% 3.06/1.01  --bmc1_max_bound                        -1
% 3.06/1.01  --bmc1_max_bound_default                -1
% 3.06/1.01  --bmc1_symbol_reachability              true
% 3.06/1.01  --bmc1_property_lemmas                  false
% 3.06/1.01  --bmc1_k_induction                      false
% 3.06/1.01  --bmc1_non_equiv_states                 false
% 3.06/1.01  --bmc1_deadlock                         false
% 3.06/1.01  --bmc1_ucm                              false
% 3.06/1.01  --bmc1_add_unsat_core                   none
% 3.06/1.01  --bmc1_unsat_core_children              false
% 3.06/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.01  --bmc1_out_stat                         full
% 3.06/1.01  --bmc1_ground_init                      false
% 3.06/1.01  --bmc1_pre_inst_next_state              false
% 3.06/1.01  --bmc1_pre_inst_state                   false
% 3.06/1.01  --bmc1_pre_inst_reach_state             false
% 3.06/1.01  --bmc1_out_unsat_core                   false
% 3.06/1.01  --bmc1_aig_witness_out                  false
% 3.06/1.01  --bmc1_verbose                          false
% 3.06/1.01  --bmc1_dump_clauses_tptp                false
% 3.06/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.01  --bmc1_dump_file                        -
% 3.06/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.01  --bmc1_ucm_extend_mode                  1
% 3.06/1.01  --bmc1_ucm_init_mode                    2
% 3.06/1.01  --bmc1_ucm_cone_mode                    none
% 3.06/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.01  --bmc1_ucm_relax_model                  4
% 3.06/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.01  --bmc1_ucm_layered_model                none
% 3.06/1.01  --bmc1_ucm_max_lemma_size               10
% 3.06/1.01  
% 3.06/1.01  ------ AIG Options
% 3.06/1.01  
% 3.06/1.01  --aig_mode                              false
% 3.06/1.01  
% 3.06/1.01  ------ Instantiation Options
% 3.06/1.01  
% 3.06/1.01  --instantiation_flag                    true
% 3.06/1.01  --inst_sos_flag                         false
% 3.06/1.01  --inst_sos_phase                        true
% 3.06/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.01  --inst_lit_sel_side                     num_symb
% 3.06/1.01  --inst_solver_per_active                1400
% 3.06/1.01  --inst_solver_calls_frac                1.
% 3.06/1.01  --inst_passive_queue_type               priority_queues
% 3.06/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.01  --inst_passive_queues_freq              [25;2]
% 3.06/1.01  --inst_dismatching                      true
% 3.06/1.01  --inst_eager_unprocessed_to_passive     true
% 3.06/1.01  --inst_prop_sim_given                   true
% 3.06/1.01  --inst_prop_sim_new                     false
% 3.06/1.01  --inst_subs_new                         false
% 3.06/1.01  --inst_eq_res_simp                      false
% 3.06/1.01  --inst_subs_given                       false
% 3.06/1.01  --inst_orphan_elimination               true
% 3.06/1.01  --inst_learning_loop_flag               true
% 3.06/1.01  --inst_learning_start                   3000
% 3.06/1.01  --inst_learning_factor                  2
% 3.06/1.01  --inst_start_prop_sim_after_learn       3
% 3.06/1.01  --inst_sel_renew                        solver
% 3.06/1.01  --inst_lit_activity_flag                true
% 3.06/1.01  --inst_restr_to_given                   false
% 3.06/1.01  --inst_activity_threshold               500
% 3.06/1.01  --inst_out_proof                        true
% 3.06/1.01  
% 3.06/1.01  ------ Resolution Options
% 3.06/1.01  
% 3.06/1.01  --resolution_flag                       true
% 3.06/1.01  --res_lit_sel                           adaptive
% 3.06/1.01  --res_lit_sel_side                      none
% 3.06/1.01  --res_ordering                          kbo
% 3.06/1.01  --res_to_prop_solver                    active
% 3.06/1.01  --res_prop_simpl_new                    false
% 3.06/1.01  --res_prop_simpl_given                  true
% 3.06/1.01  --res_passive_queue_type                priority_queues
% 3.06/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.01  --res_passive_queues_freq               [15;5]
% 3.06/1.01  --res_forward_subs                      full
% 3.06/1.01  --res_backward_subs                     full
% 3.06/1.01  --res_forward_subs_resolution           true
% 3.06/1.01  --res_backward_subs_resolution          true
% 3.06/1.01  --res_orphan_elimination                true
% 3.06/1.01  --res_time_limit                        2.
% 3.06/1.01  --res_out_proof                         true
% 3.06/1.01  
% 3.06/1.01  ------ Superposition Options
% 3.06/1.01  
% 3.06/1.01  --superposition_flag                    true
% 3.06/1.01  --sup_passive_queue_type                priority_queues
% 3.06/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.01  --demod_completeness_check              fast
% 3.06/1.01  --demod_use_ground                      true
% 3.06/1.01  --sup_to_prop_solver                    passive
% 3.06/1.01  --sup_prop_simpl_new                    true
% 3.06/1.01  --sup_prop_simpl_given                  true
% 3.06/1.01  --sup_fun_splitting                     false
% 3.06/1.01  --sup_smt_interval                      50000
% 3.06/1.01  
% 3.06/1.01  ------ Superposition Simplification Setup
% 3.06/1.01  
% 3.06/1.01  --sup_indices_passive                   []
% 3.06/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_full_bw                           [BwDemod]
% 3.06/1.01  --sup_immed_triv                        [TrivRules]
% 3.06/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_immed_bw_main                     []
% 3.06/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.01  
% 3.06/1.01  ------ Combination Options
% 3.06/1.01  
% 3.06/1.01  --comb_res_mult                         3
% 3.06/1.01  --comb_sup_mult                         2
% 3.06/1.01  --comb_inst_mult                        10
% 3.06/1.01  
% 3.06/1.01  ------ Debug Options
% 3.06/1.01  
% 3.06/1.01  --dbg_backtrace                         false
% 3.06/1.01  --dbg_dump_prop_clauses                 false
% 3.06/1.01  --dbg_dump_prop_clauses_file            -
% 3.06/1.01  --dbg_out_stat                          false
% 3.06/1.01  ------ Parsing...
% 3.06/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/1.01  ------ Proving...
% 3.06/1.01  ------ Problem Properties 
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  clauses                                 15
% 3.06/1.01  conjectures                             2
% 3.06/1.01  EPR                                     1
% 3.06/1.01  Horn                                    14
% 3.06/1.01  unary                                   9
% 3.06/1.01  binary                                  3
% 3.06/1.01  lits                                    24
% 3.06/1.01  lits eq                                 8
% 3.06/1.01  fd_pure                                 0
% 3.06/1.01  fd_pseudo                               0
% 3.06/1.01  fd_cond                                 0
% 3.06/1.01  fd_pseudo_cond                          0
% 3.06/1.01  AC symbols                              0
% 3.06/1.01  
% 3.06/1.01  ------ Schedule dynamic 5 is on 
% 3.06/1.01  
% 3.06/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  ------ 
% 3.06/1.01  Current options:
% 3.06/1.01  ------ 
% 3.06/1.01  
% 3.06/1.01  ------ Input Options
% 3.06/1.01  
% 3.06/1.01  --out_options                           all
% 3.06/1.01  --tptp_safe_out                         true
% 3.06/1.01  --problem_path                          ""
% 3.06/1.01  --include_path                          ""
% 3.06/1.01  --clausifier                            res/vclausify_rel
% 3.06/1.01  --clausifier_options                    --mode clausify
% 3.06/1.01  --stdin                                 false
% 3.06/1.01  --stats_out                             all
% 3.06/1.01  
% 3.06/1.01  ------ General Options
% 3.06/1.01  
% 3.06/1.01  --fof                                   false
% 3.06/1.01  --time_out_real                         305.
% 3.06/1.01  --time_out_virtual                      -1.
% 3.06/1.01  --symbol_type_check                     false
% 3.06/1.01  --clausify_out                          false
% 3.06/1.01  --sig_cnt_out                           false
% 3.06/1.01  --trig_cnt_out                          false
% 3.06/1.01  --trig_cnt_out_tolerance                1.
% 3.06/1.01  --trig_cnt_out_sk_spl                   false
% 3.06/1.01  --abstr_cl_out                          false
% 3.06/1.01  
% 3.06/1.01  ------ Global Options
% 3.06/1.01  
% 3.06/1.01  --schedule                              default
% 3.06/1.01  --add_important_lit                     false
% 3.06/1.01  --prop_solver_per_cl                    1000
% 3.06/1.01  --min_unsat_core                        false
% 3.06/1.01  --soft_assumptions                      false
% 3.06/1.01  --soft_lemma_size                       3
% 3.06/1.01  --prop_impl_unit_size                   0
% 3.06/1.01  --prop_impl_unit                        []
% 3.06/1.01  --share_sel_clauses                     true
% 3.06/1.01  --reset_solvers                         false
% 3.06/1.01  --bc_imp_inh                            [conj_cone]
% 3.06/1.01  --conj_cone_tolerance                   3.
% 3.06/1.01  --extra_neg_conj                        none
% 3.06/1.01  --large_theory_mode                     true
% 3.06/1.01  --prolific_symb_bound                   200
% 3.06/1.01  --lt_threshold                          2000
% 3.06/1.01  --clause_weak_htbl                      true
% 3.06/1.01  --gc_record_bc_elim                     false
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing Options
% 3.06/1.01  
% 3.06/1.01  --preprocessing_flag                    true
% 3.06/1.01  --time_out_prep_mult                    0.1
% 3.06/1.01  --splitting_mode                        input
% 3.06/1.01  --splitting_grd                         true
% 3.06/1.01  --splitting_cvd                         false
% 3.06/1.01  --splitting_cvd_svl                     false
% 3.06/1.01  --splitting_nvd                         32
% 3.06/1.01  --sub_typing                            true
% 3.06/1.01  --prep_gs_sim                           true
% 3.06/1.01  --prep_unflatten                        true
% 3.06/1.01  --prep_res_sim                          true
% 3.06/1.01  --prep_upred                            true
% 3.06/1.01  --prep_sem_filter                       exhaustive
% 3.06/1.01  --prep_sem_filter_out                   false
% 3.06/1.01  --pred_elim                             true
% 3.06/1.01  --res_sim_input                         true
% 3.06/1.01  --eq_ax_congr_red                       true
% 3.06/1.01  --pure_diseq_elim                       true
% 3.06/1.01  --brand_transform                       false
% 3.06/1.01  --non_eq_to_eq                          false
% 3.06/1.01  --prep_def_merge                        true
% 3.06/1.01  --prep_def_merge_prop_impl              false
% 3.06/1.01  --prep_def_merge_mbd                    true
% 3.06/1.01  --prep_def_merge_tr_red                 false
% 3.06/1.01  --prep_def_merge_tr_cl                  false
% 3.06/1.01  --smt_preprocessing                     true
% 3.06/1.01  --smt_ac_axioms                         fast
% 3.06/1.01  --preprocessed_out                      false
% 3.06/1.01  --preprocessed_stats                    false
% 3.06/1.01  
% 3.06/1.01  ------ Abstraction refinement Options
% 3.06/1.01  
% 3.06/1.01  --abstr_ref                             []
% 3.06/1.01  --abstr_ref_prep                        false
% 3.06/1.01  --abstr_ref_until_sat                   false
% 3.06/1.01  --abstr_ref_sig_restrict                funpre
% 3.06/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.01  --abstr_ref_under                       []
% 3.06/1.01  
% 3.06/1.01  ------ SAT Options
% 3.06/1.01  
% 3.06/1.01  --sat_mode                              false
% 3.06/1.01  --sat_fm_restart_options                ""
% 3.06/1.01  --sat_gr_def                            false
% 3.06/1.01  --sat_epr_types                         true
% 3.06/1.01  --sat_non_cyclic_types                  false
% 3.06/1.01  --sat_finite_models                     false
% 3.06/1.01  --sat_fm_lemmas                         false
% 3.06/1.01  --sat_fm_prep                           false
% 3.06/1.01  --sat_fm_uc_incr                        true
% 3.06/1.01  --sat_out_model                         small
% 3.06/1.01  --sat_out_clauses                       false
% 3.06/1.01  
% 3.06/1.01  ------ QBF Options
% 3.06/1.01  
% 3.06/1.01  --qbf_mode                              false
% 3.06/1.01  --qbf_elim_univ                         false
% 3.06/1.01  --qbf_dom_inst                          none
% 3.06/1.01  --qbf_dom_pre_inst                      false
% 3.06/1.01  --qbf_sk_in                             false
% 3.06/1.01  --qbf_pred_elim                         true
% 3.06/1.01  --qbf_split                             512
% 3.06/1.01  
% 3.06/1.01  ------ BMC1 Options
% 3.06/1.01  
% 3.06/1.01  --bmc1_incremental                      false
% 3.06/1.01  --bmc1_axioms                           reachable_all
% 3.06/1.01  --bmc1_min_bound                        0
% 3.06/1.01  --bmc1_max_bound                        -1
% 3.06/1.01  --bmc1_max_bound_default                -1
% 3.06/1.01  --bmc1_symbol_reachability              true
% 3.06/1.01  --bmc1_property_lemmas                  false
% 3.06/1.01  --bmc1_k_induction                      false
% 3.06/1.01  --bmc1_non_equiv_states                 false
% 3.06/1.01  --bmc1_deadlock                         false
% 3.06/1.01  --bmc1_ucm                              false
% 3.06/1.01  --bmc1_add_unsat_core                   none
% 3.06/1.01  --bmc1_unsat_core_children              false
% 3.06/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.01  --bmc1_out_stat                         full
% 3.06/1.01  --bmc1_ground_init                      false
% 3.06/1.01  --bmc1_pre_inst_next_state              false
% 3.06/1.01  --bmc1_pre_inst_state                   false
% 3.06/1.01  --bmc1_pre_inst_reach_state             false
% 3.06/1.01  --bmc1_out_unsat_core                   false
% 3.06/1.01  --bmc1_aig_witness_out                  false
% 3.06/1.01  --bmc1_verbose                          false
% 3.06/1.01  --bmc1_dump_clauses_tptp                false
% 3.06/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.01  --bmc1_dump_file                        -
% 3.06/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.01  --bmc1_ucm_extend_mode                  1
% 3.06/1.01  --bmc1_ucm_init_mode                    2
% 3.06/1.01  --bmc1_ucm_cone_mode                    none
% 3.06/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.01  --bmc1_ucm_relax_model                  4
% 3.06/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.01  --bmc1_ucm_layered_model                none
% 3.06/1.01  --bmc1_ucm_max_lemma_size               10
% 3.06/1.01  
% 3.06/1.01  ------ AIG Options
% 3.06/1.01  
% 3.06/1.01  --aig_mode                              false
% 3.06/1.01  
% 3.06/1.01  ------ Instantiation Options
% 3.06/1.01  
% 3.06/1.01  --instantiation_flag                    true
% 3.06/1.01  --inst_sos_flag                         false
% 3.06/1.01  --inst_sos_phase                        true
% 3.06/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.01  --inst_lit_sel_side                     none
% 3.06/1.01  --inst_solver_per_active                1400
% 3.06/1.01  --inst_solver_calls_frac                1.
% 3.06/1.01  --inst_passive_queue_type               priority_queues
% 3.06/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.01  --inst_passive_queues_freq              [25;2]
% 3.06/1.01  --inst_dismatching                      true
% 3.06/1.01  --inst_eager_unprocessed_to_passive     true
% 3.06/1.01  --inst_prop_sim_given                   true
% 3.06/1.01  --inst_prop_sim_new                     false
% 3.06/1.01  --inst_subs_new                         false
% 3.06/1.01  --inst_eq_res_simp                      false
% 3.06/1.01  --inst_subs_given                       false
% 3.06/1.01  --inst_orphan_elimination               true
% 3.06/1.01  --inst_learning_loop_flag               true
% 3.06/1.01  --inst_learning_start                   3000
% 3.06/1.01  --inst_learning_factor                  2
% 3.06/1.01  --inst_start_prop_sim_after_learn       3
% 3.06/1.01  --inst_sel_renew                        solver
% 3.06/1.01  --inst_lit_activity_flag                true
% 3.06/1.01  --inst_restr_to_given                   false
% 3.06/1.01  --inst_activity_threshold               500
% 3.06/1.01  --inst_out_proof                        true
% 3.06/1.01  
% 3.06/1.01  ------ Resolution Options
% 3.06/1.01  
% 3.06/1.01  --resolution_flag                       false
% 3.06/1.01  --res_lit_sel                           adaptive
% 3.06/1.01  --res_lit_sel_side                      none
% 3.06/1.01  --res_ordering                          kbo
% 3.06/1.01  --res_to_prop_solver                    active
% 3.06/1.01  --res_prop_simpl_new                    false
% 3.06/1.01  --res_prop_simpl_given                  true
% 3.06/1.01  --res_passive_queue_type                priority_queues
% 3.06/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.01  --res_passive_queues_freq               [15;5]
% 3.06/1.01  --res_forward_subs                      full
% 3.06/1.01  --res_backward_subs                     full
% 3.06/1.01  --res_forward_subs_resolution           true
% 3.06/1.01  --res_backward_subs_resolution          true
% 3.06/1.01  --res_orphan_elimination                true
% 3.06/1.01  --res_time_limit                        2.
% 3.06/1.01  --res_out_proof                         true
% 3.06/1.01  
% 3.06/1.01  ------ Superposition Options
% 3.06/1.01  
% 3.06/1.01  --superposition_flag                    true
% 3.06/1.01  --sup_passive_queue_type                priority_queues
% 3.06/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.01  --demod_completeness_check              fast
% 3.06/1.01  --demod_use_ground                      true
% 3.06/1.01  --sup_to_prop_solver                    passive
% 3.06/1.01  --sup_prop_simpl_new                    true
% 3.06/1.01  --sup_prop_simpl_given                  true
% 3.06/1.01  --sup_fun_splitting                     false
% 3.06/1.01  --sup_smt_interval                      50000
% 3.06/1.01  
% 3.06/1.01  ------ Superposition Simplification Setup
% 3.06/1.01  
% 3.06/1.01  --sup_indices_passive                   []
% 3.06/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_full_bw                           [BwDemod]
% 3.06/1.01  --sup_immed_triv                        [TrivRules]
% 3.06/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_immed_bw_main                     []
% 3.06/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.01  
% 3.06/1.01  ------ Combination Options
% 3.06/1.01  
% 3.06/1.01  --comb_res_mult                         3
% 3.06/1.01  --comb_sup_mult                         2
% 3.06/1.01  --comb_inst_mult                        10
% 3.06/1.01  
% 3.06/1.01  ------ Debug Options
% 3.06/1.01  
% 3.06/1.01  --dbg_backtrace                         false
% 3.06/1.01  --dbg_dump_prop_clauses                 false
% 3.06/1.01  --dbg_dump_prop_clauses_file            -
% 3.06/1.01  --dbg_out_stat                          false
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  ------ Proving...
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  % SZS status Theorem for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  fof(f1,axiom,(
% 3.06/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f18,plain,(
% 3.06/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.06/1.01    inference(ennf_transformation,[],[f1])).
% 3.06/1.01  
% 3.06/1.01  fof(f24,plain,(
% 3.06/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.01    inference(nnf_transformation,[],[f18])).
% 3.06/1.01  
% 3.06/1.01  fof(f25,plain,(
% 3.06/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.01    inference(rectify,[],[f24])).
% 3.06/1.01  
% 3.06/1.01  fof(f26,plain,(
% 3.06/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f27,plain,(
% 3.06/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.06/1.01  
% 3.06/1.01  fof(f31,plain,(
% 3.06/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f27])).
% 3.06/1.01  
% 3.06/1.01  fof(f16,conjecture,(
% 3.06/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f17,negated_conjecture,(
% 3.06/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 3.06/1.01    inference(negated_conjecture,[],[f16])).
% 3.06/1.01  
% 3.06/1.01  fof(f23,plain,(
% 3.06/1.01    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/1.01    inference(ennf_transformation,[],[f17])).
% 3.06/1.01  
% 3.06/1.01  fof(f28,plain,(
% 3.06/1.01    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f29,plain,(
% 3.06/1.01    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f28])).
% 3.06/1.01  
% 3.06/1.01  fof(f47,plain,(
% 3.06/1.01    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.06/1.01    inference(cnf_transformation,[],[f29])).
% 3.06/1.01  
% 3.06/1.01  fof(f14,axiom,(
% 3.06/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f20,plain,(
% 3.06/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/1.01    inference(ennf_transformation,[],[f14])).
% 3.06/1.01  
% 3.06/1.01  fof(f45,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f20])).
% 3.06/1.01  
% 3.06/1.01  fof(f32,plain,(
% 3.06/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f27])).
% 3.06/1.01  
% 3.06/1.01  fof(f4,axiom,(
% 3.06/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f19,plain,(
% 3.06/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.06/1.01    inference(ennf_transformation,[],[f4])).
% 3.06/1.01  
% 3.06/1.01  fof(f35,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f19])).
% 3.06/1.01  
% 3.06/1.01  fof(f5,axiom,(
% 3.06/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f36,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f5])).
% 3.06/1.01  
% 3.06/1.01  fof(f11,axiom,(
% 3.06/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f42,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f11])).
% 3.06/1.01  
% 3.06/1.01  fof(f9,axiom,(
% 3.06/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f40,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f9])).
% 3.06/1.01  
% 3.06/1.01  fof(f10,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f41,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f10])).
% 3.06/1.01  
% 3.06/1.01  fof(f49,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.06/1.01    inference(definition_unfolding,[],[f40,f41])).
% 3.06/1.01  
% 3.06/1.01  fof(f50,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.06/1.01    inference(definition_unfolding,[],[f42,f49])).
% 3.06/1.01  
% 3.06/1.01  fof(f2,axiom,(
% 3.06/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f33,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f2])).
% 3.06/1.01  
% 3.06/1.01  fof(f52,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.06/1.01    inference(definition_unfolding,[],[f36,f50,f50,f33])).
% 3.06/1.01  
% 3.06/1.01  fof(f13,axiom,(
% 3.06/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f44,plain,(
% 3.06/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f13])).
% 3.06/1.01  
% 3.06/1.01  fof(f12,axiom,(
% 3.06/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f43,plain,(
% 3.06/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.06/1.01    inference(cnf_transformation,[],[f12])).
% 3.06/1.01  
% 3.06/1.01  fof(f15,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f21,plain,(
% 3.06/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.06/1.01    inference(ennf_transformation,[],[f15])).
% 3.06/1.01  
% 3.06/1.01  fof(f22,plain,(
% 3.06/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/1.01    inference(flattening,[],[f21])).
% 3.06/1.01  
% 3.06/1.01  fof(f46,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f22])).
% 3.06/1.01  
% 3.06/1.01  fof(f56,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/1.01    inference(definition_unfolding,[],[f46,f50])).
% 3.06/1.01  
% 3.06/1.01  fof(f8,axiom,(
% 3.06/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f39,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f8])).
% 3.06/1.01  
% 3.06/1.01  fof(f55,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.06/1.01    inference(definition_unfolding,[],[f39,f49,f49])).
% 3.06/1.01  
% 3.06/1.01  fof(f7,axiom,(
% 3.06/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f38,plain,(
% 3.06/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f7])).
% 3.06/1.01  
% 3.06/1.01  fof(f54,plain,(
% 3.06/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.06/1.01    inference(definition_unfolding,[],[f38,f50])).
% 3.06/1.01  
% 3.06/1.01  fof(f6,axiom,(
% 3.06/1.01    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f37,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 3.06/1.01    inference(cnf_transformation,[],[f6])).
% 3.06/1.01  
% 3.06/1.01  fof(f53,plain,(
% 3.06/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0) )),
% 3.06/1.01    inference(definition_unfolding,[],[f37,f33,f50])).
% 3.06/1.01  
% 3.06/1.01  fof(f3,axiom,(
% 3.06/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f34,plain,(
% 3.06/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.06/1.01    inference(cnf_transformation,[],[f3])).
% 3.06/1.01  
% 3.06/1.01  fof(f51,plain,(
% 3.06/1.01    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.06/1.01    inference(definition_unfolding,[],[f34,f50])).
% 3.06/1.01  
% 3.06/1.01  fof(f48,plain,(
% 3.06/1.01    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))),
% 3.06/1.01    inference(cnf_transformation,[],[f29])).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1,plain,
% 3.06/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.06/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_401,plain,
% 3.06/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.06/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_14,negated_conjecture,
% 3.06/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_394,plain,
% 3.06/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_11,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/1.01      | ~ r2_hidden(X2,X0)
% 3.06/1.01      | r2_hidden(X2,X1) ),
% 3.06/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_396,plain,
% 3.06/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.06/1.01      | r2_hidden(X2,X0) != iProver_top
% 3.06/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1339,plain,
% 3.06/1.01      ( r2_hidden(X0,sK2) != iProver_top
% 3.06/1.01      | r2_hidden(X0,sK1) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_394,c_396]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2451,plain,
% 3.06/1.01      ( r2_hidden(sK0(sK2,X0),sK1) = iProver_top
% 3.06/1.01      | r1_tarski(sK2,X0) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_401,c_1339]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_0,plain,
% 3.06/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.06/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_402,plain,
% 3.06/1.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.06/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3092,plain,
% 3.06/1.01      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_2451,c_402]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4,plain,
% 3.06/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.06/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_399,plain,
% 3.06/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4046,plain,
% 3.06/1.01      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_3092,c_399]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8896,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK2,sK2))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_4046,c_5]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_10,plain,
% 3.06/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_397,plain,
% 3.06/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_9,plain,
% 3.06/1.01      ( k2_subset_1(X0) = X0 ),
% 3.06/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_407,plain,
% 3.06/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.06/1.01      inference(light_normalisation,[status(thm)],[c_397,c_9]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_12,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.06/1.01      | k3_tarski(k2_enumset1(X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 3.06/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_395,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.06/1.01      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.06/1.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_697,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X0,X0,X1)
% 3.06/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_407,c_395]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2192,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k4_subset_1(sK1,sK1,sK2) ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_394,c_697]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8,plain,
% 3.06/1.01      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_7,plain,
% 3.06/1.01      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 3.06/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_398,plain,
% 3.06/1.01      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_602,plain,
% 3.06/1.01      ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_8,c_398]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2603,plain,
% 3.06/1.01      ( r1_tarski(sK2,k4_subset_1(sK1,sK1,sK2)) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_2192,c_602]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2719,plain,
% 3.06/1.01      ( k3_xboole_0(sK2,k4_subset_1(sK1,sK1,sK2)) = sK2 ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_2603,c_399]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_6,plain,
% 3.06/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0 ),
% 3.06/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_712,plain,
% 3.06/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) = k1_xboole_0 ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2602,plain,
% 3.06/1.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k4_subset_1(sK1,sK1,sK2))) = k1_xboole_0 ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_2192,c_712]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4113,plain,
% 3.06/1.01      ( k5_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_2719,c_2602]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8898,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0)) = k4_subset_1(sK1,sK1,sK2) ),
% 3.06/1.01      inference(light_normalisation,[status(thm)],[c_8896,c_2192,c_4113]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.06/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8899,plain,
% 3.06/1.01      ( k4_subset_1(sK1,sK1,sK2) = sK1 ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_8898,c_3]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_696,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(sK2,sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
% 3.06/1.01      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_394,c_395]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_980,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(sK2,sK2,sK2,sK1)) = k4_subset_1(sK1,sK2,sK1) ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_407,c_696]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1109,plain,
% 3.06/1.01      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k4_subset_1(sK1,sK2,sK1) ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_8,c_980]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2599,plain,
% 3.06/1.01      ( k4_subset_1(sK1,sK1,sK2) = k4_subset_1(sK1,sK2,sK1) ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_2192,c_1109]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_13,negated_conjecture,
% 3.06/1.01      ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_412,plain,
% 3.06/1.01      ( k4_subset_1(sK1,sK2,sK1) != sK1 ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_13,c_9]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2730,plain,
% 3.06/1.01      ( k4_subset_1(sK1,sK1,sK2) != sK1 ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_2599,c_412]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(contradiction,plain,
% 3.06/1.01      ( $false ),
% 3.06/1.01      inference(minisat,[status(thm)],[c_8899,c_2730]) ).
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  ------                               Statistics
% 3.06/1.01  
% 3.06/1.01  ------ General
% 3.06/1.01  
% 3.06/1.01  abstr_ref_over_cycles:                  0
% 3.06/1.01  abstr_ref_under_cycles:                 0
% 3.06/1.01  gc_basic_clause_elim:                   0
% 3.06/1.01  forced_gc_time:                         0
% 3.06/1.01  parsing_time:                           0.01
% 3.06/1.01  unif_index_cands_time:                  0.
% 3.06/1.01  unif_index_add_time:                    0.
% 3.06/1.01  orderings_time:                         0.
% 3.06/1.01  out_proof_time:                         0.022
% 3.06/1.01  total_time:                             0.407
% 3.06/1.01  num_of_symbols:                         45
% 3.06/1.01  num_of_terms:                           8453
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing
% 3.06/1.01  
% 3.06/1.01  num_of_splits:                          0
% 3.06/1.01  num_of_split_atoms:                     0
% 3.06/1.01  num_of_reused_defs:                     0
% 3.06/1.01  num_eq_ax_congr_red:                    18
% 3.06/1.01  num_of_sem_filtered_clauses:            1
% 3.06/1.01  num_of_subtypes:                        0
% 3.06/1.01  monotx_restored_types:                  0
% 3.06/1.01  sat_num_of_epr_types:                   0
% 3.06/1.01  sat_num_of_non_cyclic_types:            0
% 3.06/1.01  sat_guarded_non_collapsed_types:        0
% 3.06/1.01  num_pure_diseq_elim:                    0
% 3.06/1.01  simp_replaced_by:                       0
% 3.06/1.01  res_preprocessed:                       70
% 3.06/1.01  prep_upred:                             0
% 3.06/1.01  prep_unflattend:                        8
% 3.06/1.01  smt_new_axioms:                         0
% 3.06/1.01  pred_elim_cands:                        3
% 3.06/1.01  pred_elim:                              0
% 3.06/1.01  pred_elim_cl:                           0
% 3.06/1.01  pred_elim_cycles:                       1
% 3.06/1.01  merged_defs:                            0
% 3.06/1.01  merged_defs_ncl:                        0
% 3.06/1.01  bin_hyper_res:                          0
% 3.06/1.01  prep_cycles:                            3
% 3.06/1.01  pred_elim_time:                         0.001
% 3.06/1.01  splitting_time:                         0.
% 3.06/1.01  sem_filter_time:                        0.
% 3.06/1.01  monotx_time:                            0.001
% 3.06/1.01  subtype_inf_time:                       0.
% 3.06/1.01  
% 3.06/1.01  ------ Problem properties
% 3.06/1.01  
% 3.06/1.01  clauses:                                15
% 3.06/1.01  conjectures:                            2
% 3.06/1.01  epr:                                    1
% 3.06/1.01  horn:                                   14
% 3.06/1.01  ground:                                 2
% 3.06/1.01  unary:                                  9
% 3.06/1.01  binary:                                 3
% 3.06/1.01  lits:                                   24
% 3.06/1.01  lits_eq:                                8
% 3.06/1.01  fd_pure:                                0
% 3.06/1.01  fd_pseudo:                              0
% 3.06/1.01  fd_cond:                                0
% 3.06/1.01  fd_pseudo_cond:                         0
% 3.06/1.01  ac_symbols:                             0
% 3.06/1.01  
% 3.06/1.01  ------ Propositional Solver
% 3.06/1.01  
% 3.06/1.01  prop_solver_calls:                      25
% 3.06/1.01  prop_fast_solver_calls:                 392
% 3.06/1.01  smt_solver_calls:                       0
% 3.06/1.01  smt_fast_solver_calls:                  0
% 3.06/1.01  prop_num_of_clauses:                    3427
% 3.06/1.01  prop_preprocess_simplified:             7554
% 3.06/1.01  prop_fo_subsumed:                       0
% 3.06/1.01  prop_solver_time:                       0.
% 3.06/1.01  smt_solver_time:                        0.
% 3.06/1.01  smt_fast_solver_time:                   0.
% 3.06/1.01  prop_fast_solver_time:                  0.
% 3.06/1.01  prop_unsat_core_time:                   0.
% 3.06/1.01  
% 3.06/1.01  ------ QBF
% 3.06/1.01  
% 3.06/1.01  qbf_q_res:                              0
% 3.06/1.01  qbf_num_tautologies:                    0
% 3.06/1.01  qbf_prep_cycles:                        0
% 3.06/1.01  
% 3.06/1.01  ------ BMC1
% 3.06/1.01  
% 3.06/1.01  bmc1_current_bound:                     -1
% 3.06/1.01  bmc1_last_solved_bound:                 -1
% 3.06/1.01  bmc1_unsat_core_size:                   -1
% 3.06/1.01  bmc1_unsat_core_parents_size:           -1
% 3.06/1.01  bmc1_merge_next_fun:                    0
% 3.06/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.01  
% 3.06/1.01  ------ Instantiation
% 3.06/1.01  
% 3.06/1.01  inst_num_of_clauses:                    1225
% 3.06/1.01  inst_num_in_passive:                    552
% 3.06/1.01  inst_num_in_active:                     442
% 3.06/1.01  inst_num_in_unprocessed:                231
% 3.06/1.01  inst_num_of_loops:                      480
% 3.06/1.01  inst_num_of_learning_restarts:          0
% 3.06/1.01  inst_num_moves_active_passive:          34
% 3.06/1.01  inst_lit_activity:                      0
% 3.06/1.01  inst_lit_activity_moves:                0
% 3.06/1.01  inst_num_tautologies:                   0
% 3.06/1.01  inst_num_prop_implied:                  0
% 3.06/1.01  inst_num_existing_simplified:           0
% 3.06/1.01  inst_num_eq_res_simplified:             0
% 3.06/1.01  inst_num_child_elim:                    0
% 3.06/1.01  inst_num_of_dismatching_blockings:      551
% 3.06/1.01  inst_num_of_non_proper_insts:           970
% 3.06/1.01  inst_num_of_duplicates:                 0
% 3.06/1.01  inst_inst_num_from_inst_to_res:         0
% 3.06/1.01  inst_dismatching_checking_time:         0.
% 3.06/1.01  
% 3.06/1.01  ------ Resolution
% 3.06/1.01  
% 3.06/1.01  res_num_of_clauses:                     0
% 3.06/1.01  res_num_in_passive:                     0
% 3.06/1.01  res_num_in_active:                      0
% 3.06/1.01  res_num_of_loops:                       73
% 3.06/1.01  res_forward_subset_subsumed:            100
% 3.06/1.01  res_backward_subset_subsumed:           0
% 3.06/1.01  res_forward_subsumed:                   0
% 3.06/1.01  res_backward_subsumed:                  0
% 3.06/1.01  res_forward_subsumption_resolution:     0
% 3.06/1.01  res_backward_subsumption_resolution:    0
% 3.06/1.01  res_clause_to_clause_subsumption:       1137
% 3.06/1.01  res_orphan_elimination:                 0
% 3.06/1.01  res_tautology_del:                      100
% 3.06/1.01  res_num_eq_res_simplified:              0
% 3.06/1.01  res_num_sel_changes:                    0
% 3.06/1.01  res_moves_from_active_to_pass:          0
% 3.06/1.01  
% 3.06/1.01  ------ Superposition
% 3.06/1.01  
% 3.06/1.01  sup_time_total:                         0.
% 3.06/1.01  sup_time_generating:                    0.
% 3.06/1.01  sup_time_sim_full:                      0.
% 3.06/1.01  sup_time_sim_immed:                     0.
% 3.06/1.01  
% 3.06/1.01  sup_num_of_clauses:                     210
% 3.06/1.01  sup_num_in_active:                      62
% 3.06/1.01  sup_num_in_passive:                     148
% 3.06/1.01  sup_num_of_loops:                       94
% 3.06/1.01  sup_fw_superposition:                   389
% 3.06/1.01  sup_bw_superposition:                   306
% 3.06/1.01  sup_immediate_simplified:               183
% 3.06/1.01  sup_given_eliminated:                   0
% 3.06/1.01  comparisons_done:                       0
% 3.06/1.01  comparisons_avoided:                    0
% 3.06/1.01  
% 3.06/1.01  ------ Simplifications
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  sim_fw_subset_subsumed:                 0
% 3.06/1.01  sim_bw_subset_subsumed:                 0
% 3.06/1.01  sim_fw_subsumed:                        39
% 3.06/1.01  sim_bw_subsumed:                        1
% 3.06/1.01  sim_fw_subsumption_res:                 0
% 3.06/1.01  sim_bw_subsumption_res:                 0
% 3.06/1.01  sim_tautology_del:                      1
% 3.06/1.01  sim_eq_tautology_del:                   12
% 3.06/1.01  sim_eq_res_simp:                        0
% 3.06/1.01  sim_fw_demodulated:                     67
% 3.06/1.01  sim_bw_demodulated:                     37
% 3.06/1.01  sim_light_normalised:                   127
% 3.06/1.01  sim_joinable_taut:                      0
% 3.06/1.01  sim_joinable_simp:                      0
% 3.06/1.01  sim_ac_normalised:                      0
% 3.06/1.01  sim_smt_subsumption:                    0
% 3.06/1.01  
%------------------------------------------------------------------------------
