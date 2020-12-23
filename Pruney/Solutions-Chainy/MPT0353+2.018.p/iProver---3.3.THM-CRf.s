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
% DateTime   : Thu Dec  3 11:39:41 EST 2020

% Result     : Theorem 11.83s
% Output     : CNFRefutation 11.83s
% Verified   : 
% Statistics : Number of formulae       :  117 (1954 expanded)
%              Number of clauses        :   76 ( 679 expanded)
%              Number of leaves         :   14 ( 503 expanded)
%              Depth                    :   19
%              Number of atoms          :  154 (3148 expanded)
%              Number of equality atoms :  115 (1926 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f7,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f27])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k7_subset_1(X0,X1,sK2) != k9_subset_1(X0,X1,k3_subset_1(X0,sK2))
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f27,f27])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f26,f27,f27,f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_367,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_369,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_367,c_7])).

cnf(c_494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_369])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_364,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_599,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_494,c_364])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_363,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_596,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(sK0,X0,sK2) ),
    inference(superposition,[status(thm)],[c_363,c_364])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_750,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = k9_subset_1(sK0,X0,sK2) ),
    inference(superposition,[status(thm)],[c_596,c_1])).

cnf(c_1731,plain,
    ( k9_subset_1(X0,sK2,X0) = k9_subset_1(sK0,X0,sK2) ),
    inference(superposition,[status(thm)],[c_599,c_750])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_745,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k9_subset_1(sK0,X0,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_596,c_0])).

cnf(c_756,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k9_subset_1(sK0,X0,sK2))) = k9_subset_1(sK0,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_745,c_596])).

cnf(c_2689,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k9_subset_1(X0,sK2,X0))) = k9_subset_1(sK0,X0,sK2) ),
    inference(superposition,[status(thm)],[c_1731,c_756])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_368,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4223,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_369,c_368])).

cnf(c_1720,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X0,X1,X0) ),
    inference(superposition,[status(thm)],[c_599,c_1])).

cnf(c_4234,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X0,X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_4223,c_1720])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_362,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_366,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4144,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_362,c_366])).

cnf(c_4222,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_362,c_368])).

cnf(c_4317,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4144,c_4144,c_4222])).

cnf(c_25564,plain,
    ( k9_subset_1(sK0,sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_4234,c_4317])).

cnf(c_598,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k9_subset_1(X1,X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_369,c_364])).

cnf(c_3,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1121,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k9_subset_1(X1,X3,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,X3),k4_xboole_0(k5_xboole_0(X0,X3),k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_598,c_3])).

cnf(c_13358,plain,
    ( k5_xboole_0(k9_subset_1(X0,k4_xboole_0(X1,X2),X0),k9_subset_1(X1,X3,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,X3),k4_xboole_0(k5_xboole_0(X0,X3),k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_1121,c_1720])).

cnf(c_13412,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X2)))) = k5_xboole_0(k9_subset_1(X0,X2,X0),k9_subset_1(X2,X1,X2)) ),
    inference(superposition,[status(thm)],[c_2,c_13358])).

cnf(c_13738,plain,
    ( k5_xboole_0(k9_subset_1(X0,X1,X0),k9_subset_1(X1,X2,X1)) = k9_subset_1(k5_xboole_0(X0,X2),X1,k5_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_13412,c_2,c_1720])).

cnf(c_26286,plain,
    ( k9_subset_1(k5_xboole_0(sK0,X0),sK1,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK1,k9_subset_1(sK1,X0,sK1)) ),
    inference(superposition,[status(thm)],[c_25564,c_13738])).

cnf(c_597,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k9_subset_1(sK0,X0,sK1) ),
    inference(superposition,[status(thm)],[c_362,c_364])).

cnf(c_809,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k9_subset_1(sK0,X0,sK1) ),
    inference(superposition,[status(thm)],[c_597,c_1])).

cnf(c_1288,plain,
    ( k5_xboole_0(sK1,k9_subset_1(sK0,X0,sK1)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_809,c_0])).

cnf(c_1727,plain,
    ( k9_subset_1(sK1,X0,sK1) = k9_subset_1(sK0,X0,sK1) ),
    inference(superposition,[status(thm)],[c_599,c_597])).

cnf(c_26314,plain,
    ( k9_subset_1(k5_xboole_0(sK0,X0),sK1,k5_xboole_0(sK0,X0)) = k4_xboole_0(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_26286,c_1288,c_1727])).

cnf(c_30648,plain,
    ( k9_subset_1(k9_subset_1(sK0,sK0,sK2),sK1,k9_subset_1(sK0,sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK0))) ),
    inference(superposition,[status(thm)],[c_2689,c_26314])).

cnf(c_4143,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_363,c_366])).

cnf(c_4221,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_363,c_368])).

cnf(c_4246,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4143,c_4143,c_4221])).

cnf(c_25563,plain,
    ( k9_subset_1(sK0,sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_4234,c_4246])).

cnf(c_26090,plain,
    ( k9_subset_1(sK0,sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_25563,c_1731])).

cnf(c_30706,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k9_subset_1(sK2,sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_30648,c_25563,c_26090])).

cnf(c_1726,plain,
    ( k9_subset_1(sK2,X0,sK2) = k9_subset_1(sK0,X0,sK2) ),
    inference(superposition,[status(thm)],[c_599,c_596])).

cnf(c_30707,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_30706,c_1726])).

cnf(c_30792,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_30707,c_598])).

cnf(c_30797,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_30707,c_809])).

cnf(c_1071,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k9_subset_1(sK0,X1,sK2)) = k4_xboole_0(k5_xboole_0(X0,sK2),k4_xboole_0(k5_xboole_0(X0,sK2),X1)) ),
    inference(superposition,[status(thm)],[c_750,c_3])).

cnf(c_8870,plain,
    ( k5_xboole_0(k9_subset_1(X0,X1,X0),k9_subset_1(sK0,X1,sK2)) = k4_xboole_0(k5_xboole_0(X0,sK2),k4_xboole_0(k5_xboole_0(X0,sK2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1071,c_1071,c_1720])).

cnf(c_8871,plain,
    ( k5_xboole_0(k9_subset_1(X0,X1,X0),k9_subset_1(sK0,X1,sK2)) = k9_subset_1(k5_xboole_0(X0,sK2),X1,k5_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_8870,c_1720])).

cnf(c_26289,plain,
    ( k9_subset_1(k5_xboole_0(sK0,sK2),sK1,k5_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_25564,c_8871])).

cnf(c_2316,plain,
    ( k5_xboole_0(X0,k9_subset_1(X0,X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1720,c_0])).

cnf(c_26081,plain,
    ( k5_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_25563,c_2316])).

cnf(c_26309,plain,
    ( k9_subset_1(k4_xboole_0(sK0,sK2),sK1,k4_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_26289,c_26081])).

cnf(c_749,plain,
    ( k5_xboole_0(X0,k9_subset_1(sK0,X0,sK2)) = k4_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_596,c_0])).

cnf(c_1729,plain,
    ( k9_subset_1(k4_xboole_0(X0,X1),X2,k4_xboole_0(X0,X1)) = k9_subset_1(X0,X2,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_599,c_598])).

cnf(c_26310,plain,
    ( k9_subset_1(k4_xboole_0(sK0,sK2),sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_26309,c_749,c_1729])).

cnf(c_1733,plain,
    ( k9_subset_1(X0,sK1,X0) = k9_subset_1(sK0,X0,sK1) ),
    inference(superposition,[status(thm)],[c_599,c_809])).

cnf(c_30366,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_26310,c_1733])).

cnf(c_30808,plain,
    ( k4_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_30797,c_30366])).

cnf(c_30818,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_30792,c_30808])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_365,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4793,plain,
    ( k7_subset_1(sK0,sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_362,c_365])).

cnf(c_10,negated_conjecture,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4318,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k7_subset_1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_4221,c_10])).

cnf(c_5156,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_4793,c_4318])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30818,c_5156])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.83/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.83/2.00  
% 11.83/2.00  ------  iProver source info
% 11.83/2.00  
% 11.83/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.83/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.83/2.00  git: non_committed_changes: false
% 11.83/2.00  git: last_make_outside_of_git: false
% 11.83/2.00  
% 11.83/2.00  ------ 
% 11.83/2.00  
% 11.83/2.00  ------ Input Options
% 11.83/2.00  
% 11.83/2.00  --out_options                           all
% 11.83/2.00  --tptp_safe_out                         true
% 11.83/2.00  --problem_path                          ""
% 11.83/2.00  --include_path                          ""
% 11.83/2.00  --clausifier                            res/vclausify_rel
% 11.83/2.00  --clausifier_options                    ""
% 11.83/2.00  --stdin                                 false
% 11.83/2.00  --stats_out                             all
% 11.83/2.00  
% 11.83/2.00  ------ General Options
% 11.83/2.00  
% 11.83/2.00  --fof                                   false
% 11.83/2.00  --time_out_real                         305.
% 11.83/2.00  --time_out_virtual                      -1.
% 11.83/2.00  --symbol_type_check                     false
% 11.83/2.00  --clausify_out                          false
% 11.83/2.00  --sig_cnt_out                           false
% 11.83/2.00  --trig_cnt_out                          false
% 11.83/2.00  --trig_cnt_out_tolerance                1.
% 11.83/2.00  --trig_cnt_out_sk_spl                   false
% 11.83/2.00  --abstr_cl_out                          false
% 11.83/2.00  
% 11.83/2.00  ------ Global Options
% 11.83/2.00  
% 11.83/2.00  --schedule                              default
% 11.83/2.00  --add_important_lit                     false
% 11.83/2.00  --prop_solver_per_cl                    1000
% 11.83/2.00  --min_unsat_core                        false
% 11.83/2.00  --soft_assumptions                      false
% 11.83/2.00  --soft_lemma_size                       3
% 11.83/2.00  --prop_impl_unit_size                   0
% 11.83/2.00  --prop_impl_unit                        []
% 11.83/2.00  --share_sel_clauses                     true
% 11.83/2.00  --reset_solvers                         false
% 11.83/2.00  --bc_imp_inh                            [conj_cone]
% 11.83/2.00  --conj_cone_tolerance                   3.
% 11.83/2.00  --extra_neg_conj                        none
% 11.83/2.00  --large_theory_mode                     true
% 11.83/2.00  --prolific_symb_bound                   200
% 11.83/2.00  --lt_threshold                          2000
% 11.83/2.00  --clause_weak_htbl                      true
% 11.83/2.00  --gc_record_bc_elim                     false
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing Options
% 11.83/2.00  
% 11.83/2.00  --preprocessing_flag                    true
% 11.83/2.00  --time_out_prep_mult                    0.1
% 11.83/2.00  --splitting_mode                        input
% 11.83/2.00  --splitting_grd                         true
% 11.83/2.00  --splitting_cvd                         false
% 11.83/2.00  --splitting_cvd_svl                     false
% 11.83/2.00  --splitting_nvd                         32
% 11.83/2.00  --sub_typing                            true
% 11.83/2.00  --prep_gs_sim                           true
% 11.83/2.00  --prep_unflatten                        true
% 11.83/2.00  --prep_res_sim                          true
% 11.83/2.00  --prep_upred                            true
% 11.83/2.00  --prep_sem_filter                       exhaustive
% 11.83/2.00  --prep_sem_filter_out                   false
% 11.83/2.00  --pred_elim                             true
% 11.83/2.00  --res_sim_input                         true
% 11.83/2.00  --eq_ax_congr_red                       true
% 11.83/2.00  --pure_diseq_elim                       true
% 11.83/2.00  --brand_transform                       false
% 11.83/2.00  --non_eq_to_eq                          false
% 11.83/2.00  --prep_def_merge                        true
% 11.83/2.00  --prep_def_merge_prop_impl              false
% 11.83/2.00  --prep_def_merge_mbd                    true
% 11.83/2.00  --prep_def_merge_tr_red                 false
% 11.83/2.00  --prep_def_merge_tr_cl                  false
% 11.83/2.00  --smt_preprocessing                     true
% 11.83/2.00  --smt_ac_axioms                         fast
% 11.83/2.00  --preprocessed_out                      false
% 11.83/2.00  --preprocessed_stats                    false
% 11.83/2.00  
% 11.83/2.00  ------ Abstraction refinement Options
% 11.83/2.00  
% 11.83/2.00  --abstr_ref                             []
% 11.83/2.00  --abstr_ref_prep                        false
% 11.83/2.00  --abstr_ref_until_sat                   false
% 11.83/2.00  --abstr_ref_sig_restrict                funpre
% 11.83/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.83/2.00  --abstr_ref_under                       []
% 11.83/2.00  
% 11.83/2.00  ------ SAT Options
% 11.83/2.00  
% 11.83/2.00  --sat_mode                              false
% 11.83/2.00  --sat_fm_restart_options                ""
% 11.83/2.00  --sat_gr_def                            false
% 11.83/2.00  --sat_epr_types                         true
% 11.83/2.00  --sat_non_cyclic_types                  false
% 11.83/2.00  --sat_finite_models                     false
% 11.83/2.00  --sat_fm_lemmas                         false
% 11.83/2.00  --sat_fm_prep                           false
% 11.83/2.00  --sat_fm_uc_incr                        true
% 11.83/2.00  --sat_out_model                         small
% 11.83/2.00  --sat_out_clauses                       false
% 11.83/2.00  
% 11.83/2.00  ------ QBF Options
% 11.83/2.00  
% 11.83/2.00  --qbf_mode                              false
% 11.83/2.00  --qbf_elim_univ                         false
% 11.83/2.00  --qbf_dom_inst                          none
% 11.83/2.00  --qbf_dom_pre_inst                      false
% 11.83/2.00  --qbf_sk_in                             false
% 11.83/2.00  --qbf_pred_elim                         true
% 11.83/2.00  --qbf_split                             512
% 11.83/2.00  
% 11.83/2.00  ------ BMC1 Options
% 11.83/2.00  
% 11.83/2.00  --bmc1_incremental                      false
% 11.83/2.00  --bmc1_axioms                           reachable_all
% 11.83/2.00  --bmc1_min_bound                        0
% 11.83/2.00  --bmc1_max_bound                        -1
% 11.83/2.00  --bmc1_max_bound_default                -1
% 11.83/2.00  --bmc1_symbol_reachability              true
% 11.83/2.00  --bmc1_property_lemmas                  false
% 11.83/2.00  --bmc1_k_induction                      false
% 11.83/2.00  --bmc1_non_equiv_states                 false
% 11.83/2.00  --bmc1_deadlock                         false
% 11.83/2.00  --bmc1_ucm                              false
% 11.83/2.00  --bmc1_add_unsat_core                   none
% 11.83/2.00  --bmc1_unsat_core_children              false
% 11.83/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.83/2.00  --bmc1_out_stat                         full
% 11.83/2.00  --bmc1_ground_init                      false
% 11.83/2.00  --bmc1_pre_inst_next_state              false
% 11.83/2.00  --bmc1_pre_inst_state                   false
% 11.83/2.00  --bmc1_pre_inst_reach_state             false
% 11.83/2.00  --bmc1_out_unsat_core                   false
% 11.83/2.00  --bmc1_aig_witness_out                  false
% 11.83/2.00  --bmc1_verbose                          false
% 11.83/2.00  --bmc1_dump_clauses_tptp                false
% 11.83/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.83/2.00  --bmc1_dump_file                        -
% 11.83/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.83/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.83/2.00  --bmc1_ucm_extend_mode                  1
% 11.83/2.00  --bmc1_ucm_init_mode                    2
% 11.83/2.00  --bmc1_ucm_cone_mode                    none
% 11.83/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.83/2.00  --bmc1_ucm_relax_model                  4
% 11.83/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.83/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.83/2.00  --bmc1_ucm_layered_model                none
% 11.83/2.00  --bmc1_ucm_max_lemma_size               10
% 11.83/2.00  
% 11.83/2.00  ------ AIG Options
% 11.83/2.00  
% 11.83/2.00  --aig_mode                              false
% 11.83/2.00  
% 11.83/2.00  ------ Instantiation Options
% 11.83/2.00  
% 11.83/2.00  --instantiation_flag                    true
% 11.83/2.00  --inst_sos_flag                         true
% 11.83/2.00  --inst_sos_phase                        true
% 11.83/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel_side                     num_symb
% 11.83/2.00  --inst_solver_per_active                1400
% 11.83/2.00  --inst_solver_calls_frac                1.
% 11.83/2.00  --inst_passive_queue_type               priority_queues
% 11.83/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.83/2.00  --inst_passive_queues_freq              [25;2]
% 11.83/2.00  --inst_dismatching                      true
% 11.83/2.00  --inst_eager_unprocessed_to_passive     true
% 11.83/2.00  --inst_prop_sim_given                   true
% 11.83/2.00  --inst_prop_sim_new                     false
% 11.83/2.00  --inst_subs_new                         false
% 11.83/2.00  --inst_eq_res_simp                      false
% 11.83/2.00  --inst_subs_given                       false
% 11.83/2.00  --inst_orphan_elimination               true
% 11.83/2.00  --inst_learning_loop_flag               true
% 11.83/2.00  --inst_learning_start                   3000
% 11.83/2.00  --inst_learning_factor                  2
% 11.83/2.00  --inst_start_prop_sim_after_learn       3
% 11.83/2.00  --inst_sel_renew                        solver
% 11.83/2.00  --inst_lit_activity_flag                true
% 11.83/2.00  --inst_restr_to_given                   false
% 11.83/2.00  --inst_activity_threshold               500
% 11.83/2.00  --inst_out_proof                        true
% 11.83/2.00  
% 11.83/2.00  ------ Resolution Options
% 11.83/2.00  
% 11.83/2.00  --resolution_flag                       true
% 11.83/2.00  --res_lit_sel                           adaptive
% 11.83/2.00  --res_lit_sel_side                      none
% 11.83/2.00  --res_ordering                          kbo
% 11.83/2.00  --res_to_prop_solver                    active
% 11.83/2.00  --res_prop_simpl_new                    false
% 11.83/2.00  --res_prop_simpl_given                  true
% 11.83/2.00  --res_passive_queue_type                priority_queues
% 11.83/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.83/2.00  --res_passive_queues_freq               [15;5]
% 11.83/2.00  --res_forward_subs                      full
% 11.83/2.00  --res_backward_subs                     full
% 11.83/2.00  --res_forward_subs_resolution           true
% 11.83/2.00  --res_backward_subs_resolution          true
% 11.83/2.00  --res_orphan_elimination                true
% 11.83/2.00  --res_time_limit                        2.
% 11.83/2.00  --res_out_proof                         true
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Options
% 11.83/2.00  
% 11.83/2.00  --superposition_flag                    true
% 11.83/2.00  --sup_passive_queue_type                priority_queues
% 11.83/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.83/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.83/2.00  --demod_completeness_check              fast
% 11.83/2.00  --demod_use_ground                      true
% 11.83/2.00  --sup_to_prop_solver                    passive
% 11.83/2.00  --sup_prop_simpl_new                    true
% 11.83/2.00  --sup_prop_simpl_given                  true
% 11.83/2.00  --sup_fun_splitting                     true
% 11.83/2.00  --sup_smt_interval                      50000
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Simplification Setup
% 11.83/2.00  
% 11.83/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.83/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.83/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.83/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.83/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.83/2.00  --sup_immed_triv                        [TrivRules]
% 11.83/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_bw_main                     []
% 11.83/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.83/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.83/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_input_bw                          []
% 11.83/2.00  
% 11.83/2.00  ------ Combination Options
% 11.83/2.00  
% 11.83/2.00  --comb_res_mult                         3
% 11.83/2.00  --comb_sup_mult                         2
% 11.83/2.00  --comb_inst_mult                        10
% 11.83/2.00  
% 11.83/2.00  ------ Debug Options
% 11.83/2.00  
% 11.83/2.00  --dbg_backtrace                         false
% 11.83/2.00  --dbg_dump_prop_clauses                 false
% 11.83/2.00  --dbg_dump_prop_clauses_file            -
% 11.83/2.00  --dbg_out_stat                          false
% 11.83/2.00  ------ Parsing...
% 11.83/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.83/2.00  ------ Proving...
% 11.83/2.00  ------ Problem Properties 
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  clauses                                 13
% 11.83/2.00  conjectures                             3
% 11.83/2.00  EPR                                     0
% 11.83/2.00  Horn                                    13
% 11.83/2.00  unary                                   9
% 11.83/2.00  binary                                  4
% 11.83/2.00  lits                                    17
% 11.83/2.00  lits eq                                 10
% 11.83/2.00  fd_pure                                 0
% 11.83/2.00  fd_pseudo                               0
% 11.83/2.00  fd_cond                                 0
% 11.83/2.00  fd_pseudo_cond                          0
% 11.83/2.00  AC symbols                              0
% 11.83/2.00  
% 11.83/2.00  ------ Schedule dynamic 5 is on 
% 11.83/2.00  
% 11.83/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  ------ 
% 11.83/2.00  Current options:
% 11.83/2.00  ------ 
% 11.83/2.00  
% 11.83/2.00  ------ Input Options
% 11.83/2.00  
% 11.83/2.00  --out_options                           all
% 11.83/2.00  --tptp_safe_out                         true
% 11.83/2.00  --problem_path                          ""
% 11.83/2.00  --include_path                          ""
% 11.83/2.00  --clausifier                            res/vclausify_rel
% 11.83/2.00  --clausifier_options                    ""
% 11.83/2.00  --stdin                                 false
% 11.83/2.00  --stats_out                             all
% 11.83/2.00  
% 11.83/2.00  ------ General Options
% 11.83/2.00  
% 11.83/2.00  --fof                                   false
% 11.83/2.00  --time_out_real                         305.
% 11.83/2.00  --time_out_virtual                      -1.
% 11.83/2.00  --symbol_type_check                     false
% 11.83/2.00  --clausify_out                          false
% 11.83/2.00  --sig_cnt_out                           false
% 11.83/2.00  --trig_cnt_out                          false
% 11.83/2.00  --trig_cnt_out_tolerance                1.
% 11.83/2.00  --trig_cnt_out_sk_spl                   false
% 11.83/2.00  --abstr_cl_out                          false
% 11.83/2.00  
% 11.83/2.00  ------ Global Options
% 11.83/2.00  
% 11.83/2.00  --schedule                              default
% 11.83/2.00  --add_important_lit                     false
% 11.83/2.00  --prop_solver_per_cl                    1000
% 11.83/2.00  --min_unsat_core                        false
% 11.83/2.00  --soft_assumptions                      false
% 11.83/2.00  --soft_lemma_size                       3
% 11.83/2.00  --prop_impl_unit_size                   0
% 11.83/2.00  --prop_impl_unit                        []
% 11.83/2.00  --share_sel_clauses                     true
% 11.83/2.00  --reset_solvers                         false
% 11.83/2.00  --bc_imp_inh                            [conj_cone]
% 11.83/2.00  --conj_cone_tolerance                   3.
% 11.83/2.00  --extra_neg_conj                        none
% 11.83/2.00  --large_theory_mode                     true
% 11.83/2.00  --prolific_symb_bound                   200
% 11.83/2.00  --lt_threshold                          2000
% 11.83/2.00  --clause_weak_htbl                      true
% 11.83/2.00  --gc_record_bc_elim                     false
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing Options
% 11.83/2.00  
% 11.83/2.00  --preprocessing_flag                    true
% 11.83/2.00  --time_out_prep_mult                    0.1
% 11.83/2.00  --splitting_mode                        input
% 11.83/2.00  --splitting_grd                         true
% 11.83/2.00  --splitting_cvd                         false
% 11.83/2.00  --splitting_cvd_svl                     false
% 11.83/2.00  --splitting_nvd                         32
% 11.83/2.00  --sub_typing                            true
% 11.83/2.00  --prep_gs_sim                           true
% 11.83/2.00  --prep_unflatten                        true
% 11.83/2.00  --prep_res_sim                          true
% 11.83/2.00  --prep_upred                            true
% 11.83/2.00  --prep_sem_filter                       exhaustive
% 11.83/2.00  --prep_sem_filter_out                   false
% 11.83/2.00  --pred_elim                             true
% 11.83/2.00  --res_sim_input                         true
% 11.83/2.00  --eq_ax_congr_red                       true
% 11.83/2.00  --pure_diseq_elim                       true
% 11.83/2.00  --brand_transform                       false
% 11.83/2.00  --non_eq_to_eq                          false
% 11.83/2.00  --prep_def_merge                        true
% 11.83/2.00  --prep_def_merge_prop_impl              false
% 11.83/2.00  --prep_def_merge_mbd                    true
% 11.83/2.00  --prep_def_merge_tr_red                 false
% 11.83/2.00  --prep_def_merge_tr_cl                  false
% 11.83/2.00  --smt_preprocessing                     true
% 11.83/2.00  --smt_ac_axioms                         fast
% 11.83/2.00  --preprocessed_out                      false
% 11.83/2.00  --preprocessed_stats                    false
% 11.83/2.00  
% 11.83/2.00  ------ Abstraction refinement Options
% 11.83/2.00  
% 11.83/2.00  --abstr_ref                             []
% 11.83/2.00  --abstr_ref_prep                        false
% 11.83/2.00  --abstr_ref_until_sat                   false
% 11.83/2.00  --abstr_ref_sig_restrict                funpre
% 11.83/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.83/2.00  --abstr_ref_under                       []
% 11.83/2.00  
% 11.83/2.00  ------ SAT Options
% 11.83/2.00  
% 11.83/2.00  --sat_mode                              false
% 11.83/2.00  --sat_fm_restart_options                ""
% 11.83/2.00  --sat_gr_def                            false
% 11.83/2.00  --sat_epr_types                         true
% 11.83/2.00  --sat_non_cyclic_types                  false
% 11.83/2.00  --sat_finite_models                     false
% 11.83/2.00  --sat_fm_lemmas                         false
% 11.83/2.00  --sat_fm_prep                           false
% 11.83/2.00  --sat_fm_uc_incr                        true
% 11.83/2.00  --sat_out_model                         small
% 11.83/2.00  --sat_out_clauses                       false
% 11.83/2.00  
% 11.83/2.00  ------ QBF Options
% 11.83/2.00  
% 11.83/2.00  --qbf_mode                              false
% 11.83/2.00  --qbf_elim_univ                         false
% 11.83/2.00  --qbf_dom_inst                          none
% 11.83/2.00  --qbf_dom_pre_inst                      false
% 11.83/2.00  --qbf_sk_in                             false
% 11.83/2.00  --qbf_pred_elim                         true
% 11.83/2.00  --qbf_split                             512
% 11.83/2.00  
% 11.83/2.00  ------ BMC1 Options
% 11.83/2.00  
% 11.83/2.00  --bmc1_incremental                      false
% 11.83/2.00  --bmc1_axioms                           reachable_all
% 11.83/2.00  --bmc1_min_bound                        0
% 11.83/2.00  --bmc1_max_bound                        -1
% 11.83/2.00  --bmc1_max_bound_default                -1
% 11.83/2.00  --bmc1_symbol_reachability              true
% 11.83/2.00  --bmc1_property_lemmas                  false
% 11.83/2.00  --bmc1_k_induction                      false
% 11.83/2.00  --bmc1_non_equiv_states                 false
% 11.83/2.00  --bmc1_deadlock                         false
% 11.83/2.00  --bmc1_ucm                              false
% 11.83/2.00  --bmc1_add_unsat_core                   none
% 11.83/2.00  --bmc1_unsat_core_children              false
% 11.83/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.83/2.00  --bmc1_out_stat                         full
% 11.83/2.00  --bmc1_ground_init                      false
% 11.83/2.00  --bmc1_pre_inst_next_state              false
% 11.83/2.00  --bmc1_pre_inst_state                   false
% 11.83/2.00  --bmc1_pre_inst_reach_state             false
% 11.83/2.00  --bmc1_out_unsat_core                   false
% 11.83/2.00  --bmc1_aig_witness_out                  false
% 11.83/2.00  --bmc1_verbose                          false
% 11.83/2.00  --bmc1_dump_clauses_tptp                false
% 11.83/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.83/2.00  --bmc1_dump_file                        -
% 11.83/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.83/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.83/2.00  --bmc1_ucm_extend_mode                  1
% 11.83/2.00  --bmc1_ucm_init_mode                    2
% 11.83/2.00  --bmc1_ucm_cone_mode                    none
% 11.83/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.83/2.00  --bmc1_ucm_relax_model                  4
% 11.83/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.83/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.83/2.00  --bmc1_ucm_layered_model                none
% 11.83/2.00  --bmc1_ucm_max_lemma_size               10
% 11.83/2.00  
% 11.83/2.00  ------ AIG Options
% 11.83/2.00  
% 11.83/2.00  --aig_mode                              false
% 11.83/2.00  
% 11.83/2.00  ------ Instantiation Options
% 11.83/2.00  
% 11.83/2.00  --instantiation_flag                    true
% 11.83/2.00  --inst_sos_flag                         true
% 11.83/2.00  --inst_sos_phase                        true
% 11.83/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel_side                     none
% 11.83/2.00  --inst_solver_per_active                1400
% 11.83/2.00  --inst_solver_calls_frac                1.
% 11.83/2.00  --inst_passive_queue_type               priority_queues
% 11.83/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.83/2.00  --inst_passive_queues_freq              [25;2]
% 11.83/2.00  --inst_dismatching                      true
% 11.83/2.00  --inst_eager_unprocessed_to_passive     true
% 11.83/2.00  --inst_prop_sim_given                   true
% 11.83/2.00  --inst_prop_sim_new                     false
% 11.83/2.00  --inst_subs_new                         false
% 11.83/2.00  --inst_eq_res_simp                      false
% 11.83/2.00  --inst_subs_given                       false
% 11.83/2.00  --inst_orphan_elimination               true
% 11.83/2.00  --inst_learning_loop_flag               true
% 11.83/2.00  --inst_learning_start                   3000
% 11.83/2.00  --inst_learning_factor                  2
% 11.83/2.00  --inst_start_prop_sim_after_learn       3
% 11.83/2.00  --inst_sel_renew                        solver
% 11.83/2.00  --inst_lit_activity_flag                true
% 11.83/2.00  --inst_restr_to_given                   false
% 11.83/2.00  --inst_activity_threshold               500
% 11.83/2.00  --inst_out_proof                        true
% 11.83/2.00  
% 11.83/2.00  ------ Resolution Options
% 11.83/2.00  
% 11.83/2.00  --resolution_flag                       false
% 11.83/2.00  --res_lit_sel                           adaptive
% 11.83/2.00  --res_lit_sel_side                      none
% 11.83/2.00  --res_ordering                          kbo
% 11.83/2.00  --res_to_prop_solver                    active
% 11.83/2.00  --res_prop_simpl_new                    false
% 11.83/2.00  --res_prop_simpl_given                  true
% 11.83/2.00  --res_passive_queue_type                priority_queues
% 11.83/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.83/2.00  --res_passive_queues_freq               [15;5]
% 11.83/2.00  --res_forward_subs                      full
% 11.83/2.00  --res_backward_subs                     full
% 11.83/2.00  --res_forward_subs_resolution           true
% 11.83/2.00  --res_backward_subs_resolution          true
% 11.83/2.00  --res_orphan_elimination                true
% 11.83/2.00  --res_time_limit                        2.
% 11.83/2.00  --res_out_proof                         true
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Options
% 11.83/2.00  
% 11.83/2.00  --superposition_flag                    true
% 11.83/2.00  --sup_passive_queue_type                priority_queues
% 11.83/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.83/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.83/2.00  --demod_completeness_check              fast
% 11.83/2.00  --demod_use_ground                      true
% 11.83/2.00  --sup_to_prop_solver                    passive
% 11.83/2.00  --sup_prop_simpl_new                    true
% 11.83/2.00  --sup_prop_simpl_given                  true
% 11.83/2.00  --sup_fun_splitting                     true
% 11.83/2.00  --sup_smt_interval                      50000
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Simplification Setup
% 11.83/2.00  
% 11.83/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.83/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.83/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.83/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.83/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.83/2.00  --sup_immed_triv                        [TrivRules]
% 11.83/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_bw_main                     []
% 11.83/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.83/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.83/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_input_bw                          []
% 11.83/2.00  
% 11.83/2.00  ------ Combination Options
% 11.83/2.00  
% 11.83/2.00  --comb_res_mult                         3
% 11.83/2.00  --comb_sup_mult                         2
% 11.83/2.00  --comb_inst_mult                        10
% 11.83/2.00  
% 11.83/2.00  ------ Debug Options
% 11.83/2.00  
% 11.83/2.00  --dbg_backtrace                         false
% 11.83/2.00  --dbg_dump_prop_clauses                 false
% 11.83/2.00  --dbg_dump_prop_clauses_file            -
% 11.83/2.00  --dbg_out_stat                          false
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  ------ Proving...
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  % SZS status Theorem for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  fof(f2,axiom,(
% 11.83/2.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f14,plain,(
% 11.83/2.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.83/2.00    inference(rectify,[],[f2])).
% 11.83/2.00  
% 11.83/2.00  fof(f24,plain,(
% 11.83/2.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.83/2.00    inference(cnf_transformation,[],[f14])).
% 11.83/2.00  
% 11.83/2.00  fof(f5,axiom,(
% 11.83/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f27,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f5])).
% 11.83/2.00  
% 11.83/2.00  fof(f39,plain,(
% 11.83/2.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 11.83/2.00    inference(definition_unfolding,[],[f24,f27])).
% 11.83/2.00  
% 11.83/2.00  fof(f7,axiom,(
% 11.83/2.00    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f29,plain,(
% 11.83/2.00    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f7])).
% 11.83/2.00  
% 11.83/2.00  fof(f9,axiom,(
% 11.83/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f31,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f9])).
% 11.83/2.00  
% 11.83/2.00  fof(f11,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f18,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.83/2.00    inference(ennf_transformation,[],[f11])).
% 11.83/2.00  
% 11.83/2.00  fof(f33,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f18])).
% 11.83/2.00  
% 11.83/2.00  fof(f41,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.83/2.00    inference(definition_unfolding,[],[f33,f27])).
% 11.83/2.00  
% 11.83/2.00  fof(f12,conjecture,(
% 11.83/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f13,negated_conjecture,(
% 11.83/2.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 11.83/2.00    inference(negated_conjecture,[],[f12])).
% 11.83/2.00  
% 11.83/2.00  fof(f19,plain,(
% 11.83/2.00    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.83/2.00    inference(ennf_transformation,[],[f13])).
% 11.83/2.00  
% 11.83/2.00  fof(f21,plain,(
% 11.83/2.00    ( ! [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k7_subset_1(X0,X1,sK2) != k9_subset_1(X0,X1,k3_subset_1(X0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f20,plain,(
% 11.83/2.00    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f22,plain,(
% 11.83/2.00    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 11.83/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).
% 11.83/2.00  
% 11.83/2.00  fof(f35,plain,(
% 11.83/2.00    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 11.83/2.00    inference(cnf_transformation,[],[f22])).
% 11.83/2.00  
% 11.83/2.00  fof(f1,axiom,(
% 11.83/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f23,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f1])).
% 11.83/2.00  
% 11.83/2.00  fof(f38,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.83/2.00    inference(definition_unfolding,[],[f23,f27,f27])).
% 11.83/2.00  
% 11.83/2.00  fof(f3,axiom,(
% 11.83/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f25,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f3])).
% 11.83/2.00  
% 11.83/2.00  fof(f37,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.83/2.00    inference(definition_unfolding,[],[f25,f27])).
% 11.83/2.00  
% 11.83/2.00  fof(f6,axiom,(
% 11.83/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f15,plain,(
% 11.83/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.83/2.00    inference(ennf_transformation,[],[f6])).
% 11.83/2.00  
% 11.83/2.00  fof(f28,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f15])).
% 11.83/2.00  
% 11.83/2.00  fof(f34,plain,(
% 11.83/2.00    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 11.83/2.00    inference(cnf_transformation,[],[f22])).
% 11.83/2.00  
% 11.83/2.00  fof(f8,axiom,(
% 11.83/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f16,plain,(
% 11.83/2.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.83/2.00    inference(ennf_transformation,[],[f8])).
% 11.83/2.00  
% 11.83/2.00  fof(f30,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f16])).
% 11.83/2.00  
% 11.83/2.00  fof(f4,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f26,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f4])).
% 11.83/2.00  
% 11.83/2.00  fof(f40,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 11.83/2.00    inference(definition_unfolding,[],[f26,f27,f27,f27])).
% 11.83/2.00  
% 11.83/2.00  fof(f10,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f17,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.83/2.00    inference(ennf_transformation,[],[f10])).
% 11.83/2.00  
% 11.83/2.00  fof(f32,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f17])).
% 11.83/2.00  
% 11.83/2.00  fof(f36,plain,(
% 11.83/2.00    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 11.83/2.00    inference(cnf_transformation,[],[f22])).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2,plain,
% 11.83/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5,plain,
% 11.83/2.00      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f29]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_367,plain,
% 11.83/2.00      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7,plain,
% 11.83/2.00      ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f31]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_369,plain,
% 11.83/2.00      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_367,c_7]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_494,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2,c_369]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/2.00      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_364,plain,
% 11.83/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 11.83/2.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_599,plain,
% 11.83/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_494,c_364]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_11,negated_conjecture,
% 11.83/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f35]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_363,plain,
% 11.83/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_596,plain,
% 11.83/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(sK0,X0,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_363,c_364]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1,plain,
% 11.83/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_750,plain,
% 11.83/2.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = k9_subset_1(sK0,X0,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_596,c_1]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1731,plain,
% 11.83/2.00      ( k9_subset_1(X0,sK2,X0) = k9_subset_1(sK0,X0,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_599,c_750]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_0,plain,
% 11.83/2.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f37]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_745,plain,
% 11.83/2.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k9_subset_1(sK0,X0,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_596,c_0]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_756,plain,
% 11.83/2.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k9_subset_1(sK0,X0,sK2))) = k9_subset_1(sK0,X0,sK2) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_745,c_596]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2689,plain,
% 11.83/2.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k9_subset_1(X0,sK2,X0))) = k9_subset_1(sK0,X0,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1731,c_756]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/2.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f28]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_368,plain,
% 11.83/2.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.83/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4223,plain,
% 11.83/2.00      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_369,c_368]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1720,plain,
% 11.83/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X0,X1,X0) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_599,c_1]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4234,plain,
% 11.83/2.00      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X0,X1,X0) ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_4223,c_1720]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_12,negated_conjecture,
% 11.83/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f34]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_362,plain,
% 11.83/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/2.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f30]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_366,plain,
% 11.83/2.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 11.83/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4144,plain,
% 11.83/2.00      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_362,c_366]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4222,plain,
% 11.83/2.00      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_362,c_368]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4317,plain,
% 11.83/2.00      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_4144,c_4144,c_4222]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_25564,plain,
% 11.83/2.00      ( k9_subset_1(sK0,sK1,sK0) = sK1 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_4234,c_4317]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_598,plain,
% 11.83/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k9_subset_1(X1,X0,k4_xboole_0(X1,X2)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_369,c_364]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3,plain,
% 11.83/2.00      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1121,plain,
% 11.83/2.00      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k9_subset_1(X1,X3,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,X3),k4_xboole_0(k5_xboole_0(X0,X3),k4_xboole_0(X1,X2))) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_598,c_3]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_13358,plain,
% 11.83/2.00      ( k5_xboole_0(k9_subset_1(X0,k4_xboole_0(X1,X2),X0),k9_subset_1(X1,X3,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,X3),k4_xboole_0(k5_xboole_0(X0,X3),k4_xboole_0(X1,X2))) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_1121,c_1720]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_13412,plain,
% 11.83/2.00      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X2)))) = k5_xboole_0(k9_subset_1(X0,X2,X0),k9_subset_1(X2,X1,X2)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2,c_13358]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_13738,plain,
% 11.83/2.00      ( k5_xboole_0(k9_subset_1(X0,X1,X0),k9_subset_1(X1,X2,X1)) = k9_subset_1(k5_xboole_0(X0,X2),X1,k5_xboole_0(X0,X2)) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_13412,c_2,c_1720]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26286,plain,
% 11.83/2.00      ( k9_subset_1(k5_xboole_0(sK0,X0),sK1,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK1,k9_subset_1(sK1,X0,sK1)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_25564,c_13738]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_597,plain,
% 11.83/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k9_subset_1(sK0,X0,sK1) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_362,c_364]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_809,plain,
% 11.83/2.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k9_subset_1(sK0,X0,sK1) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_597,c_1]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1288,plain,
% 11.83/2.00      ( k5_xboole_0(sK1,k9_subset_1(sK0,X0,sK1)) = k4_xboole_0(sK1,X0) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_809,c_0]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1727,plain,
% 11.83/2.00      ( k9_subset_1(sK1,X0,sK1) = k9_subset_1(sK0,X0,sK1) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_599,c_597]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26314,plain,
% 11.83/2.00      ( k9_subset_1(k5_xboole_0(sK0,X0),sK1,k5_xboole_0(sK0,X0)) = k4_xboole_0(sK1,X0) ),
% 11.83/2.00      inference(light_normalisation,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_26286,c_1288,c_1727]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30648,plain,
% 11.83/2.00      ( k9_subset_1(k9_subset_1(sK0,sK0,sK2),sK1,k9_subset_1(sK0,sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK0))) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2689,c_26314]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4143,plain,
% 11.83/2.00      ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_363,c_366]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4221,plain,
% 11.83/2.00      ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_363,c_368]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4246,plain,
% 11.83/2.00      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_4143,c_4143,c_4221]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_25563,plain,
% 11.83/2.00      ( k9_subset_1(sK0,sK2,sK0) = sK2 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_4234,c_4246]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26090,plain,
% 11.83/2.00      ( k9_subset_1(sK0,sK0,sK2) = sK2 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_25563,c_1731]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30706,plain,
% 11.83/2.00      ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k9_subset_1(sK2,sK1,sK2) ),
% 11.83/2.00      inference(light_normalisation,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_30648,c_25563,c_26090]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1726,plain,
% 11.83/2.00      ( k9_subset_1(sK2,X0,sK2) = k9_subset_1(sK0,X0,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_599,c_596]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30707,plain,
% 11.83/2.00      ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,sK1,sK2) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_30706,c_1726]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30792,plain,
% 11.83/2.00      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_30707,c_598]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30797,plain,
% 11.83/2.00      ( k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_30707,c_809]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1071,plain,
% 11.83/2.00      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k9_subset_1(sK0,X1,sK2)) = k4_xboole_0(k5_xboole_0(X0,sK2),k4_xboole_0(k5_xboole_0(X0,sK2),X1)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_750,c_3]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_8870,plain,
% 11.83/2.00      ( k5_xboole_0(k9_subset_1(X0,X1,X0),k9_subset_1(sK0,X1,sK2)) = k4_xboole_0(k5_xboole_0(X0,sK2),k4_xboole_0(k5_xboole_0(X0,sK2),X1)) ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_1071,c_1071,c_1720]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_8871,plain,
% 11.83/2.00      ( k5_xboole_0(k9_subset_1(X0,X1,X0),k9_subset_1(sK0,X1,sK2)) = k9_subset_1(k5_xboole_0(X0,sK2),X1,k5_xboole_0(X0,sK2)) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_8870,c_1720]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26289,plain,
% 11.83/2.00      ( k9_subset_1(k5_xboole_0(sK0,sK2),sK1,k5_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_25564,c_8871]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2316,plain,
% 11.83/2.00      ( k5_xboole_0(X0,k9_subset_1(X0,X1,X0)) = k4_xboole_0(X0,X1) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_1720,c_0]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26081,plain,
% 11.83/2.00      ( k5_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_25563,c_2316]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26309,plain,
% 11.83/2.00      ( k9_subset_1(k4_xboole_0(sK0,sK2),sK1,k4_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_26289,c_26081]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_749,plain,
% 11.83/2.00      ( k5_xboole_0(X0,k9_subset_1(sK0,X0,sK2)) = k4_xboole_0(X0,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_596,c_0]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1729,plain,
% 11.83/2.00      ( k9_subset_1(k4_xboole_0(X0,X1),X2,k4_xboole_0(X0,X1)) = k9_subset_1(X0,X2,k4_xboole_0(X0,X1)) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_599,c_598]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26310,plain,
% 11.83/2.00      ( k9_subset_1(k4_xboole_0(sK0,sK2),sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_26309,c_749,c_1729]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1733,plain,
% 11.83/2.00      ( k9_subset_1(X0,sK1,X0) = k9_subset_1(sK0,X0,sK1) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_599,c_809]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30366,plain,
% 11.83/2.00      ( k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK1,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_26310,c_1733]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30808,plain,
% 11.83/2.00      ( k4_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) = k4_xboole_0(sK1,sK2) ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_30797,c_30366]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30818,plain,
% 11.83/2.00      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_30792,c_30808]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_8,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/2.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.83/2.00      inference(cnf_transformation,[],[f32]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_365,plain,
% 11.83/2.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 11.83/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4793,plain,
% 11.83/2.00      ( k7_subset_1(sK0,sK1,X0) = k4_xboole_0(sK1,X0) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_362,c_365]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_10,negated_conjecture,
% 11.83/2.00      ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f36]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4318,plain,
% 11.83/2.00      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k7_subset_1(sK0,sK1,sK2) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_4221,c_10]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5156,plain,
% 11.83/2.00      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_4793,c_4318]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(contradiction,plain,
% 11.83/2.00      ( $false ),
% 11.83/2.00      inference(minisat,[status(thm)],[c_30818,c_5156]) ).
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  ------                               Statistics
% 11.83/2.00  
% 11.83/2.00  ------ General
% 11.83/2.00  
% 11.83/2.00  abstr_ref_over_cycles:                  0
% 11.83/2.00  abstr_ref_under_cycles:                 0
% 11.83/2.00  gc_basic_clause_elim:                   0
% 11.83/2.00  forced_gc_time:                         0
% 11.83/2.00  parsing_time:                           0.008
% 11.83/2.00  unif_index_cands_time:                  0.
% 11.83/2.00  unif_index_add_time:                    0.
% 11.83/2.00  orderings_time:                         0.
% 11.83/2.00  out_proof_time:                         0.008
% 11.83/2.00  total_time:                             1.366
% 11.83/2.00  num_of_symbols:                         42
% 11.83/2.00  num_of_terms:                           64079
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing
% 11.83/2.00  
% 11.83/2.00  num_of_splits:                          0
% 11.83/2.00  num_of_split_atoms:                     0
% 11.83/2.00  num_of_reused_defs:                     0
% 11.83/2.00  num_eq_ax_congr_red:                    4
% 11.83/2.00  num_of_sem_filtered_clauses:            1
% 11.83/2.00  num_of_subtypes:                        0
% 11.83/2.00  monotx_restored_types:                  0
% 11.83/2.00  sat_num_of_epr_types:                   0
% 11.83/2.00  sat_num_of_non_cyclic_types:            0
% 11.83/2.00  sat_guarded_non_collapsed_types:        0
% 11.83/2.00  num_pure_diseq_elim:                    0
% 11.83/2.00  simp_replaced_by:                       0
% 11.83/2.00  res_preprocessed:                       58
% 11.83/2.00  prep_upred:                             0
% 11.83/2.00  prep_unflattend:                        12
% 11.83/2.00  smt_new_axioms:                         0
% 11.83/2.00  pred_elim_cands:                        1
% 11.83/2.00  pred_elim:                              0
% 11.83/2.00  pred_elim_cl:                           0
% 11.83/2.00  pred_elim_cycles:                       1
% 11.83/2.00  merged_defs:                            0
% 11.83/2.00  merged_defs_ncl:                        0
% 11.83/2.00  bin_hyper_res:                          0
% 11.83/2.00  prep_cycles:                            3
% 11.83/2.00  pred_elim_time:                         0.001
% 11.83/2.00  splitting_time:                         0.
% 11.83/2.00  sem_filter_time:                        0.
% 11.83/2.00  monotx_time:                            0.
% 11.83/2.00  subtype_inf_time:                       0.
% 11.83/2.00  
% 11.83/2.00  ------ Problem properties
% 11.83/2.00  
% 11.83/2.00  clauses:                                13
% 11.83/2.00  conjectures:                            3
% 11.83/2.00  epr:                                    0
% 11.83/2.00  horn:                                   13
% 11.83/2.00  ground:                                 3
% 11.83/2.00  unary:                                  9
% 11.83/2.00  binary:                                 4
% 11.83/2.00  lits:                                   17
% 11.83/2.00  lits_eq:                                10
% 11.83/2.00  fd_pure:                                0
% 11.83/2.00  fd_pseudo:                              0
% 11.83/2.00  fd_cond:                                0
% 11.83/2.00  fd_pseudo_cond:                         0
% 11.83/2.00  ac_symbols:                             0
% 11.83/2.00  
% 11.83/2.00  ------ Propositional Solver
% 11.83/2.00  
% 11.83/2.00  prop_solver_calls:                      32
% 11.83/2.00  prop_fast_solver_calls:                 520
% 11.83/2.00  smt_solver_calls:                       0
% 11.83/2.00  smt_fast_solver_calls:                  0
% 11.83/2.00  prop_num_of_clauses:                    13266
% 11.83/2.00  prop_preprocess_simplified:             13091
% 11.83/2.00  prop_fo_subsumed:                       0
% 11.83/2.00  prop_solver_time:                       0.
% 11.83/2.00  smt_solver_time:                        0.
% 11.83/2.00  smt_fast_solver_time:                   0.
% 11.83/2.00  prop_fast_solver_time:                  0.
% 11.83/2.00  prop_unsat_core_time:                   0.001
% 11.83/2.00  
% 11.83/2.00  ------ QBF
% 11.83/2.00  
% 11.83/2.00  qbf_q_res:                              0
% 11.83/2.00  qbf_num_tautologies:                    0
% 11.83/2.00  qbf_prep_cycles:                        0
% 11.83/2.00  
% 11.83/2.00  ------ BMC1
% 11.83/2.00  
% 11.83/2.00  bmc1_current_bound:                     -1
% 11.83/2.00  bmc1_last_solved_bound:                 -1
% 11.83/2.00  bmc1_unsat_core_size:                   -1
% 11.83/2.00  bmc1_unsat_core_parents_size:           -1
% 11.83/2.00  bmc1_merge_next_fun:                    0
% 11.83/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.83/2.00  
% 11.83/2.00  ------ Instantiation
% 11.83/2.00  
% 11.83/2.00  inst_num_of_clauses:                    3401
% 11.83/2.00  inst_num_in_passive:                    2295
% 11.83/2.00  inst_num_in_active:                     1106
% 11.83/2.00  inst_num_in_unprocessed:                0
% 11.83/2.00  inst_num_of_loops:                      1160
% 11.83/2.00  inst_num_of_learning_restarts:          0
% 11.83/2.00  inst_num_moves_active_passive:          48
% 11.83/2.00  inst_lit_activity:                      0
% 11.83/2.00  inst_lit_activity_moves:                0
% 11.83/2.00  inst_num_tautologies:                   0
% 11.83/2.00  inst_num_prop_implied:                  0
% 11.83/2.00  inst_num_existing_simplified:           0
% 11.83/2.00  inst_num_eq_res_simplified:             0
% 11.83/2.00  inst_num_child_elim:                    0
% 11.83/2.00  inst_num_of_dismatching_blockings:      930
% 11.83/2.00  inst_num_of_non_proper_insts:           3793
% 11.83/2.00  inst_num_of_duplicates:                 0
% 11.83/2.00  inst_inst_num_from_inst_to_res:         0
% 11.83/2.00  inst_dismatching_checking_time:         0.
% 11.83/2.00  
% 11.83/2.00  ------ Resolution
% 11.83/2.00  
% 11.83/2.00  res_num_of_clauses:                     0
% 11.83/2.00  res_num_in_passive:                     0
% 11.83/2.00  res_num_in_active:                      0
% 11.83/2.00  res_num_of_loops:                       61
% 11.83/2.00  res_forward_subset_subsumed:            814
% 11.83/2.00  res_backward_subset_subsumed:           0
% 11.83/2.00  res_forward_subsumed:                   0
% 11.83/2.00  res_backward_subsumed:                  0
% 11.83/2.00  res_forward_subsumption_resolution:     0
% 11.83/2.00  res_backward_subsumption_resolution:    0
% 11.83/2.00  res_clause_to_clause_subsumption:       31446
% 11.83/2.00  res_orphan_elimination:                 0
% 11.83/2.00  res_tautology_del:                      364
% 11.83/2.00  res_num_eq_res_simplified:              0
% 11.83/2.00  res_num_sel_changes:                    0
% 11.83/2.00  res_moves_from_active_to_pass:          0
% 11.83/2.00  
% 11.83/2.00  ------ Superposition
% 11.83/2.00  
% 11.83/2.00  sup_time_total:                         0.
% 11.83/2.00  sup_time_generating:                    0.
% 11.83/2.00  sup_time_sim_full:                      0.
% 11.83/2.00  sup_time_sim_immed:                     0.
% 11.83/2.00  
% 11.83/2.00  sup_num_of_clauses:                     3916
% 11.83/2.00  sup_num_in_active:                      208
% 11.83/2.00  sup_num_in_passive:                     3708
% 11.83/2.00  sup_num_of_loops:                       231
% 11.83/2.00  sup_fw_superposition:                   4447
% 11.83/2.00  sup_bw_superposition:                   4278
% 11.83/2.00  sup_immediate_simplified:               4767
% 11.83/2.00  sup_given_eliminated:                   1
% 11.83/2.00  comparisons_done:                       0
% 11.83/2.00  comparisons_avoided:                    0
% 11.83/2.00  
% 11.83/2.00  ------ Simplifications
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  sim_fw_subset_subsumed:                 0
% 11.83/2.00  sim_bw_subset_subsumed:                 0
% 11.83/2.00  sim_fw_subsumed:                        563
% 11.83/2.00  sim_bw_subsumed:                        48
% 11.83/2.00  sim_fw_subsumption_res:                 0
% 11.83/2.00  sim_bw_subsumption_res:                 0
% 11.83/2.00  sim_tautology_del:                      0
% 11.83/2.00  sim_eq_tautology_del:                   566
% 11.83/2.00  sim_eq_res_simp:                        0
% 11.83/2.00  sim_fw_demodulated:                     3336
% 11.83/2.00  sim_bw_demodulated:                     134
% 11.83/2.00  sim_light_normalised:                   1712
% 11.83/2.00  sim_joinable_taut:                      0
% 11.83/2.00  sim_joinable_simp:                      0
% 11.83/2.00  sim_ac_normalised:                      0
% 11.83/2.00  sim_smt_subsumption:                    0
% 11.83/2.00  
%------------------------------------------------------------------------------
