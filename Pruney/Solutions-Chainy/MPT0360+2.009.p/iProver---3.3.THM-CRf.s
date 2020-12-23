%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:15 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 158 expanded)
%              Number of clauses        :   51 (  61 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   18
%              Number of atoms          :  176 ( 320 expanded)
%              Number of equality atoms :  100 ( 168 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK2
      & r1_tarski(sK2,k3_subset_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_xboole_0 != sK2
    & r1_tarski(sK2,k3_subset_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f33])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f61,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9068,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1338,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1343,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2456,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_1343])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_466,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_467,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_1482,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_467])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1337,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1500,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1482,c_1337])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1342,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2897,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_1500,c_1342])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3657,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_2897,c_0])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1818,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1828,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1818,c_8])).

cnf(c_1820,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1822,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1820,c_7])).

cnf(c_1829,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1828,c_1822])).

cnf(c_3695,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3657,c_1829])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1341,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5116,plain,
    ( r1_xboole_0(X0,k5_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3695,c_1341])).

cnf(c_5119,plain,
    ( r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5116,c_8])).

cnf(c_6113,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2456,c_5119])).

cnf(c_6124,plain,
    ( r1_xboole_0(sK3,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6113])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3635,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_959,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2779,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(c_2780,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2779])).

cnf(c_1472,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(c_2063,plain,
    ( sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_1505,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(c_1702,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1505])).

cnf(c_1947,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != sK2
    | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1702])).

cnf(c_958,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1529,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_975,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_373,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_374,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9068,c_6124,c_3635,c_2780,c_2063,c_1947,c_1529,c_975,c_374,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.36/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/1.00  
% 3.36/1.00  ------  iProver source info
% 3.36/1.00  
% 3.36/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.36/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/1.00  git: non_committed_changes: false
% 3.36/1.00  git: last_make_outside_of_git: false
% 3.36/1.00  
% 3.36/1.00  ------ 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options
% 3.36/1.00  
% 3.36/1.00  --out_options                           all
% 3.36/1.00  --tptp_safe_out                         true
% 3.36/1.00  --problem_path                          ""
% 3.36/1.00  --include_path                          ""
% 3.36/1.00  --clausifier                            res/vclausify_rel
% 3.36/1.00  --clausifier_options                    --mode clausify
% 3.36/1.00  --stdin                                 false
% 3.36/1.00  --stats_out                             all
% 3.36/1.00  
% 3.36/1.00  ------ General Options
% 3.36/1.00  
% 3.36/1.00  --fof                                   false
% 3.36/1.00  --time_out_real                         305.
% 3.36/1.00  --time_out_virtual                      -1.
% 3.36/1.00  --symbol_type_check                     false
% 3.36/1.00  --clausify_out                          false
% 3.36/1.00  --sig_cnt_out                           false
% 3.36/1.00  --trig_cnt_out                          false
% 3.36/1.00  --trig_cnt_out_tolerance                1.
% 3.36/1.00  --trig_cnt_out_sk_spl                   false
% 3.36/1.00  --abstr_cl_out                          false
% 3.36/1.00  
% 3.36/1.00  ------ Global Options
% 3.36/1.00  
% 3.36/1.00  --schedule                              default
% 3.36/1.00  --add_important_lit                     false
% 3.36/1.00  --prop_solver_per_cl                    1000
% 3.36/1.00  --min_unsat_core                        false
% 3.36/1.00  --soft_assumptions                      false
% 3.36/1.00  --soft_lemma_size                       3
% 3.36/1.00  --prop_impl_unit_size                   0
% 3.36/1.00  --prop_impl_unit                        []
% 3.36/1.00  --share_sel_clauses                     true
% 3.36/1.00  --reset_solvers                         false
% 3.36/1.00  --bc_imp_inh                            [conj_cone]
% 3.36/1.00  --conj_cone_tolerance                   3.
% 3.36/1.00  --extra_neg_conj                        none
% 3.36/1.00  --large_theory_mode                     true
% 3.36/1.00  --prolific_symb_bound                   200
% 3.36/1.00  --lt_threshold                          2000
% 3.36/1.00  --clause_weak_htbl                      true
% 3.36/1.00  --gc_record_bc_elim                     false
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing Options
% 3.36/1.00  
% 3.36/1.00  --preprocessing_flag                    true
% 3.36/1.00  --time_out_prep_mult                    0.1
% 3.36/1.00  --splitting_mode                        input
% 3.36/1.00  --splitting_grd                         true
% 3.36/1.00  --splitting_cvd                         false
% 3.36/1.00  --splitting_cvd_svl                     false
% 3.36/1.00  --splitting_nvd                         32
% 3.36/1.00  --sub_typing                            true
% 3.36/1.00  --prep_gs_sim                           true
% 3.36/1.00  --prep_unflatten                        true
% 3.36/1.00  --prep_res_sim                          true
% 3.36/1.00  --prep_upred                            true
% 3.36/1.00  --prep_sem_filter                       exhaustive
% 3.36/1.00  --prep_sem_filter_out                   false
% 3.36/1.00  --pred_elim                             true
% 3.36/1.00  --res_sim_input                         true
% 3.36/1.00  --eq_ax_congr_red                       true
% 3.36/1.00  --pure_diseq_elim                       true
% 3.36/1.00  --brand_transform                       false
% 3.36/1.00  --non_eq_to_eq                          false
% 3.36/1.00  --prep_def_merge                        true
% 3.36/1.00  --prep_def_merge_prop_impl              false
% 3.36/1.00  --prep_def_merge_mbd                    true
% 3.36/1.00  --prep_def_merge_tr_red                 false
% 3.36/1.00  --prep_def_merge_tr_cl                  false
% 3.36/1.00  --smt_preprocessing                     true
% 3.36/1.00  --smt_ac_axioms                         fast
% 3.36/1.00  --preprocessed_out                      false
% 3.36/1.00  --preprocessed_stats                    false
% 3.36/1.00  
% 3.36/1.00  ------ Abstraction refinement Options
% 3.36/1.00  
% 3.36/1.00  --abstr_ref                             []
% 3.36/1.00  --abstr_ref_prep                        false
% 3.36/1.00  --abstr_ref_until_sat                   false
% 3.36/1.00  --abstr_ref_sig_restrict                funpre
% 3.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.00  --abstr_ref_under                       []
% 3.36/1.00  
% 3.36/1.00  ------ SAT Options
% 3.36/1.00  
% 3.36/1.00  --sat_mode                              false
% 3.36/1.00  --sat_fm_restart_options                ""
% 3.36/1.00  --sat_gr_def                            false
% 3.36/1.00  --sat_epr_types                         true
% 3.36/1.00  --sat_non_cyclic_types                  false
% 3.36/1.00  --sat_finite_models                     false
% 3.36/1.00  --sat_fm_lemmas                         false
% 3.36/1.00  --sat_fm_prep                           false
% 3.36/1.00  --sat_fm_uc_incr                        true
% 3.36/1.00  --sat_out_model                         small
% 3.36/1.00  --sat_out_clauses                       false
% 3.36/1.00  
% 3.36/1.00  ------ QBF Options
% 3.36/1.00  
% 3.36/1.00  --qbf_mode                              false
% 3.36/1.00  --qbf_elim_univ                         false
% 3.36/1.00  --qbf_dom_inst                          none
% 3.36/1.00  --qbf_dom_pre_inst                      false
% 3.36/1.00  --qbf_sk_in                             false
% 3.36/1.00  --qbf_pred_elim                         true
% 3.36/1.00  --qbf_split                             512
% 3.36/1.00  
% 3.36/1.00  ------ BMC1 Options
% 3.36/1.00  
% 3.36/1.00  --bmc1_incremental                      false
% 3.36/1.00  --bmc1_axioms                           reachable_all
% 3.36/1.00  --bmc1_min_bound                        0
% 3.36/1.00  --bmc1_max_bound                        -1
% 3.36/1.00  --bmc1_max_bound_default                -1
% 3.36/1.00  --bmc1_symbol_reachability              true
% 3.36/1.00  --bmc1_property_lemmas                  false
% 3.36/1.00  --bmc1_k_induction                      false
% 3.36/1.00  --bmc1_non_equiv_states                 false
% 3.36/1.00  --bmc1_deadlock                         false
% 3.36/1.00  --bmc1_ucm                              false
% 3.36/1.00  --bmc1_add_unsat_core                   none
% 3.36/1.00  --bmc1_unsat_core_children              false
% 3.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.00  --bmc1_out_stat                         full
% 3.36/1.00  --bmc1_ground_init                      false
% 3.36/1.00  --bmc1_pre_inst_next_state              false
% 3.36/1.00  --bmc1_pre_inst_state                   false
% 3.36/1.00  --bmc1_pre_inst_reach_state             false
% 3.36/1.00  --bmc1_out_unsat_core                   false
% 3.36/1.00  --bmc1_aig_witness_out                  false
% 3.36/1.00  --bmc1_verbose                          false
% 3.36/1.00  --bmc1_dump_clauses_tptp                false
% 3.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.00  --bmc1_dump_file                        -
% 3.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.00  --bmc1_ucm_extend_mode                  1
% 3.36/1.00  --bmc1_ucm_init_mode                    2
% 3.36/1.00  --bmc1_ucm_cone_mode                    none
% 3.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.00  --bmc1_ucm_relax_model                  4
% 3.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.00  --bmc1_ucm_layered_model                none
% 3.36/1.00  --bmc1_ucm_max_lemma_size               10
% 3.36/1.00  
% 3.36/1.00  ------ AIG Options
% 3.36/1.00  
% 3.36/1.00  --aig_mode                              false
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation Options
% 3.36/1.00  
% 3.36/1.00  --instantiation_flag                    true
% 3.36/1.00  --inst_sos_flag                         false
% 3.36/1.00  --inst_sos_phase                        true
% 3.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel_side                     num_symb
% 3.36/1.00  --inst_solver_per_active                1400
% 3.36/1.00  --inst_solver_calls_frac                1.
% 3.36/1.00  --inst_passive_queue_type               priority_queues
% 3.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.00  --inst_passive_queues_freq              [25;2]
% 3.36/1.00  --inst_dismatching                      true
% 3.36/1.00  --inst_eager_unprocessed_to_passive     true
% 3.36/1.00  --inst_prop_sim_given                   true
% 3.36/1.00  --inst_prop_sim_new                     false
% 3.36/1.00  --inst_subs_new                         false
% 3.36/1.00  --inst_eq_res_simp                      false
% 3.36/1.00  --inst_subs_given                       false
% 3.36/1.00  --inst_orphan_elimination               true
% 3.36/1.00  --inst_learning_loop_flag               true
% 3.36/1.00  --inst_learning_start                   3000
% 3.36/1.00  --inst_learning_factor                  2
% 3.36/1.00  --inst_start_prop_sim_after_learn       3
% 3.36/1.00  --inst_sel_renew                        solver
% 3.36/1.00  --inst_lit_activity_flag                true
% 3.36/1.00  --inst_restr_to_given                   false
% 3.36/1.00  --inst_activity_threshold               500
% 3.36/1.00  --inst_out_proof                        true
% 3.36/1.00  
% 3.36/1.00  ------ Resolution Options
% 3.36/1.00  
% 3.36/1.00  --resolution_flag                       true
% 3.36/1.00  --res_lit_sel                           adaptive
% 3.36/1.00  --res_lit_sel_side                      none
% 3.36/1.00  --res_ordering                          kbo
% 3.36/1.00  --res_to_prop_solver                    active
% 3.36/1.00  --res_prop_simpl_new                    false
% 3.36/1.00  --res_prop_simpl_given                  true
% 3.36/1.00  --res_passive_queue_type                priority_queues
% 3.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.00  --res_passive_queues_freq               [15;5]
% 3.36/1.00  --res_forward_subs                      full
% 3.36/1.00  --res_backward_subs                     full
% 3.36/1.00  --res_forward_subs_resolution           true
% 3.36/1.00  --res_backward_subs_resolution          true
% 3.36/1.00  --res_orphan_elimination                true
% 3.36/1.00  --res_time_limit                        2.
% 3.36/1.00  --res_out_proof                         true
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Options
% 3.36/1.00  
% 3.36/1.00  --superposition_flag                    true
% 3.36/1.00  --sup_passive_queue_type                priority_queues
% 3.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.00  --demod_completeness_check              fast
% 3.36/1.00  --demod_use_ground                      true
% 3.36/1.00  --sup_to_prop_solver                    passive
% 3.36/1.00  --sup_prop_simpl_new                    true
% 3.36/1.00  --sup_prop_simpl_given                  true
% 3.36/1.00  --sup_fun_splitting                     false
% 3.36/1.00  --sup_smt_interval                      50000
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Simplification Setup
% 3.36/1.00  
% 3.36/1.00  --sup_indices_passive                   []
% 3.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_full_bw                           [BwDemod]
% 3.36/1.00  --sup_immed_triv                        [TrivRules]
% 3.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_immed_bw_main                     []
% 3.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  
% 3.36/1.00  ------ Combination Options
% 3.36/1.00  
% 3.36/1.00  --comb_res_mult                         3
% 3.36/1.00  --comb_sup_mult                         2
% 3.36/1.00  --comb_inst_mult                        10
% 3.36/1.00  
% 3.36/1.00  ------ Debug Options
% 3.36/1.00  
% 3.36/1.00  --dbg_backtrace                         false
% 3.36/1.00  --dbg_dump_prop_clauses                 false
% 3.36/1.00  --dbg_dump_prop_clauses_file            -
% 3.36/1.00  --dbg_out_stat                          false
% 3.36/1.00  ------ Parsing...
% 3.36/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/1.00  ------ Proving...
% 3.36/1.00  ------ Problem Properties 
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  clauses                                 22
% 3.36/1.00  conjectures                             3
% 3.36/1.00  EPR                                     3
% 3.36/1.00  Horn                                    21
% 3.36/1.00  unary                                   9
% 3.36/1.00  binary                                  9
% 3.36/1.00  lits                                    39
% 3.36/1.00  lits eq                                 17
% 3.36/1.00  fd_pure                                 0
% 3.36/1.00  fd_pseudo                               0
% 3.36/1.00  fd_cond                                 0
% 3.36/1.00  fd_pseudo_cond                          0
% 3.36/1.00  AC symbols                              0
% 3.36/1.00  
% 3.36/1.00  ------ Schedule dynamic 5 is on 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ 
% 3.36/1.00  Current options:
% 3.36/1.00  ------ 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options
% 3.36/1.00  
% 3.36/1.00  --out_options                           all
% 3.36/1.00  --tptp_safe_out                         true
% 3.36/1.00  --problem_path                          ""
% 3.36/1.00  --include_path                          ""
% 3.36/1.00  --clausifier                            res/vclausify_rel
% 3.36/1.00  --clausifier_options                    --mode clausify
% 3.36/1.00  --stdin                                 false
% 3.36/1.00  --stats_out                             all
% 3.36/1.00  
% 3.36/1.00  ------ General Options
% 3.36/1.00  
% 3.36/1.00  --fof                                   false
% 3.36/1.00  --time_out_real                         305.
% 3.36/1.00  --time_out_virtual                      -1.
% 3.36/1.00  --symbol_type_check                     false
% 3.36/1.00  --clausify_out                          false
% 3.36/1.00  --sig_cnt_out                           false
% 3.36/1.00  --trig_cnt_out                          false
% 3.36/1.00  --trig_cnt_out_tolerance                1.
% 3.36/1.00  --trig_cnt_out_sk_spl                   false
% 3.36/1.00  --abstr_cl_out                          false
% 3.36/1.00  
% 3.36/1.00  ------ Global Options
% 3.36/1.00  
% 3.36/1.00  --schedule                              default
% 3.36/1.00  --add_important_lit                     false
% 3.36/1.00  --prop_solver_per_cl                    1000
% 3.36/1.00  --min_unsat_core                        false
% 3.36/1.00  --soft_assumptions                      false
% 3.36/1.00  --soft_lemma_size                       3
% 3.36/1.00  --prop_impl_unit_size                   0
% 3.36/1.00  --prop_impl_unit                        []
% 3.36/1.00  --share_sel_clauses                     true
% 3.36/1.00  --reset_solvers                         false
% 3.36/1.00  --bc_imp_inh                            [conj_cone]
% 3.36/1.00  --conj_cone_tolerance                   3.
% 3.36/1.00  --extra_neg_conj                        none
% 3.36/1.00  --large_theory_mode                     true
% 3.36/1.00  --prolific_symb_bound                   200
% 3.36/1.00  --lt_threshold                          2000
% 3.36/1.00  --clause_weak_htbl                      true
% 3.36/1.00  --gc_record_bc_elim                     false
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing Options
% 3.36/1.00  
% 3.36/1.00  --preprocessing_flag                    true
% 3.36/1.00  --time_out_prep_mult                    0.1
% 3.36/1.00  --splitting_mode                        input
% 3.36/1.00  --splitting_grd                         true
% 3.36/1.00  --splitting_cvd                         false
% 3.36/1.00  --splitting_cvd_svl                     false
% 3.36/1.00  --splitting_nvd                         32
% 3.36/1.00  --sub_typing                            true
% 3.36/1.00  --prep_gs_sim                           true
% 3.36/1.00  --prep_unflatten                        true
% 3.36/1.00  --prep_res_sim                          true
% 3.36/1.00  --prep_upred                            true
% 3.36/1.00  --prep_sem_filter                       exhaustive
% 3.36/1.00  --prep_sem_filter_out                   false
% 3.36/1.00  --pred_elim                             true
% 3.36/1.00  --res_sim_input                         true
% 3.36/1.00  --eq_ax_congr_red                       true
% 3.36/1.00  --pure_diseq_elim                       true
% 3.36/1.00  --brand_transform                       false
% 3.36/1.00  --non_eq_to_eq                          false
% 3.36/1.00  --prep_def_merge                        true
% 3.36/1.00  --prep_def_merge_prop_impl              false
% 3.36/1.00  --prep_def_merge_mbd                    true
% 3.36/1.00  --prep_def_merge_tr_red                 false
% 3.36/1.00  --prep_def_merge_tr_cl                  false
% 3.36/1.00  --smt_preprocessing                     true
% 3.36/1.00  --smt_ac_axioms                         fast
% 3.36/1.00  --preprocessed_out                      false
% 3.36/1.00  --preprocessed_stats                    false
% 3.36/1.00  
% 3.36/1.00  ------ Abstraction refinement Options
% 3.36/1.00  
% 3.36/1.00  --abstr_ref                             []
% 3.36/1.00  --abstr_ref_prep                        false
% 3.36/1.00  --abstr_ref_until_sat                   false
% 3.36/1.00  --abstr_ref_sig_restrict                funpre
% 3.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.00  --abstr_ref_under                       []
% 3.36/1.00  
% 3.36/1.00  ------ SAT Options
% 3.36/1.00  
% 3.36/1.00  --sat_mode                              false
% 3.36/1.00  --sat_fm_restart_options                ""
% 3.36/1.00  --sat_gr_def                            false
% 3.36/1.00  --sat_epr_types                         true
% 3.36/1.00  --sat_non_cyclic_types                  false
% 3.36/1.00  --sat_finite_models                     false
% 3.36/1.00  --sat_fm_lemmas                         false
% 3.36/1.00  --sat_fm_prep                           false
% 3.36/1.00  --sat_fm_uc_incr                        true
% 3.36/1.00  --sat_out_model                         small
% 3.36/1.00  --sat_out_clauses                       false
% 3.36/1.00  
% 3.36/1.00  ------ QBF Options
% 3.36/1.00  
% 3.36/1.00  --qbf_mode                              false
% 3.36/1.00  --qbf_elim_univ                         false
% 3.36/1.00  --qbf_dom_inst                          none
% 3.36/1.00  --qbf_dom_pre_inst                      false
% 3.36/1.00  --qbf_sk_in                             false
% 3.36/1.00  --qbf_pred_elim                         true
% 3.36/1.00  --qbf_split                             512
% 3.36/1.00  
% 3.36/1.00  ------ BMC1 Options
% 3.36/1.00  
% 3.36/1.00  --bmc1_incremental                      false
% 3.36/1.00  --bmc1_axioms                           reachable_all
% 3.36/1.00  --bmc1_min_bound                        0
% 3.36/1.00  --bmc1_max_bound                        -1
% 3.36/1.00  --bmc1_max_bound_default                -1
% 3.36/1.00  --bmc1_symbol_reachability              true
% 3.36/1.00  --bmc1_property_lemmas                  false
% 3.36/1.00  --bmc1_k_induction                      false
% 3.36/1.00  --bmc1_non_equiv_states                 false
% 3.36/1.00  --bmc1_deadlock                         false
% 3.36/1.00  --bmc1_ucm                              false
% 3.36/1.00  --bmc1_add_unsat_core                   none
% 3.36/1.00  --bmc1_unsat_core_children              false
% 3.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.00  --bmc1_out_stat                         full
% 3.36/1.00  --bmc1_ground_init                      false
% 3.36/1.00  --bmc1_pre_inst_next_state              false
% 3.36/1.00  --bmc1_pre_inst_state                   false
% 3.36/1.00  --bmc1_pre_inst_reach_state             false
% 3.36/1.00  --bmc1_out_unsat_core                   false
% 3.36/1.00  --bmc1_aig_witness_out                  false
% 3.36/1.00  --bmc1_verbose                          false
% 3.36/1.00  --bmc1_dump_clauses_tptp                false
% 3.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.00  --bmc1_dump_file                        -
% 3.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.00  --bmc1_ucm_extend_mode                  1
% 3.36/1.00  --bmc1_ucm_init_mode                    2
% 3.36/1.00  --bmc1_ucm_cone_mode                    none
% 3.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.00  --bmc1_ucm_relax_model                  4
% 3.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.00  --bmc1_ucm_layered_model                none
% 3.36/1.00  --bmc1_ucm_max_lemma_size               10
% 3.36/1.00  
% 3.36/1.00  ------ AIG Options
% 3.36/1.00  
% 3.36/1.00  --aig_mode                              false
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation Options
% 3.36/1.00  
% 3.36/1.00  --instantiation_flag                    true
% 3.36/1.00  --inst_sos_flag                         false
% 3.36/1.00  --inst_sos_phase                        true
% 3.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel_side                     none
% 3.36/1.00  --inst_solver_per_active                1400
% 3.36/1.00  --inst_solver_calls_frac                1.
% 3.36/1.00  --inst_passive_queue_type               priority_queues
% 3.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.00  --inst_passive_queues_freq              [25;2]
% 3.36/1.00  --inst_dismatching                      true
% 3.36/1.00  --inst_eager_unprocessed_to_passive     true
% 3.36/1.00  --inst_prop_sim_given                   true
% 3.36/1.00  --inst_prop_sim_new                     false
% 3.36/1.00  --inst_subs_new                         false
% 3.36/1.00  --inst_eq_res_simp                      false
% 3.36/1.00  --inst_subs_given                       false
% 3.36/1.00  --inst_orphan_elimination               true
% 3.36/1.00  --inst_learning_loop_flag               true
% 3.36/1.00  --inst_learning_start                   3000
% 3.36/1.00  --inst_learning_factor                  2
% 3.36/1.00  --inst_start_prop_sim_after_learn       3
% 3.36/1.00  --inst_sel_renew                        solver
% 3.36/1.00  --inst_lit_activity_flag                true
% 3.36/1.00  --inst_restr_to_given                   false
% 3.36/1.00  --inst_activity_threshold               500
% 3.36/1.00  --inst_out_proof                        true
% 3.36/1.00  
% 3.36/1.00  ------ Resolution Options
% 3.36/1.00  
% 3.36/1.00  --resolution_flag                       false
% 3.36/1.00  --res_lit_sel                           adaptive
% 3.36/1.00  --res_lit_sel_side                      none
% 3.36/1.00  --res_ordering                          kbo
% 3.36/1.00  --res_to_prop_solver                    active
% 3.36/1.00  --res_prop_simpl_new                    false
% 3.36/1.00  --res_prop_simpl_given                  true
% 3.36/1.00  --res_passive_queue_type                priority_queues
% 3.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.00  --res_passive_queues_freq               [15;5]
% 3.36/1.00  --res_forward_subs                      full
% 3.36/1.00  --res_backward_subs                     full
% 3.36/1.00  --res_forward_subs_resolution           true
% 3.36/1.00  --res_backward_subs_resolution          true
% 3.36/1.00  --res_orphan_elimination                true
% 3.36/1.00  --res_time_limit                        2.
% 3.36/1.00  --res_out_proof                         true
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Options
% 3.36/1.00  
% 3.36/1.00  --superposition_flag                    true
% 3.36/1.00  --sup_passive_queue_type                priority_queues
% 3.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.00  --demod_completeness_check              fast
% 3.36/1.00  --demod_use_ground                      true
% 3.36/1.00  --sup_to_prop_solver                    passive
% 3.36/1.00  --sup_prop_simpl_new                    true
% 3.36/1.00  --sup_prop_simpl_given                  true
% 3.36/1.00  --sup_fun_splitting                     false
% 3.36/1.00  --sup_smt_interval                      50000
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Simplification Setup
% 3.36/1.00  
% 3.36/1.00  --sup_indices_passive                   []
% 3.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_full_bw                           [BwDemod]
% 3.36/1.00  --sup_immed_triv                        [TrivRules]
% 3.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_immed_bw_main                     []
% 3.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  
% 3.36/1.00  ------ Combination Options
% 3.36/1.00  
% 3.36/1.00  --comb_res_mult                         3
% 3.36/1.00  --comb_sup_mult                         2
% 3.36/1.00  --comb_inst_mult                        10
% 3.36/1.00  
% 3.36/1.00  ------ Debug Options
% 3.36/1.00  
% 3.36/1.00  --dbg_backtrace                         false
% 3.36/1.00  --dbg_dump_prop_clauses                 false
% 3.36/1.00  --dbg_dump_prop_clauses_file            -
% 3.36/1.00  --dbg_out_stat                          false
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ Proving...
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  % SZS status Theorem for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  fof(f4,axiom,(
% 3.36/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f20,plain,(
% 3.36/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.36/1.00    inference(ennf_transformation,[],[f4])).
% 3.36/1.00  
% 3.36/1.00  fof(f39,plain,(
% 3.36/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f20])).
% 3.36/1.00  
% 3.36/1.00  fof(f11,axiom,(
% 3.36/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f48,plain,(
% 3.36/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f11])).
% 3.36/1.00  
% 3.36/1.00  fof(f15,axiom,(
% 3.36/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f24,plain,(
% 3.36/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.36/1.00    inference(ennf_transformation,[],[f15])).
% 3.36/1.00  
% 3.36/1.00  fof(f58,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f24])).
% 3.36/1.00  
% 3.36/1.00  fof(f17,conjecture,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f18,negated_conjecture,(
% 3.36/1.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 3.36/1.00    inference(negated_conjecture,[],[f17])).
% 3.36/1.00  
% 3.36/1.00  fof(f25,plain,(
% 3.36/1.00    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.36/1.00    inference(ennf_transformation,[],[f18])).
% 3.36/1.00  
% 3.36/1.00  fof(f26,plain,(
% 3.36/1.00    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.36/1.00    inference(flattening,[],[f25])).
% 3.36/1.00  
% 3.36/1.00  fof(f33,plain,(
% 3.36/1.00    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 3.36/1.00    introduced(choice_axiom,[])).
% 3.36/1.00  
% 3.36/1.00  fof(f34,plain,(
% 3.36/1.00    k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f33])).
% 3.36/1.00  
% 3.36/1.00  fof(f60,plain,(
% 3.36/1.00    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.36/1.00    inference(cnf_transformation,[],[f34])).
% 3.36/1.00  
% 3.36/1.00  fof(f62,plain,(
% 3.36/1.00    r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 3.36/1.00    inference(cnf_transformation,[],[f34])).
% 3.36/1.00  
% 3.36/1.00  fof(f6,axiom,(
% 3.36/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f21,plain,(
% 3.36/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.36/1.00    inference(ennf_transformation,[],[f6])).
% 3.36/1.00  
% 3.36/1.00  fof(f41,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f21])).
% 3.36/1.00  
% 3.36/1.00  fof(f8,axiom,(
% 3.36/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f43,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f8])).
% 3.36/1.00  
% 3.36/1.00  fof(f69,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.36/1.00    inference(definition_unfolding,[],[f41,f43])).
% 3.36/1.00  
% 3.36/1.00  fof(f5,axiom,(
% 3.36/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f40,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f5])).
% 3.36/1.00  
% 3.36/1.00  fof(f64,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.36/1.00    inference(definition_unfolding,[],[f40,f43])).
% 3.36/1.00  
% 3.36/1.00  fof(f7,axiom,(
% 3.36/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f42,plain,(
% 3.36/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.36/1.00    inference(cnf_transformation,[],[f7])).
% 3.36/1.00  
% 3.36/1.00  fof(f70,plain,(
% 3.36/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.36/1.00    inference(definition_unfolding,[],[f42,f43])).
% 3.36/1.00  
% 3.36/1.00  fof(f9,axiom,(
% 3.36/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f44,plain,(
% 3.36/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.36/1.00    inference(cnf_transformation,[],[f9])).
% 3.36/1.00  
% 3.36/1.00  fof(f10,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f22,plain,(
% 3.36/1.00    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.36/1.00    inference(ennf_transformation,[],[f10])).
% 3.36/1.00  
% 3.36/1.00  fof(f47,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f22])).
% 3.36/1.01  
% 3.36/1.01  fof(f12,axiom,(
% 3.36/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f49,plain,(
% 3.36/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f12])).
% 3.36/1.01  
% 3.36/1.01  fof(f71,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) | r1_xboole_0(X0,X2)) )),
% 3.36/1.01    inference(definition_unfolding,[],[f47,f49])).
% 3.36/1.01  
% 3.36/1.01  fof(f2,axiom,(
% 3.36/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f27,plain,(
% 3.36/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.36/1.01    inference(nnf_transformation,[],[f2])).
% 3.36/1.01  
% 3.36/1.01  fof(f36,plain,(
% 3.36/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f27])).
% 3.36/1.01  
% 3.36/1.01  fof(f67,plain,(
% 3.36/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.36/1.01    inference(definition_unfolding,[],[f36,f43])).
% 3.36/1.01  
% 3.36/1.01  fof(f61,plain,(
% 3.36/1.01    r1_tarski(sK2,sK3)),
% 3.36/1.01    inference(cnf_transformation,[],[f34])).
% 3.36/1.01  
% 3.36/1.01  fof(f63,plain,(
% 3.36/1.01    k1_xboole_0 != sK2),
% 3.36/1.01    inference(cnf_transformation,[],[f34])).
% 3.36/1.01  
% 3.36/1.01  cnf(c_5,plain,
% 3.36/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.36/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_9068,plain,
% 3.36/1.01      ( ~ r1_xboole_0(sK3,sK2) | r1_xboole_0(sK2,sK3) ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_12,plain,
% 3.36/1.01      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.36/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1338,plain,
% 3.36/1.01      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1343,plain,
% 3.36/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 3.36/1.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2456,plain,
% 3.36/1.01      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_1338,c_1343]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_21,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.36/1.01      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.36/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_26,negated_conjecture,
% 3.36/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.36/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_466,plain,
% 3.36/1.01      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.36/1.01      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.36/1.01      | sK3 != X1 ),
% 3.36/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_467,plain,
% 3.36/1.01      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 3.36/1.01      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.36/1.01      inference(unflattening,[status(thm)],[c_466]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1482,plain,
% 3.36/1.01      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 3.36/1.01      inference(equality_resolution,[status(thm)],[c_467]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_24,negated_conjecture,
% 3.36/1.01      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
% 3.36/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1337,plain,
% 3.36/1.01      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1500,plain,
% 3.36/1.01      ( r1_tarski(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 3.36/1.01      inference(demodulation,[status(thm)],[c_1482,c_1337]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_6,plain,
% 3.36/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.36/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1342,plain,
% 3.36/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.36/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2897,plain,
% 3.36/1.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = sK2 ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_1500,c_1342]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_0,plain,
% 3.36/1.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.36/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3657,plain,
% 3.36/1.01      ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = k5_xboole_0(sK2,sK2) ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_2897,c_0]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_7,plain,
% 3.36/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.36/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1818,plain,
% 3.36/1.01      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_8,plain,
% 3.36/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.36/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1828,plain,
% 3.36/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.36/1.01      inference(light_normalisation,[status(thm)],[c_1818,c_8]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1820,plain,
% 3.36/1.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1822,plain,
% 3.36/1.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.36/1.01      inference(light_normalisation,[status(thm)],[c_1820,c_7]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1829,plain,
% 3.36/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.36/1.01      inference(demodulation,[status(thm)],[c_1828,c_1822]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3695,plain,
% 3.36/1.01      ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 3.36/1.01      inference(demodulation,[status(thm)],[c_3657,c_1829]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_9,plain,
% 3.36/1.01      ( r1_xboole_0(X0,X1)
% 3.36/1.01      | ~ r1_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 3.36/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1341,plain,
% 3.36/1.01      ( r1_xboole_0(X0,X1) = iProver_top
% 3.36/1.01      | r1_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_5116,plain,
% 3.36/1.01      ( r1_xboole_0(X0,k5_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)) != iProver_top
% 3.36/1.01      | r1_xboole_0(X0,sK2) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_3695,c_1341]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_5119,plain,
% 3.36/1.01      ( r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) != iProver_top
% 3.36/1.01      | r1_xboole_0(X0,sK2) = iProver_top ),
% 3.36/1.01      inference(demodulation,[status(thm)],[c_5116,c_8]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_6113,plain,
% 3.36/1.01      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_2456,c_5119]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_6124,plain,
% 3.36/1.01      ( r1_xboole_0(sK3,sK2) ),
% 3.36/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6113]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3,plain,
% 3.36/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.36/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.36/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3635,plain,
% 3.36/1.01      ( ~ r1_xboole_0(sK2,sK3)
% 3.36/1.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_959,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2779,plain,
% 3.36/1.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0
% 3.36/1.01      | k1_xboole_0 != X0
% 3.36/1.01      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_959]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2780,plain,
% 3.36/1.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 3.36/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_2779]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1472,plain,
% 3.36/1.01      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_959]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2063,plain,
% 3.36/1.01      ( sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 3.36/1.01      | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 3.36/1.01      | k1_xboole_0 = sK2 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1472]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1505,plain,
% 3.36/1.01      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_959]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1702,plain,
% 3.36/1.01      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1505]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1947,plain,
% 3.36/1.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != sK2
% 3.36/1.01      | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 3.36/1.01      | sK2 != sK2 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1702]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_958,plain,( X0 = X0 ),theory(equality) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1529,plain,
% 3.36/1.01      ( sK2 = sK2 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_958]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_975,plain,
% 3.36/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_958]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_25,negated_conjecture,
% 3.36/1.01      ( r1_tarski(sK2,sK3) ),
% 3.36/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_373,plain,
% 3.36/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | sK3 != X1 | sK2 != X0 ),
% 3.36/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_374,plain,
% 3.36/1.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 3.36/1.01      inference(unflattening,[status(thm)],[c_373]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_23,negated_conjecture,
% 3.36/1.01      ( k1_xboole_0 != sK2 ),
% 3.36/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(contradiction,plain,
% 3.36/1.01      ( $false ),
% 3.36/1.01      inference(minisat,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_9068,c_6124,c_3635,c_2780,c_2063,c_1947,c_1529,c_975,
% 3.36/1.01                 c_374,c_23]) ).
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/1.01  
% 3.36/1.01  ------                               Statistics
% 3.36/1.01  
% 3.36/1.01  ------ General
% 3.36/1.01  
% 3.36/1.01  abstr_ref_over_cycles:                  0
% 3.36/1.01  abstr_ref_under_cycles:                 0
% 3.36/1.01  gc_basic_clause_elim:                   0
% 3.36/1.01  forced_gc_time:                         0
% 3.36/1.01  parsing_time:                           0.01
% 3.36/1.01  unif_index_cands_time:                  0.
% 3.36/1.01  unif_index_add_time:                    0.
% 3.36/1.01  orderings_time:                         0.
% 3.36/1.01  out_proof_time:                         0.006
% 3.36/1.01  total_time:                             0.264
% 3.36/1.01  num_of_symbols:                         45
% 3.36/1.01  num_of_terms:                           6571
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing
% 3.36/1.01  
% 3.36/1.01  num_of_splits:                          0
% 3.36/1.01  num_of_split_atoms:                     0
% 3.36/1.01  num_of_reused_defs:                     0
% 3.36/1.01  num_eq_ax_congr_red:                    14
% 3.36/1.01  num_of_sem_filtered_clauses:            1
% 3.36/1.01  num_of_subtypes:                        0
% 3.36/1.01  monotx_restored_types:                  0
% 3.36/1.01  sat_num_of_epr_types:                   0
% 3.36/1.01  sat_num_of_non_cyclic_types:            0
% 3.36/1.01  sat_guarded_non_collapsed_types:        0
% 3.36/1.01  num_pure_diseq_elim:                    0
% 3.36/1.01  simp_replaced_by:                       0
% 3.36/1.01  res_preprocessed:                       135
% 3.36/1.01  prep_upred:                             0
% 3.36/1.01  prep_unflattend:                        40
% 3.36/1.01  smt_new_axioms:                         0
% 3.36/1.01  pred_elim_cands:                        2
% 3.36/1.01  pred_elim:                              3
% 3.36/1.01  pred_elim_cl:                           5
% 3.36/1.01  pred_elim_cycles:                       7
% 3.36/1.01  merged_defs:                            14
% 3.36/1.01  merged_defs_ncl:                        0
% 3.36/1.01  bin_hyper_res:                          15
% 3.36/1.01  prep_cycles:                            5
% 3.36/1.01  pred_elim_time:                         0.018
% 3.36/1.01  splitting_time:                         0.
% 3.36/1.01  sem_filter_time:                        0.
% 3.36/1.01  monotx_time:                            0.001
% 3.36/1.01  subtype_inf_time:                       0.
% 3.36/1.01  
% 3.36/1.01  ------ Problem properties
% 3.36/1.01  
% 3.36/1.01  clauses:                                22
% 3.36/1.01  conjectures:                            3
% 3.36/1.01  epr:                                    3
% 3.36/1.01  horn:                                   21
% 3.36/1.01  ground:                                 3
% 3.36/1.01  unary:                                  9
% 3.36/1.01  binary:                                 9
% 3.36/1.01  lits:                                   39
% 3.36/1.01  lits_eq:                                17
% 3.36/1.01  fd_pure:                                0
% 3.36/1.01  fd_pseudo:                              0
% 3.36/1.01  fd_cond:                                0
% 3.36/1.01  fd_pseudo_cond:                         0
% 3.36/1.01  ac_symbols:                             0
% 3.36/1.01  
% 3.36/1.01  ------ Propositional Solver
% 3.36/1.01  
% 3.36/1.01  prop_solver_calls:                      32
% 3.36/1.01  prop_fast_solver_calls:                 691
% 3.36/1.01  smt_solver_calls:                       0
% 3.36/1.01  smt_fast_solver_calls:                  0
% 3.36/1.01  prop_num_of_clauses:                    3188
% 3.36/1.01  prop_preprocess_simplified:             7097
% 3.36/1.01  prop_fo_subsumed:                       1
% 3.36/1.01  prop_solver_time:                       0.
% 3.36/1.01  smt_solver_time:                        0.
% 3.36/1.01  smt_fast_solver_time:                   0.
% 3.36/1.01  prop_fast_solver_time:                  0.
% 3.36/1.01  prop_unsat_core_time:                   0.
% 3.36/1.01  
% 3.36/1.01  ------ QBF
% 3.36/1.01  
% 3.36/1.01  qbf_q_res:                              0
% 3.36/1.01  qbf_num_tautologies:                    0
% 3.36/1.01  qbf_prep_cycles:                        0
% 3.36/1.01  
% 3.36/1.01  ------ BMC1
% 3.36/1.01  
% 3.36/1.01  bmc1_current_bound:                     -1
% 3.36/1.01  bmc1_last_solved_bound:                 -1
% 3.36/1.01  bmc1_unsat_core_size:                   -1
% 3.36/1.01  bmc1_unsat_core_parents_size:           -1
% 3.36/1.01  bmc1_merge_next_fun:                    0
% 3.36/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.36/1.01  
% 3.36/1.01  ------ Instantiation
% 3.36/1.01  
% 3.36/1.01  inst_num_of_clauses:                    1049
% 3.36/1.01  inst_num_in_passive:                    172
% 3.36/1.01  inst_num_in_active:                     404
% 3.36/1.01  inst_num_in_unprocessed:                472
% 3.36/1.01  inst_num_of_loops:                      416
% 3.36/1.01  inst_num_of_learning_restarts:          0
% 3.36/1.01  inst_num_moves_active_passive:          8
% 3.36/1.01  inst_lit_activity:                      0
% 3.36/1.01  inst_lit_activity_moves:                0
% 3.36/1.01  inst_num_tautologies:                   0
% 3.36/1.01  inst_num_prop_implied:                  0
% 3.36/1.01  inst_num_existing_simplified:           0
% 3.36/1.01  inst_num_eq_res_simplified:             0
% 3.36/1.01  inst_num_child_elim:                    0
% 3.36/1.01  inst_num_of_dismatching_blockings:      40
% 3.36/1.01  inst_num_of_non_proper_insts:           600
% 3.36/1.01  inst_num_of_duplicates:                 0
% 3.36/1.01  inst_inst_num_from_inst_to_res:         0
% 3.36/1.01  inst_dismatching_checking_time:         0.
% 3.36/1.01  
% 3.36/1.01  ------ Resolution
% 3.36/1.01  
% 3.36/1.01  res_num_of_clauses:                     0
% 3.36/1.01  res_num_in_passive:                     0
% 3.36/1.01  res_num_in_active:                      0
% 3.36/1.01  res_num_of_loops:                       140
% 3.36/1.01  res_forward_subset_subsumed:            73
% 3.36/1.01  res_backward_subset_subsumed:           0
% 3.36/1.01  res_forward_subsumed:                   2
% 3.36/1.01  res_backward_subsumed:                  0
% 3.36/1.01  res_forward_subsumption_resolution:     2
% 3.36/1.01  res_backward_subsumption_resolution:    0
% 3.36/1.01  res_clause_to_clause_subsumption:       1745
% 3.36/1.01  res_orphan_elimination:                 0
% 3.36/1.01  res_tautology_del:                      94
% 3.36/1.01  res_num_eq_res_simplified:              0
% 3.36/1.01  res_num_sel_changes:                    0
% 3.36/1.01  res_moves_from_active_to_pass:          0
% 3.36/1.01  
% 3.36/1.01  ------ Superposition
% 3.36/1.01  
% 3.36/1.01  sup_time_total:                         0.
% 3.36/1.01  sup_time_generating:                    0.
% 3.36/1.01  sup_time_sim_full:                      0.
% 3.36/1.01  sup_time_sim_immed:                     0.
% 3.36/1.01  
% 3.36/1.01  sup_num_of_clauses:                     201
% 3.36/1.01  sup_num_in_active:                      70
% 3.36/1.01  sup_num_in_passive:                     131
% 3.36/1.01  sup_num_of_loops:                       82
% 3.36/1.01  sup_fw_superposition:                   318
% 3.36/1.01  sup_bw_superposition:                   430
% 3.36/1.01  sup_immediate_simplified:               519
% 3.36/1.01  sup_given_eliminated:                   4
% 3.36/1.01  comparisons_done:                       0
% 3.36/1.01  comparisons_avoided:                    8
% 3.36/1.01  
% 3.36/1.01  ------ Simplifications
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  sim_fw_subset_subsumed:                 18
% 3.36/1.01  sim_bw_subset_subsumed:                 3
% 3.36/1.01  sim_fw_subsumed:                        186
% 3.36/1.01  sim_bw_subsumed:                        0
% 3.36/1.01  sim_fw_subsumption_res:                 0
% 3.36/1.01  sim_bw_subsumption_res:                 0
% 3.36/1.01  sim_tautology_del:                      10
% 3.36/1.01  sim_eq_tautology_del:                   47
% 3.36/1.01  sim_eq_res_simp:                        4
% 3.36/1.01  sim_fw_demodulated:                     314
% 3.36/1.01  sim_bw_demodulated:                     43
% 3.36/1.01  sim_light_normalised:                   237
% 3.36/1.01  sim_joinable_taut:                      0
% 3.36/1.01  sim_joinable_simp:                      0
% 3.36/1.01  sim_ac_normalised:                      0
% 3.36/1.01  sim_smt_subsumption:                    0
% 3.36/1.01  
%------------------------------------------------------------------------------
