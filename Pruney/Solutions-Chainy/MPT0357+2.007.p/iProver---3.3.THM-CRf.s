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
% DateTime   : Thu Dec  3 11:39:46 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :  136 (2159 expanded)
%              Number of clauses        :   88 ( 757 expanded)
%              Number of leaves         :   17 ( 571 expanded)
%              Depth                    :   28
%              Number of atoms          :  210 (2996 expanded)
%              Number of equality atoms :  126 (1936 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,sK2),X1)
        & r1_tarski(k3_subset_1(X0,X1),sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
          & r1_tarski(k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    & r1_tarski(k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f31,f31])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f48,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_7,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_328,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_333,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_328,c_8])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_322,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_329,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1703,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_322,c_329])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_324,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_332,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1064,plain,
    ( k4_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),sK2)) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_324,c_332])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1210,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k3_subset_1(sK0,sK1))) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1064,c_1])).

cnf(c_1882,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1703,c_1210])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_323,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_331,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_327,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_748,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_331,c_327])).

cnf(c_5,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_750,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_748,c_5])).

cnf(c_1503,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_323,c_750])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_21,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2170,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1503,c_21])).

cnf(c_2174,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_2170,c_332])).

cnf(c_2334,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2174,c_1])).

cnf(c_927,plain,
    ( m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_333])).

cnf(c_985,plain,
    ( m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_zfmisc_1(k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_927])).

cnf(c_1706,plain,
    ( k3_subset_1(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_985,c_329])).

cnf(c_15899,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_1,c_1706])).

cnf(c_1680,plain,
    ( m1_subset_1(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_zfmisc_1(k4_xboole_0(k4_xboole_0(X0,X1),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_985])).

cnf(c_4723,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[status(thm)],[c_1680,c_329])).

cnf(c_15893,plain,
    ( k3_subset_1(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_1,c_1706])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16145,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k3_subset_1(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_15893,c_0])).

cnf(c_1705,plain,
    ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_927,c_329])).

cnf(c_1704,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_333,c_329])).

cnf(c_10680,plain,
    ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1,c_1704])).

cnf(c_11007,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_10680,c_0])).

cnf(c_11167,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_11007,c_1705])).

cnf(c_16264,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_16145,c_1705,c_11167])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_330,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1063,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_330,c_332])).

cnf(c_16265,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_16264,c_1063])).

cnf(c_326,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1701,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_326,c_329])).

cnf(c_1709,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1701,c_5])).

cnf(c_2686,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1709,c_1])).

cnf(c_1062,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_331,c_332])).

cnf(c_2689,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2686,c_1062])).

cnf(c_16266,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16265,c_2689])).

cnf(c_16334,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k3_subset_1(k4_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_15899,c_4723,c_16266])).

cnf(c_16335,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16334,c_5,c_16266])).

cnf(c_16586,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_16335])).

cnf(c_874,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_16831,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_16586,c_874])).

cnf(c_16866,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_16831,c_874,c_1709])).

cnf(c_11882,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1,c_1705])).

cnf(c_22890,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_16866,c_11882])).

cnf(c_24376,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_2334,c_22890])).

cnf(c_24447,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_24376,c_2334])).

cnf(c_879,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_xboole_0(k3_subset_1(X1,X0),X2),k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,k4_xboole_0(k3_subset_1(X1,X0),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_330,c_327])).

cnf(c_24688,plain,
    ( m1_subset_1(k4_xboole_0(k3_subset_1(sK0,k4_xboole_0(sK0,sK2)),X0),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,k4_xboole_0(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_24447,c_879])).

cnf(c_24691,plain,
    ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,k4_xboole_0(sK2,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24688,c_24447])).

cnf(c_26881,plain,
    ( m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,k4_xboole_0(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_24691])).

cnf(c_1504,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_322,c_750])).

cnf(c_2176,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1504,c_21])).

cnf(c_2180,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = sK1 ),
    inference(superposition,[status(thm)],[c_2176,c_332])).

cnf(c_2365,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_2180,c_1])).

cnf(c_24385,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2365,c_22890])).

cnf(c_24439,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_24385,c_2365])).

cnf(c_26885,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26881,c_1882,c_24439])).

cnf(c_1702,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_323,c_329])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_325,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1875,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1702,c_325])).

cnf(c_27479,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26885,c_1875])).

cnf(c_27480,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_27479])).

cnf(c_27483,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_333,c_27480])).

cnf(c_27486,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_333,c_27483])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:47:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.98/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.98/1.49  
% 7.98/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.98/1.49  
% 7.98/1.49  ------  iProver source info
% 7.98/1.49  
% 7.98/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.98/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.98/1.49  git: non_committed_changes: false
% 7.98/1.49  git: last_make_outside_of_git: false
% 7.98/1.49  
% 7.98/1.49  ------ 
% 7.98/1.49  
% 7.98/1.49  ------ Input Options
% 7.98/1.49  
% 7.98/1.49  --out_options                           all
% 7.98/1.49  --tptp_safe_out                         true
% 7.98/1.49  --problem_path                          ""
% 7.98/1.49  --include_path                          ""
% 7.98/1.49  --clausifier                            res/vclausify_rel
% 7.98/1.49  --clausifier_options                    ""
% 7.98/1.49  --stdin                                 false
% 7.98/1.49  --stats_out                             all
% 7.98/1.49  
% 7.98/1.49  ------ General Options
% 7.98/1.49  
% 7.98/1.49  --fof                                   false
% 7.98/1.49  --time_out_real                         305.
% 7.98/1.49  --time_out_virtual                      -1.
% 7.98/1.49  --symbol_type_check                     false
% 7.98/1.49  --clausify_out                          false
% 7.98/1.49  --sig_cnt_out                           false
% 7.98/1.49  --trig_cnt_out                          false
% 7.98/1.49  --trig_cnt_out_tolerance                1.
% 7.98/1.49  --trig_cnt_out_sk_spl                   false
% 7.98/1.49  --abstr_cl_out                          false
% 7.98/1.49  
% 7.98/1.49  ------ Global Options
% 7.98/1.49  
% 7.98/1.49  --schedule                              default
% 7.98/1.49  --add_important_lit                     false
% 7.98/1.49  --prop_solver_per_cl                    1000
% 7.98/1.49  --min_unsat_core                        false
% 7.98/1.49  --soft_assumptions                      false
% 7.98/1.49  --soft_lemma_size                       3
% 7.98/1.49  --prop_impl_unit_size                   0
% 7.98/1.49  --prop_impl_unit                        []
% 7.98/1.49  --share_sel_clauses                     true
% 7.98/1.49  --reset_solvers                         false
% 7.98/1.49  --bc_imp_inh                            [conj_cone]
% 7.98/1.49  --conj_cone_tolerance                   3.
% 7.98/1.49  --extra_neg_conj                        none
% 7.98/1.49  --large_theory_mode                     true
% 7.98/1.49  --prolific_symb_bound                   200
% 7.98/1.49  --lt_threshold                          2000
% 7.98/1.49  --clause_weak_htbl                      true
% 7.98/1.49  --gc_record_bc_elim                     false
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing Options
% 7.98/1.49  
% 7.98/1.49  --preprocessing_flag                    true
% 7.98/1.49  --time_out_prep_mult                    0.1
% 7.98/1.49  --splitting_mode                        input
% 7.98/1.49  --splitting_grd                         true
% 7.98/1.49  --splitting_cvd                         false
% 7.98/1.49  --splitting_cvd_svl                     false
% 7.98/1.49  --splitting_nvd                         32
% 7.98/1.49  --sub_typing                            true
% 7.98/1.49  --prep_gs_sim                           true
% 7.98/1.49  --prep_unflatten                        true
% 7.98/1.49  --prep_res_sim                          true
% 7.98/1.49  --prep_upred                            true
% 7.98/1.49  --prep_sem_filter                       exhaustive
% 7.98/1.49  --prep_sem_filter_out                   false
% 7.98/1.49  --pred_elim                             true
% 7.98/1.49  --res_sim_input                         true
% 7.98/1.49  --eq_ax_congr_red                       true
% 7.98/1.49  --pure_diseq_elim                       true
% 7.98/1.49  --brand_transform                       false
% 7.98/1.49  --non_eq_to_eq                          false
% 7.98/1.49  --prep_def_merge                        true
% 7.98/1.49  --prep_def_merge_prop_impl              false
% 7.98/1.49  --prep_def_merge_mbd                    true
% 7.98/1.49  --prep_def_merge_tr_red                 false
% 7.98/1.49  --prep_def_merge_tr_cl                  false
% 7.98/1.49  --smt_preprocessing                     true
% 7.98/1.49  --smt_ac_axioms                         fast
% 7.98/1.49  --preprocessed_out                      false
% 7.98/1.49  --preprocessed_stats                    false
% 7.98/1.49  
% 7.98/1.49  ------ Abstraction refinement Options
% 7.98/1.49  
% 7.98/1.49  --abstr_ref                             []
% 7.98/1.49  --abstr_ref_prep                        false
% 7.98/1.49  --abstr_ref_until_sat                   false
% 7.98/1.49  --abstr_ref_sig_restrict                funpre
% 7.98/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.98/1.49  --abstr_ref_under                       []
% 7.98/1.49  
% 7.98/1.49  ------ SAT Options
% 7.98/1.49  
% 7.98/1.49  --sat_mode                              false
% 7.98/1.49  --sat_fm_restart_options                ""
% 7.98/1.49  --sat_gr_def                            false
% 7.98/1.49  --sat_epr_types                         true
% 7.98/1.49  --sat_non_cyclic_types                  false
% 7.98/1.49  --sat_finite_models                     false
% 7.98/1.49  --sat_fm_lemmas                         false
% 7.98/1.49  --sat_fm_prep                           false
% 7.98/1.49  --sat_fm_uc_incr                        true
% 7.98/1.49  --sat_out_model                         small
% 7.98/1.49  --sat_out_clauses                       false
% 7.98/1.49  
% 7.98/1.49  ------ QBF Options
% 7.98/1.49  
% 7.98/1.49  --qbf_mode                              false
% 7.98/1.49  --qbf_elim_univ                         false
% 7.98/1.49  --qbf_dom_inst                          none
% 7.98/1.49  --qbf_dom_pre_inst                      false
% 7.98/1.49  --qbf_sk_in                             false
% 7.98/1.49  --qbf_pred_elim                         true
% 7.98/1.49  --qbf_split                             512
% 7.98/1.49  
% 7.98/1.49  ------ BMC1 Options
% 7.98/1.49  
% 7.98/1.49  --bmc1_incremental                      false
% 7.98/1.49  --bmc1_axioms                           reachable_all
% 7.98/1.49  --bmc1_min_bound                        0
% 7.98/1.49  --bmc1_max_bound                        -1
% 7.98/1.49  --bmc1_max_bound_default                -1
% 7.98/1.49  --bmc1_symbol_reachability              true
% 7.98/1.49  --bmc1_property_lemmas                  false
% 7.98/1.49  --bmc1_k_induction                      false
% 7.98/1.49  --bmc1_non_equiv_states                 false
% 7.98/1.49  --bmc1_deadlock                         false
% 7.98/1.49  --bmc1_ucm                              false
% 7.98/1.49  --bmc1_add_unsat_core                   none
% 7.98/1.49  --bmc1_unsat_core_children              false
% 7.98/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.98/1.49  --bmc1_out_stat                         full
% 7.98/1.49  --bmc1_ground_init                      false
% 7.98/1.49  --bmc1_pre_inst_next_state              false
% 7.98/1.49  --bmc1_pre_inst_state                   false
% 7.98/1.49  --bmc1_pre_inst_reach_state             false
% 7.98/1.49  --bmc1_out_unsat_core                   false
% 7.98/1.49  --bmc1_aig_witness_out                  false
% 7.98/1.49  --bmc1_verbose                          false
% 7.98/1.49  --bmc1_dump_clauses_tptp                false
% 7.98/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.98/1.49  --bmc1_dump_file                        -
% 7.98/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.98/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.98/1.49  --bmc1_ucm_extend_mode                  1
% 7.98/1.49  --bmc1_ucm_init_mode                    2
% 7.98/1.49  --bmc1_ucm_cone_mode                    none
% 7.98/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.98/1.49  --bmc1_ucm_relax_model                  4
% 7.98/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.98/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.98/1.49  --bmc1_ucm_layered_model                none
% 7.98/1.49  --bmc1_ucm_max_lemma_size               10
% 7.98/1.49  
% 7.98/1.49  ------ AIG Options
% 7.98/1.49  
% 7.98/1.49  --aig_mode                              false
% 7.98/1.49  
% 7.98/1.49  ------ Instantiation Options
% 7.98/1.49  
% 7.98/1.49  --instantiation_flag                    true
% 7.98/1.49  --inst_sos_flag                         true
% 7.98/1.49  --inst_sos_phase                        true
% 7.98/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.98/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.98/1.49  --inst_lit_sel_side                     num_symb
% 7.98/1.49  --inst_solver_per_active                1400
% 7.98/1.49  --inst_solver_calls_frac                1.
% 7.98/1.49  --inst_passive_queue_type               priority_queues
% 7.98/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.98/1.49  --inst_passive_queues_freq              [25;2]
% 7.98/1.49  --inst_dismatching                      true
% 7.98/1.49  --inst_eager_unprocessed_to_passive     true
% 7.98/1.49  --inst_prop_sim_given                   true
% 7.98/1.49  --inst_prop_sim_new                     false
% 7.98/1.49  --inst_subs_new                         false
% 7.98/1.49  --inst_eq_res_simp                      false
% 7.98/1.49  --inst_subs_given                       false
% 7.98/1.49  --inst_orphan_elimination               true
% 7.98/1.49  --inst_learning_loop_flag               true
% 7.98/1.49  --inst_learning_start                   3000
% 7.98/1.49  --inst_learning_factor                  2
% 7.98/1.49  --inst_start_prop_sim_after_learn       3
% 7.98/1.49  --inst_sel_renew                        solver
% 7.98/1.49  --inst_lit_activity_flag                true
% 7.98/1.49  --inst_restr_to_given                   false
% 7.98/1.49  --inst_activity_threshold               500
% 7.98/1.49  --inst_out_proof                        true
% 7.98/1.49  
% 7.98/1.49  ------ Resolution Options
% 7.98/1.49  
% 7.98/1.49  --resolution_flag                       true
% 7.98/1.49  --res_lit_sel                           adaptive
% 7.98/1.49  --res_lit_sel_side                      none
% 7.98/1.49  --res_ordering                          kbo
% 7.98/1.49  --res_to_prop_solver                    active
% 7.98/1.49  --res_prop_simpl_new                    false
% 7.98/1.49  --res_prop_simpl_given                  true
% 7.98/1.49  --res_passive_queue_type                priority_queues
% 7.98/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.98/1.49  --res_passive_queues_freq               [15;5]
% 7.98/1.49  --res_forward_subs                      full
% 7.98/1.49  --res_backward_subs                     full
% 7.98/1.49  --res_forward_subs_resolution           true
% 7.98/1.49  --res_backward_subs_resolution          true
% 7.98/1.49  --res_orphan_elimination                true
% 7.98/1.49  --res_time_limit                        2.
% 7.98/1.49  --res_out_proof                         true
% 7.98/1.49  
% 7.98/1.49  ------ Superposition Options
% 7.98/1.49  
% 7.98/1.49  --superposition_flag                    true
% 7.98/1.49  --sup_passive_queue_type                priority_queues
% 7.98/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.98/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.98/1.49  --demod_completeness_check              fast
% 7.98/1.49  --demod_use_ground                      true
% 7.98/1.49  --sup_to_prop_solver                    passive
% 7.98/1.49  --sup_prop_simpl_new                    true
% 7.98/1.49  --sup_prop_simpl_given                  true
% 7.98/1.49  --sup_fun_splitting                     true
% 7.98/1.49  --sup_smt_interval                      50000
% 7.98/1.49  
% 7.98/1.49  ------ Superposition Simplification Setup
% 7.98/1.49  
% 7.98/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.98/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.98/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.98/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.98/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.98/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.98/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.98/1.49  --sup_immed_triv                        [TrivRules]
% 7.98/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.49  --sup_immed_bw_main                     []
% 7.98/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.98/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.98/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.49  --sup_input_bw                          []
% 7.98/1.49  
% 7.98/1.49  ------ Combination Options
% 7.98/1.49  
% 7.98/1.49  --comb_res_mult                         3
% 7.98/1.49  --comb_sup_mult                         2
% 7.98/1.49  --comb_inst_mult                        10
% 7.98/1.49  
% 7.98/1.49  ------ Debug Options
% 7.98/1.49  
% 7.98/1.49  --dbg_backtrace                         false
% 7.98/1.49  --dbg_dump_prop_clauses                 false
% 7.98/1.49  --dbg_dump_prop_clauses_file            -
% 7.98/1.49  --dbg_out_stat                          false
% 7.98/1.49  ------ Parsing...
% 7.98/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.98/1.49  ------ Proving...
% 7.98/1.49  ------ Problem Properties 
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  clauses                                 15
% 7.98/1.49  conjectures                             4
% 7.98/1.49  EPR                                     1
% 7.98/1.49  Horn                                    15
% 7.98/1.49  unary                                   12
% 7.98/1.49  binary                                  2
% 7.98/1.49  lits                                    20
% 7.98/1.49  lits eq                                 6
% 7.98/1.49  fd_pure                                 0
% 7.98/1.49  fd_pseudo                               0
% 7.98/1.49  fd_cond                                 0
% 7.98/1.49  fd_pseudo_cond                          0
% 7.98/1.49  AC symbols                              0
% 7.98/1.49  
% 7.98/1.49  ------ Schedule dynamic 5 is on 
% 7.98/1.49  
% 7.98/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  ------ 
% 7.98/1.49  Current options:
% 7.98/1.49  ------ 
% 7.98/1.49  
% 7.98/1.49  ------ Input Options
% 7.98/1.49  
% 7.98/1.49  --out_options                           all
% 7.98/1.49  --tptp_safe_out                         true
% 7.98/1.49  --problem_path                          ""
% 7.98/1.49  --include_path                          ""
% 7.98/1.49  --clausifier                            res/vclausify_rel
% 7.98/1.49  --clausifier_options                    ""
% 7.98/1.49  --stdin                                 false
% 7.98/1.49  --stats_out                             all
% 7.98/1.49  
% 7.98/1.49  ------ General Options
% 7.98/1.49  
% 7.98/1.49  --fof                                   false
% 7.98/1.49  --time_out_real                         305.
% 7.98/1.49  --time_out_virtual                      -1.
% 7.98/1.49  --symbol_type_check                     false
% 7.98/1.49  --clausify_out                          false
% 7.98/1.49  --sig_cnt_out                           false
% 7.98/1.49  --trig_cnt_out                          false
% 7.98/1.49  --trig_cnt_out_tolerance                1.
% 7.98/1.49  --trig_cnt_out_sk_spl                   false
% 7.98/1.49  --abstr_cl_out                          false
% 7.98/1.49  
% 7.98/1.49  ------ Global Options
% 7.98/1.49  
% 7.98/1.49  --schedule                              default
% 7.98/1.49  --add_important_lit                     false
% 7.98/1.49  --prop_solver_per_cl                    1000
% 7.98/1.49  --min_unsat_core                        false
% 7.98/1.49  --soft_assumptions                      false
% 7.98/1.49  --soft_lemma_size                       3
% 7.98/1.49  --prop_impl_unit_size                   0
% 7.98/1.49  --prop_impl_unit                        []
% 7.98/1.49  --share_sel_clauses                     true
% 7.98/1.49  --reset_solvers                         false
% 7.98/1.49  --bc_imp_inh                            [conj_cone]
% 7.98/1.49  --conj_cone_tolerance                   3.
% 7.98/1.49  --extra_neg_conj                        none
% 7.98/1.49  --large_theory_mode                     true
% 7.98/1.49  --prolific_symb_bound                   200
% 7.98/1.49  --lt_threshold                          2000
% 7.98/1.49  --clause_weak_htbl                      true
% 7.98/1.49  --gc_record_bc_elim                     false
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing Options
% 7.98/1.49  
% 7.98/1.49  --preprocessing_flag                    true
% 7.98/1.49  --time_out_prep_mult                    0.1
% 7.98/1.49  --splitting_mode                        input
% 7.98/1.49  --splitting_grd                         true
% 7.98/1.49  --splitting_cvd                         false
% 7.98/1.49  --splitting_cvd_svl                     false
% 7.98/1.49  --splitting_nvd                         32
% 7.98/1.49  --sub_typing                            true
% 7.98/1.49  --prep_gs_sim                           true
% 7.98/1.49  --prep_unflatten                        true
% 7.98/1.49  --prep_res_sim                          true
% 7.98/1.49  --prep_upred                            true
% 7.98/1.49  --prep_sem_filter                       exhaustive
% 7.98/1.49  --prep_sem_filter_out                   false
% 7.98/1.49  --pred_elim                             true
% 7.98/1.49  --res_sim_input                         true
% 7.98/1.49  --eq_ax_congr_red                       true
% 7.98/1.49  --pure_diseq_elim                       true
% 7.98/1.49  --brand_transform                       false
% 7.98/1.49  --non_eq_to_eq                          false
% 7.98/1.49  --prep_def_merge                        true
% 7.98/1.49  --prep_def_merge_prop_impl              false
% 7.98/1.49  --prep_def_merge_mbd                    true
% 7.98/1.49  --prep_def_merge_tr_red                 false
% 7.98/1.49  --prep_def_merge_tr_cl                  false
% 7.98/1.49  --smt_preprocessing                     true
% 7.98/1.49  --smt_ac_axioms                         fast
% 7.98/1.49  --preprocessed_out                      false
% 7.98/1.49  --preprocessed_stats                    false
% 7.98/1.49  
% 7.98/1.49  ------ Abstraction refinement Options
% 7.98/1.49  
% 7.98/1.49  --abstr_ref                             []
% 7.98/1.49  --abstr_ref_prep                        false
% 7.98/1.49  --abstr_ref_until_sat                   false
% 7.98/1.49  --abstr_ref_sig_restrict                funpre
% 7.98/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.98/1.49  --abstr_ref_under                       []
% 7.98/1.49  
% 7.98/1.49  ------ SAT Options
% 7.98/1.49  
% 7.98/1.49  --sat_mode                              false
% 7.98/1.49  --sat_fm_restart_options                ""
% 7.98/1.49  --sat_gr_def                            false
% 7.98/1.49  --sat_epr_types                         true
% 7.98/1.49  --sat_non_cyclic_types                  false
% 7.98/1.49  --sat_finite_models                     false
% 7.98/1.49  --sat_fm_lemmas                         false
% 7.98/1.49  --sat_fm_prep                           false
% 7.98/1.49  --sat_fm_uc_incr                        true
% 7.98/1.49  --sat_out_model                         small
% 7.98/1.49  --sat_out_clauses                       false
% 7.98/1.49  
% 7.98/1.49  ------ QBF Options
% 7.98/1.49  
% 7.98/1.49  --qbf_mode                              false
% 7.98/1.49  --qbf_elim_univ                         false
% 7.98/1.49  --qbf_dom_inst                          none
% 7.98/1.49  --qbf_dom_pre_inst                      false
% 7.98/1.49  --qbf_sk_in                             false
% 7.98/1.49  --qbf_pred_elim                         true
% 7.98/1.49  --qbf_split                             512
% 7.98/1.49  
% 7.98/1.49  ------ BMC1 Options
% 7.98/1.49  
% 7.98/1.49  --bmc1_incremental                      false
% 7.98/1.49  --bmc1_axioms                           reachable_all
% 7.98/1.49  --bmc1_min_bound                        0
% 7.98/1.49  --bmc1_max_bound                        -1
% 7.98/1.49  --bmc1_max_bound_default                -1
% 7.98/1.49  --bmc1_symbol_reachability              true
% 7.98/1.49  --bmc1_property_lemmas                  false
% 7.98/1.49  --bmc1_k_induction                      false
% 7.98/1.49  --bmc1_non_equiv_states                 false
% 7.98/1.49  --bmc1_deadlock                         false
% 7.98/1.49  --bmc1_ucm                              false
% 7.98/1.49  --bmc1_add_unsat_core                   none
% 7.98/1.49  --bmc1_unsat_core_children              false
% 7.98/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.98/1.49  --bmc1_out_stat                         full
% 7.98/1.49  --bmc1_ground_init                      false
% 7.98/1.49  --bmc1_pre_inst_next_state              false
% 7.98/1.49  --bmc1_pre_inst_state                   false
% 7.98/1.49  --bmc1_pre_inst_reach_state             false
% 7.98/1.49  --bmc1_out_unsat_core                   false
% 7.98/1.49  --bmc1_aig_witness_out                  false
% 7.98/1.49  --bmc1_verbose                          false
% 7.98/1.49  --bmc1_dump_clauses_tptp                false
% 7.98/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.98/1.49  --bmc1_dump_file                        -
% 7.98/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.98/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.98/1.49  --bmc1_ucm_extend_mode                  1
% 7.98/1.49  --bmc1_ucm_init_mode                    2
% 7.98/1.49  --bmc1_ucm_cone_mode                    none
% 7.98/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.98/1.49  --bmc1_ucm_relax_model                  4
% 7.98/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.98/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.98/1.49  --bmc1_ucm_layered_model                none
% 7.98/1.49  --bmc1_ucm_max_lemma_size               10
% 7.98/1.49  
% 7.98/1.49  ------ AIG Options
% 7.98/1.49  
% 7.98/1.49  --aig_mode                              false
% 7.98/1.49  
% 7.98/1.49  ------ Instantiation Options
% 7.98/1.49  
% 7.98/1.49  --instantiation_flag                    true
% 7.98/1.49  --inst_sos_flag                         true
% 7.98/1.49  --inst_sos_phase                        true
% 7.98/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.98/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.98/1.49  --inst_lit_sel_side                     none
% 7.98/1.49  --inst_solver_per_active                1400
% 7.98/1.49  --inst_solver_calls_frac                1.
% 7.98/1.49  --inst_passive_queue_type               priority_queues
% 7.98/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.98/1.49  --inst_passive_queues_freq              [25;2]
% 7.98/1.49  --inst_dismatching                      true
% 7.98/1.49  --inst_eager_unprocessed_to_passive     true
% 7.98/1.49  --inst_prop_sim_given                   true
% 7.98/1.49  --inst_prop_sim_new                     false
% 7.98/1.49  --inst_subs_new                         false
% 7.98/1.49  --inst_eq_res_simp                      false
% 7.98/1.49  --inst_subs_given                       false
% 7.98/1.49  --inst_orphan_elimination               true
% 7.98/1.49  --inst_learning_loop_flag               true
% 7.98/1.49  --inst_learning_start                   3000
% 7.98/1.49  --inst_learning_factor                  2
% 7.98/1.49  --inst_start_prop_sim_after_learn       3
% 7.98/1.49  --inst_sel_renew                        solver
% 7.98/1.49  --inst_lit_activity_flag                true
% 7.98/1.49  --inst_restr_to_given                   false
% 7.98/1.49  --inst_activity_threshold               500
% 7.98/1.49  --inst_out_proof                        true
% 7.98/1.49  
% 7.98/1.49  ------ Resolution Options
% 7.98/1.49  
% 7.98/1.49  --resolution_flag                       false
% 7.98/1.49  --res_lit_sel                           adaptive
% 7.98/1.49  --res_lit_sel_side                      none
% 7.98/1.49  --res_ordering                          kbo
% 7.98/1.49  --res_to_prop_solver                    active
% 7.98/1.49  --res_prop_simpl_new                    false
% 7.98/1.49  --res_prop_simpl_given                  true
% 7.98/1.49  --res_passive_queue_type                priority_queues
% 7.98/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.98/1.49  --res_passive_queues_freq               [15;5]
% 7.98/1.49  --res_forward_subs                      full
% 7.98/1.49  --res_backward_subs                     full
% 7.98/1.49  --res_forward_subs_resolution           true
% 7.98/1.49  --res_backward_subs_resolution          true
% 7.98/1.49  --res_orphan_elimination                true
% 7.98/1.49  --res_time_limit                        2.
% 7.98/1.49  --res_out_proof                         true
% 7.98/1.49  
% 7.98/1.49  ------ Superposition Options
% 7.98/1.49  
% 7.98/1.49  --superposition_flag                    true
% 7.98/1.49  --sup_passive_queue_type                priority_queues
% 7.98/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.98/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.98/1.49  --demod_completeness_check              fast
% 7.98/1.49  --demod_use_ground                      true
% 7.98/1.49  --sup_to_prop_solver                    passive
% 7.98/1.49  --sup_prop_simpl_new                    true
% 7.98/1.49  --sup_prop_simpl_given                  true
% 7.98/1.49  --sup_fun_splitting                     true
% 7.98/1.49  --sup_smt_interval                      50000
% 7.98/1.49  
% 7.98/1.49  ------ Superposition Simplification Setup
% 7.98/1.49  
% 7.98/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.98/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.98/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.98/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.98/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.98/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.98/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.98/1.49  --sup_immed_triv                        [TrivRules]
% 7.98/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.49  --sup_immed_bw_main                     []
% 7.98/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.98/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.98/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.49  --sup_input_bw                          []
% 7.98/1.49  
% 7.98/1.49  ------ Combination Options
% 7.98/1.49  
% 7.98/1.49  --comb_res_mult                         3
% 7.98/1.49  --comb_sup_mult                         2
% 7.98/1.49  --comb_inst_mult                        10
% 7.98/1.49  
% 7.98/1.49  ------ Debug Options
% 7.98/1.49  
% 7.98/1.49  --dbg_backtrace                         false
% 7.98/1.49  --dbg_dump_prop_clauses                 false
% 7.98/1.49  --dbg_dump_prop_clauses_file            -
% 7.98/1.49  --dbg_out_stat                          false
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  ------ Proving...
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  % SZS status Theorem for theBenchmark.p
% 7.98/1.49  
% 7.98/1.49   Resolution empty clause
% 7.98/1.49  
% 7.98/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.98/1.49  
% 7.98/1.49  fof(f10,axiom,(
% 7.98/1.49    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f35,plain,(
% 7.98/1.49    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f10])).
% 7.98/1.49  
% 7.98/1.49  fof(f11,axiom,(
% 7.98/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f36,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f11])).
% 7.98/1.49  
% 7.98/1.49  fof(f15,conjecture,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f16,negated_conjecture,(
% 7.98/1.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 7.98/1.49    inference(negated_conjecture,[],[f15])).
% 7.98/1.49  
% 7.98/1.49  fof(f21,plain,(
% 7.98/1.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(ennf_transformation,[],[f16])).
% 7.98/1.49  
% 7.98/1.49  fof(f22,plain,(
% 7.98/1.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(flattening,[],[f21])).
% 7.98/1.49  
% 7.98/1.49  fof(f24,plain,(
% 7.98/1.49    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,sK2),X1) & r1_tarski(k3_subset_1(X0,X1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 7.98/1.49    introduced(choice_axiom,[])).
% 7.98/1.49  
% 7.98/1.49  fof(f23,plain,(
% 7.98/1.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 7.98/1.49    introduced(choice_axiom,[])).
% 7.98/1.49  
% 7.98/1.49  fof(f25,plain,(
% 7.98/1.49    (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.98/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).
% 7.98/1.49  
% 7.98/1.49  fof(f40,plain,(
% 7.98/1.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.98/1.49    inference(cnf_transformation,[],[f25])).
% 7.98/1.49  
% 7.98/1.49  fof(f9,axiom,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f18,plain,(
% 7.98/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(ennf_transformation,[],[f9])).
% 7.98/1.49  
% 7.98/1.49  fof(f34,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f18])).
% 7.98/1.49  
% 7.98/1.49  fof(f42,plain,(
% 7.98/1.49    r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 7.98/1.49    inference(cnf_transformation,[],[f25])).
% 7.98/1.49  
% 7.98/1.49  fof(f3,axiom,(
% 7.98/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f17,plain,(
% 7.98/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.98/1.49    inference(ennf_transformation,[],[f3])).
% 7.98/1.49  
% 7.98/1.49  fof(f28,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f17])).
% 7.98/1.49  
% 7.98/1.49  fof(f6,axiom,(
% 7.98/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f31,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f6])).
% 7.98/1.49  
% 7.98/1.49  fof(f47,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.98/1.49    inference(definition_unfolding,[],[f28,f31])).
% 7.98/1.49  
% 7.98/1.49  fof(f1,axiom,(
% 7.98/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f26,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f1])).
% 7.98/1.49  
% 7.98/1.49  fof(f46,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.98/1.49    inference(definition_unfolding,[],[f26,f31,f31])).
% 7.98/1.49  
% 7.98/1.49  fof(f41,plain,(
% 7.98/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.98/1.49    inference(cnf_transformation,[],[f25])).
% 7.98/1.49  
% 7.98/1.49  fof(f4,axiom,(
% 7.98/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f29,plain,(
% 7.98/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f4])).
% 7.98/1.49  
% 7.98/1.49  fof(f13,axiom,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f19,plain,(
% 7.98/1.49    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(ennf_transformation,[],[f13])).
% 7.98/1.49  
% 7.98/1.49  fof(f20,plain,(
% 7.98/1.49    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(flattening,[],[f19])).
% 7.98/1.49  
% 7.98/1.49  fof(f38,plain,(
% 7.98/1.49    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f20])).
% 7.98/1.49  
% 7.98/1.49  fof(f8,axiom,(
% 7.98/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f33,plain,(
% 7.98/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.98/1.49    inference(cnf_transformation,[],[f8])).
% 7.98/1.49  
% 7.98/1.49  fof(f12,axiom,(
% 7.98/1.49    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f37,plain,(
% 7.98/1.49    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f12])).
% 7.98/1.49  
% 7.98/1.49  fof(f7,axiom,(
% 7.98/1.49    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f32,plain,(
% 7.98/1.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f7])).
% 7.98/1.49  
% 7.98/1.49  fof(f44,plain,(
% 7.98/1.49    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 7.98/1.49    inference(definition_unfolding,[],[f37,f32])).
% 7.98/1.49  
% 7.98/1.49  fof(f48,plain,(
% 7.98/1.49    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 7.98/1.49    inference(definition_unfolding,[],[f33,f44])).
% 7.98/1.49  
% 7.98/1.49  fof(f14,axiom,(
% 7.98/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f39,plain,(
% 7.98/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f14])).
% 7.98/1.49  
% 7.98/1.49  fof(f2,axiom,(
% 7.98/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f27,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f2])).
% 7.98/1.49  
% 7.98/1.49  fof(f45,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.98/1.49    inference(definition_unfolding,[],[f27,f31])).
% 7.98/1.49  
% 7.98/1.49  fof(f5,axiom,(
% 7.98/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.98/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f30,plain,(
% 7.98/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f5])).
% 7.98/1.49  
% 7.98/1.49  fof(f43,plain,(
% 7.98/1.49    ~r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 7.98/1.49    inference(cnf_transformation,[],[f25])).
% 7.98/1.49  
% 7.98/1.49  cnf(c_7,plain,
% 7.98/1.49      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_328,plain,
% 7.98/1.49      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_8,plain,
% 7.98/1.49      ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
% 7.98/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_333,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_328,c_8]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_14,negated_conjecture,
% 7.98/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_322,plain,
% 7.98/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_6,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.98/1.49      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_329,plain,
% 7.98/1.49      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.98/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1703,plain,
% 7.98/1.49      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_322,c_329]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_12,negated_conjecture,
% 7.98/1.49      ( r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
% 7.98/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_324,plain,
% 7.98/1.49      ( r1_tarski(k3_subset_1(sK0,sK1),sK2) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2,plain,
% 7.98/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.98/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_332,plain,
% 7.98/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.98/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1064,plain,
% 7.98/1.49      ( k4_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),sK2)) = k3_subset_1(sK0,sK1) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_324,c_332]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1,plain,
% 7.98/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1210,plain,
% 7.98/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k3_subset_1(sK0,sK1))) = k3_subset_1(sK0,sK1) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1064,c_1]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1882,plain,
% 7.98/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_1703,c_1210]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_13,negated_conjecture,
% 7.98/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_323,plain,
% 7.98/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3,plain,
% 7.98/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_331,plain,
% 7.98/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_9,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.98/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.98/1.49      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 7.98/1.49      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_327,plain,
% 7.98/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.98/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.98/1.49      | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
% 7.98/1.49      | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_748,plain,
% 7.98/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.98/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 7.98/1.49      | r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_331,c_327]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5,plain,
% 7.98/1.49      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 7.98/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_750,plain,
% 7.98/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.98/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 7.98/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_748,c_5]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1503,plain,
% 7.98/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | r1_tarski(sK2,sK0) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_323,c_750]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_10,plain,
% 7.98/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_19,plain,
% 7.98/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_21,plain,
% 7.98/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2170,plain,
% 7.98/1.49      ( r1_tarski(sK2,sK0) = iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1503,c_21]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2174,plain,
% 7.98/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = sK2 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2170,c_332]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2334,plain,
% 7.98/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2174,c_1]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_927,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_333]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_985,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_zfmisc_1(k4_xboole_0(X0,X1))) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_927]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1706,plain,
% 7.98/1.49      ( k3_subset_1(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_985,c_329]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_15899,plain,
% 7.98/1.49      ( k3_subset_1(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_1706]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1680,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_zfmisc_1(k4_xboole_0(k4_xboole_0(X0,X1),X0))) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_985]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4723,plain,
% 7.98/1.49      ( k3_subset_1(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1680,c_329]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_15893,plain,
% 7.98/1.49      ( k3_subset_1(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_1706]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_0,plain,
% 7.98/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.98/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16145,plain,
% 7.98/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k3_subset_1(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_15893,c_0]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1705,plain,
% 7.98/1.49      ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_927,c_329]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1704,plain,
% 7.98/1.49      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_333,c_329]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_10680,plain,
% 7.98/1.49      ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_1704]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_11007,plain,
% 7.98/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_10680,c_0]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_11167,plain,
% 7.98/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_11007,c_1705]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16264,plain,
% 7.98/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_16145,c_1705,c_11167]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4,plain,
% 7.98/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_330,plain,
% 7.98/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1063,plain,
% 7.98/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_330,c_332]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16265,plain,
% 7.98/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_16264,c_1063]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_326,plain,
% 7.98/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1701,plain,
% 7.98/1.49      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_326,c_329]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1709,plain,
% 7.98/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_1701,c_5]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2686,plain,
% 7.98/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1709,c_1]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1062,plain,
% 7.98/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_331,c_332]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2689,plain,
% 7.98/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_2686,c_1062]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16266,plain,
% 7.98/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_16265,c_2689]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16334,plain,
% 7.98/1.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k3_subset_1(k4_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_15899,c_4723,c_16266]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16335,plain,
% 7.98/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_16334,c_5,c_16266]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16586,plain,
% 7.98/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_16335]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_874,plain,
% 7.98/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16831,plain,
% 7.98/1.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_16586,c_874]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16866,plain,
% 7.98/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_16831,c_874,c_1709]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_11882,plain,
% 7.98/1.49      ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_1705]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_22890,plain,
% 7.98/1.49      ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_16866,c_11882]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_24376,plain,
% 7.98/1.49      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2334,c_22890]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_24447,plain,
% 7.98/1.49      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_24376,c_2334]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_879,plain,
% 7.98/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.98/1.49      | m1_subset_1(k4_xboole_0(k3_subset_1(X1,X0),X2),k1_zfmisc_1(X1)) != iProver_top
% 7.98/1.49      | r1_tarski(X0,k3_subset_1(X1,k4_xboole_0(k3_subset_1(X1,X0),X2))) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_330,c_327]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_24688,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(k3_subset_1(sK0,k4_xboole_0(sK0,sK2)),X0),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,k4_xboole_0(sK2,X0))) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_24447,c_879]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_24691,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,k4_xboole_0(sK2,X0))) = iProver_top ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_24688,c_24447]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_26881,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,k4_xboole_0(sK0,sK1))) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1882,c_24691]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1504,plain,
% 7.98/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | r1_tarski(sK1,sK0) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_322,c_750]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2176,plain,
% 7.98/1.49      ( r1_tarski(sK1,sK0) = iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1504,c_21]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2180,plain,
% 7.98/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = sK1 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2176,c_332]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2365,plain,
% 7.98/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2180,c_1]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_24385,plain,
% 7.98/1.49      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2365,c_22890]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_24439,plain,
% 7.98/1.49      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_24385,c_2365]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_26885,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | r1_tarski(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_26881,c_1882,c_24439]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1702,plain,
% 7.98/1.49      ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_323,c_329]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_11,negated_conjecture,
% 7.98/1.49      ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
% 7.98/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_325,plain,
% 7.98/1.49      ( r1_tarski(k3_subset_1(sK0,sK2),sK1) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1875,plain,
% 7.98/1.49      ( r1_tarski(k4_xboole_0(sK0,sK2),sK1) != iProver_top ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_1702,c_325]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_27479,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_26885,c_1875]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_27480,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 7.98/1.49      | m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top ),
% 7.98/1.49      inference(renaming,[status(thm)],[c_27479]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_27483,plain,
% 7.98/1.49      ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_333,c_27480]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_27486,plain,
% 7.98/1.49      ( $false ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_333,c_27483]) ).
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.98/1.49  
% 7.98/1.49  ------                               Statistics
% 7.98/1.49  
% 7.98/1.49  ------ General
% 7.98/1.49  
% 7.98/1.49  abstr_ref_over_cycles:                  0
% 7.98/1.49  abstr_ref_under_cycles:                 0
% 7.98/1.49  gc_basic_clause_elim:                   0
% 7.98/1.49  forced_gc_time:                         0
% 7.98/1.49  parsing_time:                           0.007
% 7.98/1.49  unif_index_cands_time:                  0.
% 7.98/1.49  unif_index_add_time:                    0.
% 7.98/1.49  orderings_time:                         0.
% 7.98/1.49  out_proof_time:                         0.01
% 7.98/1.49  total_time:                             0.806
% 7.98/1.49  num_of_symbols:                         42
% 7.98/1.49  num_of_terms:                           29099
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing
% 7.98/1.49  
% 7.98/1.49  num_of_splits:                          0
% 7.98/1.49  num_of_split_atoms:                     0
% 7.98/1.49  num_of_reused_defs:                     0
% 7.98/1.49  num_eq_ax_congr_red:                    8
% 7.98/1.49  num_of_sem_filtered_clauses:            1
% 7.98/1.49  num_of_subtypes:                        0
% 7.98/1.49  monotx_restored_types:                  0
% 7.98/1.49  sat_num_of_epr_types:                   0
% 7.98/1.49  sat_num_of_non_cyclic_types:            0
% 7.98/1.49  sat_guarded_non_collapsed_types:        0
% 7.98/1.49  num_pure_diseq_elim:                    0
% 7.98/1.49  simp_replaced_by:                       0
% 7.98/1.49  res_preprocessed:                       62
% 7.98/1.49  prep_upred:                             0
% 7.98/1.49  prep_unflattend:                        0
% 7.98/1.49  smt_new_axioms:                         0
% 7.98/1.49  pred_elim_cands:                        2
% 7.98/1.49  pred_elim:                              0
% 7.98/1.49  pred_elim_cl:                           0
% 7.98/1.49  pred_elim_cycles:                       1
% 7.98/1.49  merged_defs:                            0
% 7.98/1.49  merged_defs_ncl:                        0
% 7.98/1.49  bin_hyper_res:                          0
% 7.98/1.49  prep_cycles:                            3
% 7.98/1.49  pred_elim_time:                         0.
% 7.98/1.49  splitting_time:                         0.
% 7.98/1.49  sem_filter_time:                        0.
% 7.98/1.49  monotx_time:                            0.
% 7.98/1.49  subtype_inf_time:                       0.
% 7.98/1.49  
% 7.98/1.49  ------ Problem properties
% 7.98/1.49  
% 7.98/1.49  clauses:                                15
% 7.98/1.49  conjectures:                            4
% 7.98/1.49  epr:                                    1
% 7.98/1.49  horn:                                   15
% 7.98/1.49  ground:                                 4
% 7.98/1.49  unary:                                  12
% 7.98/1.49  binary:                                 2
% 7.98/1.49  lits:                                   20
% 7.98/1.49  lits_eq:                                6
% 7.98/1.49  fd_pure:                                0
% 7.98/1.49  fd_pseudo:                              0
% 7.98/1.49  fd_cond:                                0
% 7.98/1.49  fd_pseudo_cond:                         0
% 7.98/1.49  ac_symbols:                             0
% 7.98/1.49  
% 7.98/1.49  ------ Propositional Solver
% 7.98/1.49  
% 7.98/1.49  prop_solver_calls:                      26
% 7.98/1.49  prop_fast_solver_calls:                 708
% 7.98/1.49  smt_solver_calls:                       0
% 7.98/1.49  smt_fast_solver_calls:                  0
% 7.98/1.49  prop_num_of_clauses:                    9127
% 7.98/1.49  prop_preprocess_simplified:             16396
% 7.98/1.49  prop_fo_subsumed:                       24
% 7.98/1.49  prop_solver_time:                       0.
% 7.98/1.49  smt_solver_time:                        0.
% 7.98/1.49  smt_fast_solver_time:                   0.
% 7.98/1.49  prop_fast_solver_time:                  0.
% 7.98/1.49  prop_unsat_core_time:                   0.
% 7.98/1.49  
% 7.98/1.49  ------ QBF
% 7.98/1.49  
% 7.98/1.49  qbf_q_res:                              0
% 7.98/1.49  qbf_num_tautologies:                    0
% 7.98/1.49  qbf_prep_cycles:                        0
% 7.98/1.49  
% 7.98/1.49  ------ BMC1
% 7.98/1.49  
% 7.98/1.49  bmc1_current_bound:                     -1
% 7.98/1.49  bmc1_last_solved_bound:                 -1
% 7.98/1.49  bmc1_unsat_core_size:                   -1
% 7.98/1.49  bmc1_unsat_core_parents_size:           -1
% 7.98/1.49  bmc1_merge_next_fun:                    0
% 7.98/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.98/1.49  
% 7.98/1.49  ------ Instantiation
% 7.98/1.49  
% 7.98/1.49  inst_num_of_clauses:                    2543
% 7.98/1.49  inst_num_in_passive:                    851
% 7.98/1.49  inst_num_in_active:                     868
% 7.98/1.49  inst_num_in_unprocessed:                830
% 7.98/1.49  inst_num_of_loops:                      1020
% 7.98/1.49  inst_num_of_learning_restarts:          0
% 7.98/1.49  inst_num_moves_active_passive:          151
% 7.98/1.49  inst_lit_activity:                      0
% 7.98/1.49  inst_lit_activity_moves:                0
% 7.98/1.49  inst_num_tautologies:                   0
% 7.98/1.49  inst_num_prop_implied:                  0
% 7.98/1.49  inst_num_existing_simplified:           0
% 7.98/1.49  inst_num_eq_res_simplified:             0
% 7.98/1.49  inst_num_child_elim:                    0
% 7.98/1.49  inst_num_of_dismatching_blockings:      2485
% 7.98/1.49  inst_num_of_non_proper_insts:           3595
% 7.98/1.49  inst_num_of_duplicates:                 0
% 7.98/1.49  inst_inst_num_from_inst_to_res:         0
% 7.98/1.49  inst_dismatching_checking_time:         0.
% 7.98/1.49  
% 7.98/1.49  ------ Resolution
% 7.98/1.49  
% 7.98/1.49  res_num_of_clauses:                     0
% 7.98/1.49  res_num_in_passive:                     0
% 7.98/1.49  res_num_in_active:                      0
% 7.98/1.49  res_num_of_loops:                       65
% 7.98/1.49  res_forward_subset_subsumed:            391
% 7.98/1.49  res_backward_subset_subsumed:           26
% 7.98/1.49  res_forward_subsumed:                   0
% 7.98/1.49  res_backward_subsumed:                  0
% 7.98/1.49  res_forward_subsumption_resolution:     0
% 7.98/1.49  res_backward_subsumption_resolution:    0
% 7.98/1.49  res_clause_to_clause_subsumption:       6699
% 7.98/1.49  res_orphan_elimination:                 0
% 7.98/1.49  res_tautology_del:                      209
% 7.98/1.49  res_num_eq_res_simplified:              0
% 7.98/1.49  res_num_sel_changes:                    0
% 7.98/1.49  res_moves_from_active_to_pass:          0
% 7.98/1.49  
% 7.98/1.49  ------ Superposition
% 7.98/1.49  
% 7.98/1.49  sup_time_total:                         0.
% 7.98/1.49  sup_time_generating:                    0.
% 7.98/1.49  sup_time_sim_full:                      0.
% 7.98/1.49  sup_time_sim_immed:                     0.
% 7.98/1.49  
% 7.98/1.49  sup_num_of_clauses:                     525
% 7.98/1.49  sup_num_in_active:                      126
% 7.98/1.49  sup_num_in_passive:                     399
% 7.98/1.49  sup_num_of_loops:                       203
% 7.98/1.49  sup_fw_superposition:                   2490
% 7.98/1.49  sup_bw_superposition:                   3021
% 7.98/1.49  sup_immediate_simplified:               2996
% 7.98/1.49  sup_given_eliminated:                   2
% 7.98/1.49  comparisons_done:                       0
% 7.98/1.49  comparisons_avoided:                    0
% 7.98/1.49  
% 7.98/1.49  ------ Simplifications
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  sim_fw_subset_subsumed:                 28
% 7.98/1.49  sim_bw_subset_subsumed:                 0
% 7.98/1.49  sim_fw_subsumed:                        732
% 7.98/1.49  sim_bw_subsumed:                        39
% 7.98/1.49  sim_fw_subsumption_res:                 0
% 7.98/1.49  sim_bw_subsumption_res:                 0
% 7.98/1.49  sim_tautology_del:                      13
% 7.98/1.49  sim_eq_tautology_del:                   672
% 7.98/1.49  sim_eq_res_simp:                        0
% 7.98/1.49  sim_fw_demodulated:                     2657
% 7.98/1.49  sim_bw_demodulated:                     63
% 7.98/1.49  sim_light_normalised:                   1367
% 7.98/1.49  sim_joinable_taut:                      0
% 7.98/1.49  sim_joinable_simp:                      0
% 7.98/1.49  sim_ac_normalised:                      0
% 7.98/1.49  sim_smt_subsumption:                    0
% 7.98/1.49  
%------------------------------------------------------------------------------
