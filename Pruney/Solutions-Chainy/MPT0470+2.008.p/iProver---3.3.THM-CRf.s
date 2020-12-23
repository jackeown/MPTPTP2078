%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:56 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 203 expanded)
%              Number of clauses        :   51 (  85 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  239 ( 464 expanded)
%              Number of equality atoms :  145 ( 258 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f27])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_374,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_375,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_624,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_375])).

cnf(c_13,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_638,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_624,c_13])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_30,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_32,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_7,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_33,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1021,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_32,c_33])).

cnf(c_1022,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1021])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_379,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1028,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1022,c_379])).

cnf(c_1033,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_374,c_1028])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_377,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1050,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_377])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1062,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1050,c_4])).

cnf(c_17,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_728,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_729,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_1321,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_17,c_32,c_33,c_729])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_381,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_839,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_379,c_381])).

cnf(c_1327,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1321,c_839])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_5346,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1327,c_15])).

cnf(c_5347,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5346])).

cnf(c_378,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_376,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1176,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_376])).

cnf(c_1199,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1176,c_14])).

cnf(c_1925,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1199,c_32,c_33])).

cnf(c_1926,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1925])).

cnf(c_1932,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1926,c_379])).

cnf(c_1937,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_374,c_1932])).

cnf(c_2009,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_377])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2030,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2009,c_5])).

cnf(c_2258,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_839])).

cnf(c_2576,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_378,c_2258])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5347,c_2576,c_33,c_32,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:19:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.71/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/0.98  
% 1.71/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.71/0.98  
% 1.71/0.98  ------  iProver source info
% 1.71/0.98  
% 1.71/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.71/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.71/0.98  git: non_committed_changes: false
% 1.71/0.98  git: last_make_outside_of_git: false
% 1.71/0.98  
% 1.71/0.98  ------ 
% 1.71/0.98  
% 1.71/0.98  ------ Input Options
% 1.71/0.98  
% 1.71/0.98  --out_options                           all
% 1.71/0.98  --tptp_safe_out                         true
% 1.71/0.98  --problem_path                          ""
% 1.71/0.98  --include_path                          ""
% 1.71/0.98  --clausifier                            res/vclausify_rel
% 1.71/0.98  --clausifier_options                    --mode clausify
% 1.71/0.98  --stdin                                 false
% 1.71/0.98  --stats_out                             all
% 1.71/0.98  
% 1.71/0.98  ------ General Options
% 1.71/0.98  
% 1.71/0.98  --fof                                   false
% 1.71/0.98  --time_out_real                         305.
% 1.71/0.98  --time_out_virtual                      -1.
% 1.71/0.98  --symbol_type_check                     false
% 1.71/0.98  --clausify_out                          false
% 1.71/0.98  --sig_cnt_out                           false
% 1.71/0.98  --trig_cnt_out                          false
% 1.71/0.98  --trig_cnt_out_tolerance                1.
% 1.71/0.98  --trig_cnt_out_sk_spl                   false
% 1.71/0.98  --abstr_cl_out                          false
% 1.71/0.98  
% 1.71/0.98  ------ Global Options
% 1.71/0.98  
% 1.71/0.98  --schedule                              default
% 1.71/0.98  --add_important_lit                     false
% 1.71/0.98  --prop_solver_per_cl                    1000
% 1.71/0.98  --min_unsat_core                        false
% 1.71/0.98  --soft_assumptions                      false
% 1.71/0.98  --soft_lemma_size                       3
% 1.71/0.98  --prop_impl_unit_size                   0
% 1.71/0.98  --prop_impl_unit                        []
% 1.71/0.98  --share_sel_clauses                     true
% 1.71/0.98  --reset_solvers                         false
% 1.71/0.98  --bc_imp_inh                            [conj_cone]
% 1.71/0.98  --conj_cone_tolerance                   3.
% 1.71/0.98  --extra_neg_conj                        none
% 1.71/0.98  --large_theory_mode                     true
% 1.71/0.98  --prolific_symb_bound                   200
% 1.71/0.98  --lt_threshold                          2000
% 1.71/0.98  --clause_weak_htbl                      true
% 1.71/0.98  --gc_record_bc_elim                     false
% 1.71/0.98  
% 1.71/0.98  ------ Preprocessing Options
% 1.71/0.98  
% 1.71/0.98  --preprocessing_flag                    true
% 1.71/0.98  --time_out_prep_mult                    0.1
% 1.71/0.98  --splitting_mode                        input
% 1.71/0.98  --splitting_grd                         true
% 1.71/0.98  --splitting_cvd                         false
% 1.71/0.98  --splitting_cvd_svl                     false
% 1.71/0.98  --splitting_nvd                         32
% 1.71/0.98  --sub_typing                            true
% 1.71/0.98  --prep_gs_sim                           true
% 1.71/0.98  --prep_unflatten                        true
% 1.71/0.98  --prep_res_sim                          true
% 1.71/0.98  --prep_upred                            true
% 1.71/0.98  --prep_sem_filter                       exhaustive
% 1.71/0.98  --prep_sem_filter_out                   false
% 1.71/0.98  --pred_elim                             true
% 1.71/0.98  --res_sim_input                         true
% 1.71/0.98  --eq_ax_congr_red                       true
% 1.71/0.98  --pure_diseq_elim                       true
% 1.71/0.98  --brand_transform                       false
% 1.71/0.98  --non_eq_to_eq                          false
% 1.71/0.98  --prep_def_merge                        true
% 1.71/0.98  --prep_def_merge_prop_impl              false
% 1.71/0.98  --prep_def_merge_mbd                    true
% 1.71/0.98  --prep_def_merge_tr_red                 false
% 1.71/0.98  --prep_def_merge_tr_cl                  false
% 1.71/0.98  --smt_preprocessing                     true
% 1.71/0.98  --smt_ac_axioms                         fast
% 1.71/0.98  --preprocessed_out                      false
% 1.71/0.98  --preprocessed_stats                    false
% 1.71/0.98  
% 1.71/0.98  ------ Abstraction refinement Options
% 1.71/0.98  
% 1.71/0.98  --abstr_ref                             []
% 1.71/0.98  --abstr_ref_prep                        false
% 1.71/0.98  --abstr_ref_until_sat                   false
% 1.71/0.98  --abstr_ref_sig_restrict                funpre
% 1.71/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/0.98  --abstr_ref_under                       []
% 1.71/0.98  
% 1.71/0.98  ------ SAT Options
% 1.71/0.98  
% 1.71/0.98  --sat_mode                              false
% 1.71/0.98  --sat_fm_restart_options                ""
% 1.71/0.98  --sat_gr_def                            false
% 1.71/0.98  --sat_epr_types                         true
% 1.71/0.98  --sat_non_cyclic_types                  false
% 1.71/0.98  --sat_finite_models                     false
% 1.71/0.98  --sat_fm_lemmas                         false
% 1.71/0.98  --sat_fm_prep                           false
% 1.71/0.98  --sat_fm_uc_incr                        true
% 1.71/0.98  --sat_out_model                         small
% 1.71/0.98  --sat_out_clauses                       false
% 1.71/0.98  
% 1.71/0.98  ------ QBF Options
% 1.71/0.98  
% 1.71/0.98  --qbf_mode                              false
% 1.71/0.98  --qbf_elim_univ                         false
% 1.71/0.98  --qbf_dom_inst                          none
% 1.71/0.98  --qbf_dom_pre_inst                      false
% 1.71/0.98  --qbf_sk_in                             false
% 1.71/0.98  --qbf_pred_elim                         true
% 1.71/0.98  --qbf_split                             512
% 1.71/0.98  
% 1.71/0.98  ------ BMC1 Options
% 1.71/0.98  
% 1.71/0.98  --bmc1_incremental                      false
% 1.71/0.98  --bmc1_axioms                           reachable_all
% 1.71/0.98  --bmc1_min_bound                        0
% 1.71/0.98  --bmc1_max_bound                        -1
% 1.71/0.98  --bmc1_max_bound_default                -1
% 1.71/0.98  --bmc1_symbol_reachability              true
% 1.71/0.98  --bmc1_property_lemmas                  false
% 1.71/0.98  --bmc1_k_induction                      false
% 1.71/0.98  --bmc1_non_equiv_states                 false
% 1.71/0.98  --bmc1_deadlock                         false
% 1.71/0.98  --bmc1_ucm                              false
% 1.71/0.98  --bmc1_add_unsat_core                   none
% 1.71/0.98  --bmc1_unsat_core_children              false
% 1.71/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/0.98  --bmc1_out_stat                         full
% 1.71/0.98  --bmc1_ground_init                      false
% 1.71/0.98  --bmc1_pre_inst_next_state              false
% 1.71/0.98  --bmc1_pre_inst_state                   false
% 1.71/0.98  --bmc1_pre_inst_reach_state             false
% 1.71/0.98  --bmc1_out_unsat_core                   false
% 1.71/0.98  --bmc1_aig_witness_out                  false
% 1.71/0.98  --bmc1_verbose                          false
% 1.71/0.98  --bmc1_dump_clauses_tptp                false
% 1.71/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.71/0.98  --bmc1_dump_file                        -
% 1.71/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.71/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.71/0.98  --bmc1_ucm_extend_mode                  1
% 1.71/0.98  --bmc1_ucm_init_mode                    2
% 1.71/0.98  --bmc1_ucm_cone_mode                    none
% 1.71/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.71/0.98  --bmc1_ucm_relax_model                  4
% 1.71/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.71/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/0.98  --bmc1_ucm_layered_model                none
% 1.71/0.98  --bmc1_ucm_max_lemma_size               10
% 1.71/0.98  
% 1.71/0.98  ------ AIG Options
% 1.71/0.98  
% 1.71/0.98  --aig_mode                              false
% 1.71/0.98  
% 1.71/0.98  ------ Instantiation Options
% 1.71/0.98  
% 1.71/0.98  --instantiation_flag                    true
% 1.71/0.98  --inst_sos_flag                         false
% 1.71/0.98  --inst_sos_phase                        true
% 1.71/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/0.98  --inst_lit_sel_side                     num_symb
% 1.71/0.98  --inst_solver_per_active                1400
% 1.71/0.98  --inst_solver_calls_frac                1.
% 1.71/0.98  --inst_passive_queue_type               priority_queues
% 1.71/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/0.98  --inst_passive_queues_freq              [25;2]
% 1.71/0.98  --inst_dismatching                      true
% 1.71/0.98  --inst_eager_unprocessed_to_passive     true
% 1.71/0.98  --inst_prop_sim_given                   true
% 1.71/0.98  --inst_prop_sim_new                     false
% 1.71/0.98  --inst_subs_new                         false
% 1.71/0.98  --inst_eq_res_simp                      false
% 1.71/0.98  --inst_subs_given                       false
% 1.71/0.98  --inst_orphan_elimination               true
% 1.71/0.98  --inst_learning_loop_flag               true
% 1.71/0.98  --inst_learning_start                   3000
% 1.71/0.98  --inst_learning_factor                  2
% 1.71/0.98  --inst_start_prop_sim_after_learn       3
% 1.71/0.98  --inst_sel_renew                        solver
% 1.71/0.98  --inst_lit_activity_flag                true
% 1.71/0.98  --inst_restr_to_given                   false
% 1.71/0.98  --inst_activity_threshold               500
% 1.71/0.98  --inst_out_proof                        true
% 1.71/0.98  
% 1.71/0.98  ------ Resolution Options
% 1.71/0.98  
% 1.71/0.98  --resolution_flag                       true
% 1.71/0.98  --res_lit_sel                           adaptive
% 1.71/0.98  --res_lit_sel_side                      none
% 1.71/0.98  --res_ordering                          kbo
% 1.71/0.98  --res_to_prop_solver                    active
% 1.71/0.98  --res_prop_simpl_new                    false
% 1.71/0.98  --res_prop_simpl_given                  true
% 1.71/0.98  --res_passive_queue_type                priority_queues
% 1.71/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/0.98  --res_passive_queues_freq               [15;5]
% 1.71/0.98  --res_forward_subs                      full
% 1.71/0.98  --res_backward_subs                     full
% 1.71/0.98  --res_forward_subs_resolution           true
% 1.71/0.98  --res_backward_subs_resolution          true
% 1.71/0.98  --res_orphan_elimination                true
% 1.71/0.98  --res_time_limit                        2.
% 1.71/0.98  --res_out_proof                         true
% 1.71/0.98  
% 1.71/0.98  ------ Superposition Options
% 1.71/0.98  
% 1.71/0.98  --superposition_flag                    true
% 1.71/0.98  --sup_passive_queue_type                priority_queues
% 1.71/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.71/0.98  --demod_completeness_check              fast
% 1.71/0.98  --demod_use_ground                      true
% 1.71/0.98  --sup_to_prop_solver                    passive
% 1.71/0.98  --sup_prop_simpl_new                    true
% 1.71/0.98  --sup_prop_simpl_given                  true
% 1.71/0.98  --sup_fun_splitting                     false
% 1.71/0.98  --sup_smt_interval                      50000
% 1.71/0.98  
% 1.71/0.98  ------ Superposition Simplification Setup
% 1.71/0.98  
% 1.71/0.98  --sup_indices_passive                   []
% 1.71/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.98  --sup_full_bw                           [BwDemod]
% 1.71/0.98  --sup_immed_triv                        [TrivRules]
% 1.71/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.98  --sup_immed_bw_main                     []
% 1.71/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.98  
% 1.71/0.98  ------ Combination Options
% 1.71/0.98  
% 1.71/0.98  --comb_res_mult                         3
% 1.71/0.98  --comb_sup_mult                         2
% 1.71/0.98  --comb_inst_mult                        10
% 1.71/0.98  
% 1.71/0.98  ------ Debug Options
% 1.71/0.98  
% 1.71/0.98  --dbg_backtrace                         false
% 1.71/0.98  --dbg_dump_prop_clauses                 false
% 1.71/0.98  --dbg_dump_prop_clauses_file            -
% 1.71/0.98  --dbg_out_stat                          false
% 1.71/0.98  ------ Parsing...
% 1.71/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.71/0.98  
% 1.71/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.71/0.98  
% 1.71/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.71/0.98  
% 1.71/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.71/0.98  ------ Proving...
% 1.71/0.98  ------ Problem Properties 
% 1.71/0.98  
% 1.71/0.98  
% 1.71/0.98  clauses                                 15
% 1.71/0.98  conjectures                             2
% 1.71/0.98  EPR                                     5
% 1.71/0.98  Horn                                    14
% 1.71/0.98  unary                                   8
% 1.71/0.98  binary                                  2
% 1.71/0.98  lits                                    29
% 1.71/0.98  lits eq                                 12
% 1.71/0.98  fd_pure                                 0
% 1.71/0.98  fd_pseudo                               0
% 1.71/0.98  fd_cond                                 1
% 1.71/0.98  fd_pseudo_cond                          1
% 1.71/0.98  AC symbols                              0
% 1.71/0.98  
% 1.71/0.98  ------ Schedule dynamic 5 is on 
% 1.71/0.98  
% 1.71/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.71/0.98  
% 1.71/0.98  
% 1.71/0.98  ------ 
% 1.71/0.98  Current options:
% 1.71/0.98  ------ 
% 1.71/0.98  
% 1.71/0.98  ------ Input Options
% 1.71/0.98  
% 1.71/0.98  --out_options                           all
% 1.71/0.98  --tptp_safe_out                         true
% 1.71/0.98  --problem_path                          ""
% 1.71/0.98  --include_path                          ""
% 1.71/0.98  --clausifier                            res/vclausify_rel
% 1.71/0.98  --clausifier_options                    --mode clausify
% 1.71/0.98  --stdin                                 false
% 1.71/0.98  --stats_out                             all
% 1.71/0.98  
% 1.71/0.98  ------ General Options
% 1.71/0.98  
% 1.71/0.98  --fof                                   false
% 1.71/0.98  --time_out_real                         305.
% 1.71/0.98  --time_out_virtual                      -1.
% 1.71/0.98  --symbol_type_check                     false
% 1.71/0.98  --clausify_out                          false
% 1.71/0.98  --sig_cnt_out                           false
% 1.71/0.98  --trig_cnt_out                          false
% 1.71/0.98  --trig_cnt_out_tolerance                1.
% 1.71/0.98  --trig_cnt_out_sk_spl                   false
% 1.71/0.98  --abstr_cl_out                          false
% 1.71/0.98  
% 1.71/0.98  ------ Global Options
% 1.71/0.98  
% 1.71/0.98  --schedule                              default
% 1.71/0.98  --add_important_lit                     false
% 1.71/0.98  --prop_solver_per_cl                    1000
% 1.71/0.98  --min_unsat_core                        false
% 1.71/0.98  --soft_assumptions                      false
% 1.71/0.98  --soft_lemma_size                       3
% 1.71/0.98  --prop_impl_unit_size                   0
% 1.71/0.98  --prop_impl_unit                        []
% 1.71/0.98  --share_sel_clauses                     true
% 1.71/0.98  --reset_solvers                         false
% 1.71/0.98  --bc_imp_inh                            [conj_cone]
% 1.71/0.98  --conj_cone_tolerance                   3.
% 1.71/0.98  --extra_neg_conj                        none
% 1.71/0.98  --large_theory_mode                     true
% 1.71/0.98  --prolific_symb_bound                   200
% 1.71/0.98  --lt_threshold                          2000
% 1.71/0.98  --clause_weak_htbl                      true
% 1.71/0.98  --gc_record_bc_elim                     false
% 1.71/0.98  
% 1.71/0.98  ------ Preprocessing Options
% 1.71/0.98  
% 1.71/0.98  --preprocessing_flag                    true
% 1.71/0.98  --time_out_prep_mult                    0.1
% 1.71/0.98  --splitting_mode                        input
% 1.71/0.98  --splitting_grd                         true
% 1.71/0.98  --splitting_cvd                         false
% 1.71/0.98  --splitting_cvd_svl                     false
% 1.71/0.98  --splitting_nvd                         32
% 1.71/0.98  --sub_typing                            true
% 1.71/0.98  --prep_gs_sim                           true
% 1.71/0.98  --prep_unflatten                        true
% 1.71/0.98  --prep_res_sim                          true
% 1.71/0.98  --prep_upred                            true
% 1.71/0.98  --prep_sem_filter                       exhaustive
% 1.71/0.98  --prep_sem_filter_out                   false
% 1.71/0.98  --pred_elim                             true
% 1.71/0.98  --res_sim_input                         true
% 1.71/0.98  --eq_ax_congr_red                       true
% 1.71/0.98  --pure_diseq_elim                       true
% 1.71/0.98  --brand_transform                       false
% 1.71/0.98  --non_eq_to_eq                          false
% 1.71/0.98  --prep_def_merge                        true
% 1.71/0.98  --prep_def_merge_prop_impl              false
% 1.71/0.98  --prep_def_merge_mbd                    true
% 1.71/0.98  --prep_def_merge_tr_red                 false
% 1.71/0.98  --prep_def_merge_tr_cl                  false
% 1.71/0.98  --smt_preprocessing                     true
% 1.71/0.98  --smt_ac_axioms                         fast
% 1.71/0.98  --preprocessed_out                      false
% 1.71/0.98  --preprocessed_stats                    false
% 1.71/0.98  
% 1.71/0.98  ------ Abstraction refinement Options
% 1.71/0.98  
% 1.71/0.98  --abstr_ref                             []
% 1.71/0.98  --abstr_ref_prep                        false
% 1.71/0.98  --abstr_ref_until_sat                   false
% 1.71/0.98  --abstr_ref_sig_restrict                funpre
% 1.71/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/0.98  --abstr_ref_under                       []
% 1.71/0.98  
% 1.71/0.98  ------ SAT Options
% 1.71/0.98  
% 1.71/0.98  --sat_mode                              false
% 1.71/0.98  --sat_fm_restart_options                ""
% 1.71/0.98  --sat_gr_def                            false
% 1.71/0.98  --sat_epr_types                         true
% 1.71/0.98  --sat_non_cyclic_types                  false
% 1.71/0.98  --sat_finite_models                     false
% 1.71/0.98  --sat_fm_lemmas                         false
% 1.71/0.98  --sat_fm_prep                           false
% 1.71/0.98  --sat_fm_uc_incr                        true
% 1.71/0.98  --sat_out_model                         small
% 1.71/0.98  --sat_out_clauses                       false
% 1.71/0.98  
% 1.71/0.98  ------ QBF Options
% 1.71/0.98  
% 1.71/0.98  --qbf_mode                              false
% 1.71/0.98  --qbf_elim_univ                         false
% 1.71/0.98  --qbf_dom_inst                          none
% 1.71/0.98  --qbf_dom_pre_inst                      false
% 1.71/0.98  --qbf_sk_in                             false
% 1.71/0.98  --qbf_pred_elim                         true
% 1.71/0.98  --qbf_split                             512
% 1.71/0.98  
% 1.71/0.98  ------ BMC1 Options
% 1.71/0.98  
% 1.71/0.98  --bmc1_incremental                      false
% 1.71/0.98  --bmc1_axioms                           reachable_all
% 1.71/0.98  --bmc1_min_bound                        0
% 1.71/0.98  --bmc1_max_bound                        -1
% 1.71/0.98  --bmc1_max_bound_default                -1
% 1.71/0.98  --bmc1_symbol_reachability              true
% 1.71/0.98  --bmc1_property_lemmas                  false
% 1.71/0.98  --bmc1_k_induction                      false
% 1.71/0.98  --bmc1_non_equiv_states                 false
% 1.71/0.98  --bmc1_deadlock                         false
% 1.71/0.98  --bmc1_ucm                              false
% 1.71/0.98  --bmc1_add_unsat_core                   none
% 1.71/0.98  --bmc1_unsat_core_children              false
% 1.71/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/0.98  --bmc1_out_stat                         full
% 1.71/0.98  --bmc1_ground_init                      false
% 1.71/0.98  --bmc1_pre_inst_next_state              false
% 1.71/0.98  --bmc1_pre_inst_state                   false
% 1.71/0.98  --bmc1_pre_inst_reach_state             false
% 1.71/0.98  --bmc1_out_unsat_core                   false
% 1.71/0.98  --bmc1_aig_witness_out                  false
% 1.71/0.98  --bmc1_verbose                          false
% 1.71/0.98  --bmc1_dump_clauses_tptp                false
% 1.71/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.71/0.98  --bmc1_dump_file                        -
% 1.71/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.71/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.71/0.98  --bmc1_ucm_extend_mode                  1
% 1.71/0.99  --bmc1_ucm_init_mode                    2
% 1.71/0.99  --bmc1_ucm_cone_mode                    none
% 1.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.71/0.99  --bmc1_ucm_relax_model                  4
% 1.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/0.99  --bmc1_ucm_layered_model                none
% 1.71/0.99  --bmc1_ucm_max_lemma_size               10
% 1.71/0.99  
% 1.71/0.99  ------ AIG Options
% 1.71/0.99  
% 1.71/0.99  --aig_mode                              false
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation Options
% 1.71/0.99  
% 1.71/0.99  --instantiation_flag                    true
% 1.71/0.99  --inst_sos_flag                         false
% 1.71/0.99  --inst_sos_phase                        true
% 1.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel_side                     none
% 1.71/0.99  --inst_solver_per_active                1400
% 1.71/0.99  --inst_solver_calls_frac                1.
% 1.71/0.99  --inst_passive_queue_type               priority_queues
% 1.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/0.99  --inst_passive_queues_freq              [25;2]
% 1.71/0.99  --inst_dismatching                      true
% 1.71/0.99  --inst_eager_unprocessed_to_passive     true
% 1.71/0.99  --inst_prop_sim_given                   true
% 1.71/0.99  --inst_prop_sim_new                     false
% 1.71/0.99  --inst_subs_new                         false
% 1.71/0.99  --inst_eq_res_simp                      false
% 1.71/0.99  --inst_subs_given                       false
% 1.71/0.99  --inst_orphan_elimination               true
% 1.71/0.99  --inst_learning_loop_flag               true
% 1.71/0.99  --inst_learning_start                   3000
% 1.71/0.99  --inst_learning_factor                  2
% 1.71/0.99  --inst_start_prop_sim_after_learn       3
% 1.71/0.99  --inst_sel_renew                        solver
% 1.71/0.99  --inst_lit_activity_flag                true
% 1.71/0.99  --inst_restr_to_given                   false
% 1.71/0.99  --inst_activity_threshold               500
% 1.71/0.99  --inst_out_proof                        true
% 1.71/0.99  
% 1.71/0.99  ------ Resolution Options
% 1.71/0.99  
% 1.71/0.99  --resolution_flag                       false
% 1.71/0.99  --res_lit_sel                           adaptive
% 1.71/0.99  --res_lit_sel_side                      none
% 1.71/0.99  --res_ordering                          kbo
% 1.71/0.99  --res_to_prop_solver                    active
% 1.71/0.99  --res_prop_simpl_new                    false
% 1.71/0.99  --res_prop_simpl_given                  true
% 1.71/0.99  --res_passive_queue_type                priority_queues
% 1.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/0.99  --res_passive_queues_freq               [15;5]
% 1.71/0.99  --res_forward_subs                      full
% 1.71/0.99  --res_backward_subs                     full
% 1.71/0.99  --res_forward_subs_resolution           true
% 1.71/0.99  --res_backward_subs_resolution          true
% 1.71/0.99  --res_orphan_elimination                true
% 1.71/0.99  --res_time_limit                        2.
% 1.71/0.99  --res_out_proof                         true
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Options
% 1.71/0.99  
% 1.71/0.99  --superposition_flag                    true
% 1.71/0.99  --sup_passive_queue_type                priority_queues
% 1.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.71/0.99  --demod_completeness_check              fast
% 1.71/0.99  --demod_use_ground                      true
% 1.71/0.99  --sup_to_prop_solver                    passive
% 1.71/0.99  --sup_prop_simpl_new                    true
% 1.71/0.99  --sup_prop_simpl_given                  true
% 1.71/0.99  --sup_fun_splitting                     false
% 1.71/0.99  --sup_smt_interval                      50000
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Simplification Setup
% 1.71/0.99  
% 1.71/0.99  --sup_indices_passive                   []
% 1.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_full_bw                           [BwDemod]
% 1.71/0.99  --sup_immed_triv                        [TrivRules]
% 1.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_immed_bw_main                     []
% 1.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  
% 1.71/0.99  ------ Combination Options
% 1.71/0.99  
% 1.71/0.99  --comb_res_mult                         3
% 1.71/0.99  --comb_sup_mult                         2
% 1.71/0.99  --comb_inst_mult                        10
% 1.71/0.99  
% 1.71/0.99  ------ Debug Options
% 1.71/0.99  
% 1.71/0.99  --dbg_backtrace                         false
% 1.71/0.99  --dbg_dump_prop_clauses                 false
% 1.71/0.99  --dbg_dump_prop_clauses_file            -
% 1.71/0.99  --dbg_out_stat                          false
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  ------ Proving...
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  % SZS status Theorem for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  fof(f12,conjecture,(
% 1.71/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f13,negated_conjecture,(
% 1.71/0.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.71/0.99    inference(negated_conjecture,[],[f12])).
% 1.71/0.99  
% 1.71/0.99  fof(f22,plain,(
% 1.71/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.71/0.99    inference(ennf_transformation,[],[f13])).
% 1.71/0.99  
% 1.71/0.99  fof(f27,plain,(
% 1.71/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f28,plain,(
% 1.71/0.99    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f27])).
% 1.71/0.99  
% 1.71/0.99  fof(f45,plain,(
% 1.71/0.99    v1_relat_1(sK0)),
% 1.71/0.99    inference(cnf_transformation,[],[f28])).
% 1.71/0.99  
% 1.71/0.99  fof(f11,axiom,(
% 1.71/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f43,plain,(
% 1.71/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.71/0.99    inference(cnf_transformation,[],[f11])).
% 1.71/0.99  
% 1.71/0.99  fof(f10,axiom,(
% 1.71/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f20,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(ennf_transformation,[],[f10])).
% 1.71/0.99  
% 1.71/0.99  fof(f21,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(flattening,[],[f20])).
% 1.71/0.99  
% 1.71/0.99  fof(f42,plain,(
% 1.71/0.99    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f21])).
% 1.71/0.99  
% 1.71/0.99  fof(f44,plain,(
% 1.71/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.71/0.99    inference(cnf_transformation,[],[f11])).
% 1.71/0.99  
% 1.71/0.99  fof(f6,axiom,(
% 1.71/0.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f14,plain,(
% 1.71/0.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.71/0.99    inference(ennf_transformation,[],[f6])).
% 1.71/0.99  
% 1.71/0.99  fof(f38,plain,(
% 1.71/0.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f14])).
% 1.71/0.99  
% 1.71/0.99  fof(f5,axiom,(
% 1.71/0.99    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f37,plain,(
% 1.71/0.99    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 1.71/0.99    inference(cnf_transformation,[],[f5])).
% 1.71/0.99  
% 1.71/0.99  fof(f4,axiom,(
% 1.71/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f36,plain,(
% 1.71/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f4])).
% 1.71/0.99  
% 1.71/0.99  fof(f47,plain,(
% 1.71/0.99    v1_xboole_0(k1_xboole_0)),
% 1.71/0.99    inference(definition_unfolding,[],[f37,f36])).
% 1.71/0.99  
% 1.71/0.99  fof(f2,axiom,(
% 1.71/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f32,plain,(
% 1.71/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f2])).
% 1.71/0.99  
% 1.71/0.99  fof(f8,axiom,(
% 1.71/0.99    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f17,plain,(
% 1.71/0.99    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(ennf_transformation,[],[f8])).
% 1.71/0.99  
% 1.71/0.99  fof(f40,plain,(
% 1.71/0.99    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f17])).
% 1.71/0.99  
% 1.71/0.99  fof(f3,axiom,(
% 1.71/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f25,plain,(
% 1.71/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.99    inference(nnf_transformation,[],[f3])).
% 1.71/0.99  
% 1.71/0.99  fof(f26,plain,(
% 1.71/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.99    inference(flattening,[],[f25])).
% 1.71/0.99  
% 1.71/0.99  fof(f35,plain,(
% 1.71/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.71/0.99    inference(cnf_transformation,[],[f26])).
% 1.71/0.99  
% 1.71/0.99  fof(f50,plain,(
% 1.71/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.71/0.99    inference(equality_resolution,[],[f35])).
% 1.71/0.99  
% 1.71/0.99  fof(f7,axiom,(
% 1.71/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f15,plain,(
% 1.71/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f7])).
% 1.71/0.99  
% 1.71/0.99  fof(f16,plain,(
% 1.71/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(flattening,[],[f15])).
% 1.71/0.99  
% 1.71/0.99  fof(f39,plain,(
% 1.71/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f16])).
% 1.71/0.99  
% 1.71/0.99  fof(f1,axiom,(
% 1.71/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f23,plain,(
% 1.71/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.99    inference(nnf_transformation,[],[f1])).
% 1.71/0.99  
% 1.71/0.99  fof(f24,plain,(
% 1.71/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.99    inference(flattening,[],[f23])).
% 1.71/0.99  
% 1.71/0.99  fof(f31,plain,(
% 1.71/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f24])).
% 1.71/0.99  
% 1.71/0.99  fof(f46,plain,(
% 1.71/0.99    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.71/0.99    inference(cnf_transformation,[],[f28])).
% 1.71/0.99  
% 1.71/0.99  fof(f9,axiom,(
% 1.71/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f18,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(ennf_transformation,[],[f9])).
% 1.71/0.99  
% 1.71/0.99  fof(f19,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(flattening,[],[f18])).
% 1.71/0.99  
% 1.71/0.99  fof(f41,plain,(
% 1.71/0.99    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f19])).
% 1.71/0.99  
% 1.71/0.99  fof(f34,plain,(
% 1.71/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.71/0.99    inference(cnf_transformation,[],[f26])).
% 1.71/0.99  
% 1.71/0.99  fof(f51,plain,(
% 1.71/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.71/0.99    inference(equality_resolution,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  cnf(c_16,negated_conjecture,
% 1.71/0.99      ( v1_relat_1(sK0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_374,plain,
% 1.71/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_14,plain,
% 1.71/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_12,plain,
% 1.71/0.99      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 1.71/0.99      | ~ v1_relat_1(X1)
% 1.71/0.99      | ~ v1_relat_1(X0)
% 1.71/0.99      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_375,plain,
% 1.71/0.99      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 1.71/0.99      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 1.71/0.99      | v1_relat_1(X0) != iProver_top
% 1.71/0.99      | v1_relat_1(X1) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_624,plain,
% 1.71/0.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 1.71/0.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 1.71/0.99      | v1_relat_1(X0) != iProver_top
% 1.71/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_14,c_375]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_13,plain,
% 1.71/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_638,plain,
% 1.71/0.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 1.71/0.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 1.71/0.99      | v1_relat_1(X0) != iProver_top
% 1.71/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.71/0.99      inference(light_normalisation,[status(thm)],[c_624,c_13]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_8,plain,
% 1.71/0.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_30,plain,
% 1.71/0.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_32,plain,
% 1.71/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 1.71/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_7,plain,
% 1.71/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_33,plain,
% 1.71/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1021,plain,
% 1.71/0.99      ( v1_relat_1(X0) != iProver_top
% 1.71/0.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 1.71/0.99      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_638,c_32,c_33]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1022,plain,
% 1.71/0.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 1.71/0.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 1.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_1021]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_3,plain,
% 1.71/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_379,plain,
% 1.71/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1028,plain,
% 1.71/0.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 1.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 1.71/0.99      inference(forward_subsumption_resolution,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_1022,c_379]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1033,plain,
% 1.71/0.99      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_374,c_1028]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_10,plain,
% 1.71/0.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 1.71/0.99      | ~ v1_relat_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_377,plain,
% 1.71/0.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 1.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1050,plain,
% 1.71/0.99      ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) = iProver_top
% 1.71/0.99      | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_1033,c_377]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_4,plain,
% 1.71/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1062,plain,
% 1.71/0.99      ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) = iProver_top
% 1.71/0.99      | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top ),
% 1.71/0.99      inference(demodulation,[status(thm)],[c_1050,c_4]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_17,plain,
% 1.71/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_9,plain,
% 1.71/0.99      ( ~ v1_relat_1(X0)
% 1.71/0.99      | ~ v1_relat_1(X1)
% 1.71/0.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 1.71/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_728,plain,
% 1.71/0.99      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 1.71/0.99      | ~ v1_relat_1(sK0)
% 1.71/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_729,plain,
% 1.71/0.99      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 1.71/0.99      | v1_relat_1(sK0) != iProver_top
% 1.71/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1321,plain,
% 1.71/0.99      ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_1062,c_17,c_32,c_33,c_729]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_0,plain,
% 1.71/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.71/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_381,plain,
% 1.71/0.99      ( X0 = X1
% 1.71/0.99      | r1_tarski(X0,X1) != iProver_top
% 1.71/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_839,plain,
% 1.71/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_379,c_381]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1327,plain,
% 1.71/0.99      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_1321,c_839]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_15,negated_conjecture,
% 1.71/0.99      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 1.71/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_5346,plain,
% 1.71/0.99      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 1.71/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 1.71/0.99      inference(demodulation,[status(thm)],[c_1327,c_15]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_5347,plain,
% 1.71/0.99      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
% 1.71/0.99      inference(equality_resolution_simp,[status(thm)],[c_5346]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_378,plain,
% 1.71/0.99      ( v1_relat_1(X0) != iProver_top
% 1.71/0.99      | v1_relat_1(X1) != iProver_top
% 1.71/0.99      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_11,plain,
% 1.71/0.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 1.71/0.99      | ~ v1_relat_1(X1)
% 1.71/0.99      | ~ v1_relat_1(X0)
% 1.71/0.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_376,plain,
% 1.71/0.99      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 1.71/0.99      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 1.71/0.99      | v1_relat_1(X1) != iProver_top
% 1.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1176,plain,
% 1.71/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 1.71/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 1.71/0.99      | v1_relat_1(X0) != iProver_top
% 1.71/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_13,c_376]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1199,plain,
% 1.71/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 1.71/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 1.71/0.99      | v1_relat_1(X0) != iProver_top
% 1.71/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.71/0.99      inference(light_normalisation,[status(thm)],[c_1176,c_14]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1925,plain,
% 1.71/0.99      ( v1_relat_1(X0) != iProver_top
% 1.71/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 1.71/0.99      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_1199,c_32,c_33]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1926,plain,
% 1.71/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 1.71/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 1.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_1925]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1932,plain,
% 1.71/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 1.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 1.71/0.99      inference(forward_subsumption_resolution,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_1926,c_379]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1937,plain,
% 1.71/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_374,c_1932]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2009,plain,
% 1.71/0.99      ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) = iProver_top
% 1.71/0.99      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_1937,c_377]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_5,plain,
% 1.71/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2030,plain,
% 1.71/0.99      ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) = iProver_top
% 1.71/0.99      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.71/0.99      inference(demodulation,[status(thm)],[c_2009,c_5]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2258,plain,
% 1.71/0.99      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 1.71/0.99      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_2030,c_839]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2576,plain,
% 1.71/0.99      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 1.71/0.99      | v1_relat_1(sK0) != iProver_top
% 1.71/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_378,c_2258]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(contradiction,plain,
% 1.71/0.99      ( $false ),
% 1.71/0.99      inference(minisat,[status(thm)],[c_5347,c_2576,c_33,c_32,c_17]) ).
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  ------                               Statistics
% 1.71/0.99  
% 1.71/0.99  ------ General
% 1.71/0.99  
% 1.71/0.99  abstr_ref_over_cycles:                  0
% 1.71/0.99  abstr_ref_under_cycles:                 0
% 1.71/0.99  gc_basic_clause_elim:                   0
% 1.71/0.99  forced_gc_time:                         0
% 1.71/0.99  parsing_time:                           0.007
% 1.71/0.99  unif_index_cands_time:                  0.
% 1.71/0.99  unif_index_add_time:                    0.
% 1.71/0.99  orderings_time:                         0.
% 1.71/0.99  out_proof_time:                         0.006
% 1.71/0.99  total_time:                             0.191
% 1.71/0.99  num_of_symbols:                         40
% 1.71/0.99  num_of_terms:                           3954
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing
% 1.71/0.99  
% 1.71/0.99  num_of_splits:                          0
% 1.71/0.99  num_of_split_atoms:                     0
% 1.71/0.99  num_of_reused_defs:                     0
% 1.71/0.99  num_eq_ax_congr_red:                    0
% 1.71/0.99  num_of_sem_filtered_clauses:            1
% 1.71/0.99  num_of_subtypes:                        0
% 1.71/0.99  monotx_restored_types:                  0
% 1.71/0.99  sat_num_of_epr_types:                   0
% 1.71/0.99  sat_num_of_non_cyclic_types:            0
% 1.71/0.99  sat_guarded_non_collapsed_types:        0
% 1.71/0.99  num_pure_diseq_elim:                    0
% 1.71/0.99  simp_replaced_by:                       0
% 1.71/0.99  res_preprocessed:                       78
% 1.71/0.99  prep_upred:                             0
% 1.71/0.99  prep_unflattend:                        1
% 1.71/0.99  smt_new_axioms:                         0
% 1.71/0.99  pred_elim_cands:                        2
% 1.71/0.99  pred_elim:                              1
% 1.71/0.99  pred_elim_cl:                           1
% 1.71/0.99  pred_elim_cycles:                       3
% 1.71/0.99  merged_defs:                            0
% 1.71/0.99  merged_defs_ncl:                        0
% 1.71/0.99  bin_hyper_res:                          0
% 1.71/0.99  prep_cycles:                            4
% 1.71/0.99  pred_elim_time:                         0.001
% 1.71/0.99  splitting_time:                         0.
% 1.71/0.99  sem_filter_time:                        0.
% 1.71/0.99  monotx_time:                            0.
% 1.71/0.99  subtype_inf_time:                       0.
% 1.71/0.99  
% 1.71/0.99  ------ Problem properties
% 1.71/0.99  
% 1.71/0.99  clauses:                                15
% 1.71/0.99  conjectures:                            2
% 1.71/0.99  epr:                                    5
% 1.71/0.99  horn:                                   14
% 1.71/0.99  ground:                                 5
% 1.71/0.99  unary:                                  8
% 1.71/0.99  binary:                                 2
% 1.71/0.99  lits:                                   29
% 1.71/0.99  lits_eq:                                12
% 1.71/0.99  fd_pure:                                0
% 1.71/0.99  fd_pseudo:                              0
% 1.71/0.99  fd_cond:                                1
% 1.71/0.99  fd_pseudo_cond:                         1
% 1.71/0.99  ac_symbols:                             0
% 1.71/0.99  
% 1.71/0.99  ------ Propositional Solver
% 1.71/0.99  
% 1.71/0.99  prop_solver_calls:                      30
% 1.71/0.99  prop_fast_solver_calls:                 532
% 1.71/0.99  smt_solver_calls:                       0
% 1.71/0.99  smt_fast_solver_calls:                  0
% 1.71/0.99  prop_num_of_clauses:                    1580
% 1.71/0.99  prop_preprocess_simplified:             4227
% 1.71/0.99  prop_fo_subsumed:                       18
% 1.71/0.99  prop_solver_time:                       0.
% 1.71/0.99  smt_solver_time:                        0.
% 1.71/0.99  smt_fast_solver_time:                   0.
% 1.71/0.99  prop_fast_solver_time:                  0.
% 1.71/0.99  prop_unsat_core_time:                   0.
% 1.71/0.99  
% 1.71/0.99  ------ QBF
% 1.71/0.99  
% 1.71/0.99  qbf_q_res:                              0
% 1.71/0.99  qbf_num_tautologies:                    0
% 1.71/0.99  qbf_prep_cycles:                        0
% 1.71/0.99  
% 1.71/0.99  ------ BMC1
% 1.71/0.99  
% 1.71/0.99  bmc1_current_bound:                     -1
% 1.71/0.99  bmc1_last_solved_bound:                 -1
% 1.71/0.99  bmc1_unsat_core_size:                   -1
% 1.71/0.99  bmc1_unsat_core_parents_size:           -1
% 1.71/0.99  bmc1_merge_next_fun:                    0
% 1.71/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation
% 1.71/0.99  
% 1.71/0.99  inst_num_of_clauses:                    506
% 1.71/0.99  inst_num_in_passive:                    159
% 1.71/0.99  inst_num_in_active:                     289
% 1.71/0.99  inst_num_in_unprocessed:                58
% 1.71/0.99  inst_num_of_loops:                      340
% 1.71/0.99  inst_num_of_learning_restarts:          0
% 1.71/0.99  inst_num_moves_active_passive:          47
% 1.71/0.99  inst_lit_activity:                      0
% 1.71/0.99  inst_lit_activity_moves:                0
% 1.71/0.99  inst_num_tautologies:                   0
% 1.71/0.99  inst_num_prop_implied:                  0
% 1.71/0.99  inst_num_existing_simplified:           0
% 1.71/0.99  inst_num_eq_res_simplified:             0
% 1.71/0.99  inst_num_child_elim:                    0
% 1.71/0.99  inst_num_of_dismatching_blockings:      292
% 1.71/0.99  inst_num_of_non_proper_insts:           785
% 1.71/0.99  inst_num_of_duplicates:                 0
% 1.71/0.99  inst_inst_num_from_inst_to_res:         0
% 1.71/0.99  inst_dismatching_checking_time:         0.
% 1.71/0.99  
% 1.71/0.99  ------ Resolution
% 1.71/0.99  
% 1.71/0.99  res_num_of_clauses:                     0
% 1.71/0.99  res_num_in_passive:                     0
% 1.71/0.99  res_num_in_active:                      0
% 1.71/0.99  res_num_of_loops:                       82
% 1.71/0.99  res_forward_subset_subsumed:            66
% 1.71/0.99  res_backward_subset_subsumed:           0
% 1.71/0.99  res_forward_subsumed:                   0
% 1.71/0.99  res_backward_subsumed:                  0
% 1.71/0.99  res_forward_subsumption_resolution:     0
% 1.71/0.99  res_backward_subsumption_resolution:    0
% 1.71/0.99  res_clause_to_clause_subsumption:       666
% 1.71/0.99  res_orphan_elimination:                 0
% 1.71/0.99  res_tautology_del:                      83
% 1.71/0.99  res_num_eq_res_simplified:              0
% 1.71/0.99  res_num_sel_changes:                    0
% 1.71/0.99  res_moves_from_active_to_pass:          0
% 1.71/0.99  
% 1.71/0.99  ------ Superposition
% 1.71/0.99  
% 1.71/0.99  sup_time_total:                         0.
% 1.71/0.99  sup_time_generating:                    0.
% 1.71/0.99  sup_time_sim_full:                      0.
% 1.71/0.99  sup_time_sim_immed:                     0.
% 1.71/0.99  
% 1.71/0.99  sup_num_of_clauses:                     166
% 1.71/0.99  sup_num_in_active:                      49
% 1.71/0.99  sup_num_in_passive:                     117
% 1.71/0.99  sup_num_of_loops:                       66
% 1.71/0.99  sup_fw_superposition:                   74
% 1.71/0.99  sup_bw_superposition:                   121
% 1.71/0.99  sup_immediate_simplified:               54
% 1.71/0.99  sup_given_eliminated:                   2
% 1.71/0.99  comparisons_done:                       0
% 1.71/0.99  comparisons_avoided:                    0
% 1.71/0.99  
% 1.71/0.99  ------ Simplifications
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  sim_fw_subset_subsumed:                 5
% 1.71/0.99  sim_bw_subset_subsumed:                 3
% 1.71/0.99  sim_fw_subsumed:                        9
% 1.71/0.99  sim_bw_subsumed:                        0
% 1.71/0.99  sim_fw_subsumption_res:                 4
% 1.71/0.99  sim_bw_subsumption_res:                 0
% 1.71/0.99  sim_tautology_del:                      0
% 1.71/0.99  sim_eq_tautology_del:                   6
% 1.71/0.99  sim_eq_res_simp:                        1
% 1.71/0.99  sim_fw_demodulated:                     31
% 1.71/0.99  sim_bw_demodulated:                     16
% 1.71/0.99  sim_light_normalised:                   32
% 1.71/0.99  sim_joinable_taut:                      0
% 1.71/0.99  sim_joinable_simp:                      0
% 1.71/0.99  sim_ac_normalised:                      0
% 1.71/0.99  sim_smt_subsumption:                    0
% 1.71/0.99  
%------------------------------------------------------------------------------
