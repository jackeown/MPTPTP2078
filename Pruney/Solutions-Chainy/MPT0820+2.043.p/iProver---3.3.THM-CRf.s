%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:58 EST 2020

% Result     : Theorem 31.68s
% Output     : CNFRefutation 31.68s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 442 expanded)
%              Number of clauses        :   73 ( 207 expanded)
%              Number of leaves         :   15 (  77 expanded)
%              Depth                    :   22
%              Number of atoms          :  260 ( 916 expanded)
%              Number of equality atoms :   86 ( 200 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f49,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(definition_unfolding,[],[f49,f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_375,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X0_43,k5_xboole_0(X2_43,k4_xboole_0(X1_43,X2_43))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_738,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X0_43,k5_xboole_0(X2_43,k4_xboole_0(X1_43,X2_43))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_372,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X1_43)
    | r1_tarski(k5_xboole_0(X0_43,k4_xboole_0(X2_43,X0_43)),X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_741,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X2_43,X1_43) != iProver_top
    | r1_tarski(k5_xboole_0(X0_43,k4_xboole_0(X2_43,X0_43)),X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_364,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_749,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_8])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | r1_tarski(k1_relat_1(X0_43),X1_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_215])).

cnf(c_751,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
    | r1_tarski(k1_relat_1(X0_43),X1_43) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_2494,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_751])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_368,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_745,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_743,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_1079,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_743])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_127,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_128,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_127])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_128])).

cnf(c_363,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ v1_relat_1(X1_43)
    | v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_155])).

cnf(c_750,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_1886,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_750])).

cnf(c_2133,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_745,c_1886])).

cnf(c_2619,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2494,c_2133])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_374,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X1_43,X2_43)
    | r1_tarski(X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_739,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X1_43,X2_43) != iProver_top
    | r1_tarski(X0_43,X2_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_2624,plain,
    ( r1_tarski(k1_relat_1(sK2),X0_43) = iProver_top
    | r1_tarski(sK0,X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_2619,c_739])).

cnf(c_2787,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X1_43) = iProver_top
    | r1_tarski(sK0,X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_739])).

cnf(c_3146,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k5_xboole_0(X2_43,k4_xboole_0(X1_43,X2_43))) = iProver_top
    | r1_tarski(sK0,X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_2787])).

cnf(c_4095,plain,
    ( r1_tarski(k1_relat_1(sK2),k5_xboole_0(X0_43,k4_xboole_0(sK0,X0_43))) = iProver_top
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2619,c_3146])).

cnf(c_2,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_373,plain,
    ( r1_tarski(X0_43,k5_xboole_0(X0_43,k4_xboole_0(X1_43,X0_43))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_740,plain,
    ( r1_tarski(X0_43,k5_xboole_0(X0_43,k4_xboole_0(X1_43,X0_43))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_369,plain,
    ( ~ v1_relat_1(X0_43)
    | k5_xboole_0(k1_relat_1(X0_43),k4_xboole_0(k2_relat_1(X0_43),k1_relat_1(X0_43))) = k3_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_744,plain,
    ( k5_xboole_0(k1_relat_1(X0_43),k4_xboole_0(k2_relat_1(X0_43),k1_relat_1(X0_43))) = k3_relat_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_2136,plain,
    ( k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2133,c_744])).

cnf(c_2331,plain,
    ( r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_741])).

cnf(c_8885,plain,
    ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(X0_43,k2_relat_1(sK2)))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(X0_43,k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_2331])).

cnf(c_24022,plain,
    ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))) = iProver_top
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4095,c_8885])).

cnf(c_24015,plain,
    ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(X0_43,k2_relat_1(sK2)))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_8885])).

cnf(c_24028,plain,
    ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24015])).

cnf(c_24445,plain,
    ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24022,c_2133,c_2494,c_24028])).

cnf(c_24459,plain,
    ( r1_tarski(k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2))),X0_43) != iProver_top
    | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top ),
    inference(superposition,[status(thm)],[c_24445,c_739])).

cnf(c_26840,plain,
    ( r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
    | r1_tarski(sK0,X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_24459])).

cnf(c_27167,plain,
    ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(X0_43,k4_xboole_0(X1_43,X0_43))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X1_43) != iProver_top
    | r1_tarski(sK0,k5_xboole_0(X0_43,k4_xboole_0(X1_43,X0_43))) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_26840])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_365,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_748,plain,
    ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_96235,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27167,c_748])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | k2_relset_1(X1_43,X2_43,X0_43) = k2_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_747,plain,
    ( k2_relset_1(X0_43,X1_43,X2_43) = k2_relat_1(X2_43)
    | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_1365,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_749,c_747])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_746,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_1524,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_746])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1637,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1524,c_16])).

cnf(c_1641,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_743])).

cnf(c_1501,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_1502,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1501])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_96235,c_1641,c_1502])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : iproveropt_run.sh %d %s
% 0.09/0.29  % Computer   : n021.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 12:45:34 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  % Running in FOF mode
% 31.68/4.39  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.68/4.39  
% 31.68/4.39  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.68/4.39  
% 31.68/4.39  ------  iProver source info
% 31.68/4.39  
% 31.68/4.39  git: date: 2020-06-30 10:37:57 +0100
% 31.68/4.39  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.68/4.39  git: non_committed_changes: false
% 31.68/4.39  git: last_make_outside_of_git: false
% 31.68/4.39  
% 31.68/4.39  ------ 
% 31.68/4.39  
% 31.68/4.39  ------ Input Options
% 31.68/4.39  
% 31.68/4.39  --out_options                           all
% 31.68/4.39  --tptp_safe_out                         true
% 31.68/4.39  --problem_path                          ""
% 31.68/4.39  --include_path                          ""
% 31.68/4.39  --clausifier                            res/vclausify_rel
% 31.68/4.39  --clausifier_options                    ""
% 31.68/4.39  --stdin                                 false
% 31.68/4.39  --stats_out                             all
% 31.68/4.39  
% 31.68/4.39  ------ General Options
% 31.68/4.39  
% 31.68/4.39  --fof                                   false
% 31.68/4.39  --time_out_real                         305.
% 31.68/4.39  --time_out_virtual                      -1.
% 31.68/4.39  --symbol_type_check                     false
% 31.68/4.39  --clausify_out                          false
% 31.68/4.39  --sig_cnt_out                           false
% 31.68/4.39  --trig_cnt_out                          false
% 31.68/4.39  --trig_cnt_out_tolerance                1.
% 31.68/4.39  --trig_cnt_out_sk_spl                   false
% 31.68/4.39  --abstr_cl_out                          false
% 31.68/4.39  
% 31.68/4.39  ------ Global Options
% 31.68/4.39  
% 31.68/4.39  --schedule                              default
% 31.68/4.39  --add_important_lit                     false
% 31.68/4.39  --prop_solver_per_cl                    1000
% 31.68/4.39  --min_unsat_core                        false
% 31.68/4.39  --soft_assumptions                      false
% 31.68/4.39  --soft_lemma_size                       3
% 31.68/4.39  --prop_impl_unit_size                   0
% 31.68/4.39  --prop_impl_unit                        []
% 31.68/4.39  --share_sel_clauses                     true
% 31.68/4.39  --reset_solvers                         false
% 31.68/4.39  --bc_imp_inh                            [conj_cone]
% 31.68/4.39  --conj_cone_tolerance                   3.
% 31.68/4.39  --extra_neg_conj                        none
% 31.68/4.39  --large_theory_mode                     true
% 31.68/4.39  --prolific_symb_bound                   200
% 31.68/4.39  --lt_threshold                          2000
% 31.68/4.39  --clause_weak_htbl                      true
% 31.68/4.39  --gc_record_bc_elim                     false
% 31.68/4.39  
% 31.68/4.39  ------ Preprocessing Options
% 31.68/4.39  
% 31.68/4.39  --preprocessing_flag                    true
% 31.68/4.39  --time_out_prep_mult                    0.1
% 31.68/4.39  --splitting_mode                        input
% 31.68/4.39  --splitting_grd                         true
% 31.68/4.39  --splitting_cvd                         false
% 31.68/4.39  --splitting_cvd_svl                     false
% 31.68/4.39  --splitting_nvd                         32
% 31.68/4.39  --sub_typing                            true
% 31.68/4.39  --prep_gs_sim                           true
% 31.68/4.39  --prep_unflatten                        true
% 31.68/4.39  --prep_res_sim                          true
% 31.68/4.39  --prep_upred                            true
% 31.68/4.39  --prep_sem_filter                       exhaustive
% 31.68/4.39  --prep_sem_filter_out                   false
% 31.68/4.39  --pred_elim                             true
% 31.68/4.39  --res_sim_input                         true
% 31.68/4.39  --eq_ax_congr_red                       true
% 31.68/4.39  --pure_diseq_elim                       true
% 31.68/4.39  --brand_transform                       false
% 31.68/4.39  --non_eq_to_eq                          false
% 31.68/4.39  --prep_def_merge                        true
% 31.68/4.39  --prep_def_merge_prop_impl              false
% 31.68/4.39  --prep_def_merge_mbd                    true
% 31.68/4.39  --prep_def_merge_tr_red                 false
% 31.68/4.39  --prep_def_merge_tr_cl                  false
% 31.68/4.39  --smt_preprocessing                     true
% 31.68/4.39  --smt_ac_axioms                         fast
% 31.68/4.39  --preprocessed_out                      false
% 31.68/4.39  --preprocessed_stats                    false
% 31.68/4.39  
% 31.68/4.39  ------ Abstraction refinement Options
% 31.68/4.39  
% 31.68/4.39  --abstr_ref                             []
% 31.68/4.39  --abstr_ref_prep                        false
% 31.68/4.39  --abstr_ref_until_sat                   false
% 31.68/4.39  --abstr_ref_sig_restrict                funpre
% 31.68/4.39  --abstr_ref_af_restrict_to_split_sk     false
% 31.68/4.39  --abstr_ref_under                       []
% 31.68/4.39  
% 31.68/4.39  ------ SAT Options
% 31.68/4.39  
% 31.68/4.39  --sat_mode                              false
% 31.68/4.39  --sat_fm_restart_options                ""
% 31.68/4.39  --sat_gr_def                            false
% 31.68/4.39  --sat_epr_types                         true
% 31.68/4.39  --sat_non_cyclic_types                  false
% 31.68/4.39  --sat_finite_models                     false
% 31.68/4.39  --sat_fm_lemmas                         false
% 31.68/4.39  --sat_fm_prep                           false
% 31.68/4.39  --sat_fm_uc_incr                        true
% 31.68/4.39  --sat_out_model                         small
% 31.68/4.39  --sat_out_clauses                       false
% 31.68/4.39  
% 31.68/4.39  ------ QBF Options
% 31.68/4.39  
% 31.68/4.39  --qbf_mode                              false
% 31.68/4.39  --qbf_elim_univ                         false
% 31.68/4.39  --qbf_dom_inst                          none
% 31.68/4.39  --qbf_dom_pre_inst                      false
% 31.68/4.39  --qbf_sk_in                             false
% 31.68/4.39  --qbf_pred_elim                         true
% 31.68/4.39  --qbf_split                             512
% 31.68/4.39  
% 31.68/4.39  ------ BMC1 Options
% 31.68/4.39  
% 31.68/4.39  --bmc1_incremental                      false
% 31.68/4.39  --bmc1_axioms                           reachable_all
% 31.68/4.39  --bmc1_min_bound                        0
% 31.68/4.39  --bmc1_max_bound                        -1
% 31.68/4.39  --bmc1_max_bound_default                -1
% 31.68/4.39  --bmc1_symbol_reachability              true
% 31.68/4.39  --bmc1_property_lemmas                  false
% 31.68/4.39  --bmc1_k_induction                      false
% 31.68/4.39  --bmc1_non_equiv_states                 false
% 31.68/4.39  --bmc1_deadlock                         false
% 31.68/4.39  --bmc1_ucm                              false
% 31.68/4.39  --bmc1_add_unsat_core                   none
% 31.68/4.39  --bmc1_unsat_core_children              false
% 31.68/4.39  --bmc1_unsat_core_extrapolate_axioms    false
% 31.68/4.39  --bmc1_out_stat                         full
% 31.68/4.39  --bmc1_ground_init                      false
% 31.68/4.39  --bmc1_pre_inst_next_state              false
% 31.68/4.39  --bmc1_pre_inst_state                   false
% 31.68/4.39  --bmc1_pre_inst_reach_state             false
% 31.68/4.39  --bmc1_out_unsat_core                   false
% 31.68/4.39  --bmc1_aig_witness_out                  false
% 31.68/4.39  --bmc1_verbose                          false
% 31.68/4.39  --bmc1_dump_clauses_tptp                false
% 31.68/4.39  --bmc1_dump_unsat_core_tptp             false
% 31.68/4.39  --bmc1_dump_file                        -
% 31.68/4.39  --bmc1_ucm_expand_uc_limit              128
% 31.68/4.39  --bmc1_ucm_n_expand_iterations          6
% 31.68/4.39  --bmc1_ucm_extend_mode                  1
% 31.68/4.39  --bmc1_ucm_init_mode                    2
% 31.68/4.39  --bmc1_ucm_cone_mode                    none
% 31.68/4.39  --bmc1_ucm_reduced_relation_type        0
% 31.68/4.39  --bmc1_ucm_relax_model                  4
% 31.68/4.39  --bmc1_ucm_full_tr_after_sat            true
% 31.68/4.39  --bmc1_ucm_expand_neg_assumptions       false
% 31.68/4.39  --bmc1_ucm_layered_model                none
% 31.68/4.39  --bmc1_ucm_max_lemma_size               10
% 31.68/4.39  
% 31.68/4.39  ------ AIG Options
% 31.68/4.39  
% 31.68/4.39  --aig_mode                              false
% 31.68/4.39  
% 31.68/4.39  ------ Instantiation Options
% 31.68/4.39  
% 31.68/4.39  --instantiation_flag                    true
% 31.68/4.39  --inst_sos_flag                         true
% 31.68/4.39  --inst_sos_phase                        true
% 31.68/4.39  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.68/4.39  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.68/4.39  --inst_lit_sel_side                     num_symb
% 31.68/4.39  --inst_solver_per_active                1400
% 31.68/4.39  --inst_solver_calls_frac                1.
% 31.68/4.39  --inst_passive_queue_type               priority_queues
% 31.68/4.39  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.68/4.39  --inst_passive_queues_freq              [25;2]
% 31.68/4.39  --inst_dismatching                      true
% 31.68/4.39  --inst_eager_unprocessed_to_passive     true
% 31.68/4.39  --inst_prop_sim_given                   true
% 31.68/4.39  --inst_prop_sim_new                     false
% 31.68/4.39  --inst_subs_new                         false
% 31.68/4.39  --inst_eq_res_simp                      false
% 31.68/4.39  --inst_subs_given                       false
% 31.68/4.39  --inst_orphan_elimination               true
% 31.68/4.39  --inst_learning_loop_flag               true
% 31.68/4.39  --inst_learning_start                   3000
% 31.68/4.39  --inst_learning_factor                  2
% 31.68/4.39  --inst_start_prop_sim_after_learn       3
% 31.68/4.39  --inst_sel_renew                        solver
% 31.68/4.39  --inst_lit_activity_flag                true
% 31.68/4.39  --inst_restr_to_given                   false
% 31.68/4.39  --inst_activity_threshold               500
% 31.68/4.39  --inst_out_proof                        true
% 31.68/4.39  
% 31.68/4.39  ------ Resolution Options
% 31.68/4.39  
% 31.68/4.39  --resolution_flag                       true
% 31.68/4.39  --res_lit_sel                           adaptive
% 31.68/4.39  --res_lit_sel_side                      none
% 31.68/4.39  --res_ordering                          kbo
% 31.68/4.39  --res_to_prop_solver                    active
% 31.68/4.39  --res_prop_simpl_new                    false
% 31.68/4.39  --res_prop_simpl_given                  true
% 31.68/4.39  --res_passive_queue_type                priority_queues
% 31.68/4.39  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.68/4.39  --res_passive_queues_freq               [15;5]
% 31.68/4.39  --res_forward_subs                      full
% 31.68/4.39  --res_backward_subs                     full
% 31.68/4.39  --res_forward_subs_resolution           true
% 31.68/4.39  --res_backward_subs_resolution          true
% 31.68/4.39  --res_orphan_elimination                true
% 31.68/4.39  --res_time_limit                        2.
% 31.68/4.39  --res_out_proof                         true
% 31.68/4.39  
% 31.68/4.39  ------ Superposition Options
% 31.68/4.39  
% 31.68/4.39  --superposition_flag                    true
% 31.68/4.39  --sup_passive_queue_type                priority_queues
% 31.68/4.39  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.68/4.39  --sup_passive_queues_freq               [8;1;4]
% 31.68/4.39  --demod_completeness_check              fast
% 31.68/4.39  --demod_use_ground                      true
% 31.68/4.39  --sup_to_prop_solver                    passive
% 31.68/4.39  --sup_prop_simpl_new                    true
% 31.68/4.39  --sup_prop_simpl_given                  true
% 31.68/4.39  --sup_fun_splitting                     true
% 31.68/4.39  --sup_smt_interval                      50000
% 31.68/4.39  
% 31.68/4.39  ------ Superposition Simplification Setup
% 31.68/4.39  
% 31.68/4.39  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.68/4.39  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.68/4.39  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.68/4.39  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.68/4.39  --sup_full_triv                         [TrivRules;PropSubs]
% 31.68/4.39  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.68/4.39  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.68/4.39  --sup_immed_triv                        [TrivRules]
% 31.68/4.39  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.68/4.39  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.68/4.39  --sup_immed_bw_main                     []
% 31.68/4.39  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.68/4.39  --sup_input_triv                        [Unflattening;TrivRules]
% 31.68/4.39  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.68/4.39  --sup_input_bw                          []
% 31.68/4.39  
% 31.68/4.39  ------ Combination Options
% 31.68/4.39  
% 31.68/4.39  --comb_res_mult                         3
% 31.68/4.39  --comb_sup_mult                         2
% 31.68/4.39  --comb_inst_mult                        10
% 31.68/4.39  
% 31.68/4.39  ------ Debug Options
% 31.68/4.39  
% 31.68/4.39  --dbg_backtrace                         false
% 31.68/4.39  --dbg_dump_prop_clauses                 false
% 31.68/4.39  --dbg_dump_prop_clauses_file            -
% 31.68/4.39  --dbg_out_stat                          false
% 31.68/4.39  ------ Parsing...
% 31.68/4.39  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.68/4.39  
% 31.68/4.39  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.68/4.39  
% 31.68/4.39  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.68/4.39  
% 31.68/4.39  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.68/4.39  ------ Proving...
% 31.68/4.39  ------ Problem Properties 
% 31.68/4.39  
% 31.68/4.39  
% 31.68/4.39  clauses                                 14
% 31.68/4.39  conjectures                             2
% 31.68/4.39  EPR                                     2
% 31.68/4.39  Horn                                    14
% 31.68/4.39  unary                                   4
% 31.68/4.39  binary                                  6
% 31.68/4.39  lits                                    28
% 31.68/4.39  lits eq                                 2
% 31.68/4.39  fd_pure                                 0
% 31.68/4.39  fd_pseudo                               0
% 31.68/4.39  fd_cond                                 0
% 31.68/4.39  fd_pseudo_cond                          0
% 31.68/4.39  AC symbols                              0
% 31.68/4.39  
% 31.68/4.39  ------ Schedule dynamic 5 is on 
% 31.68/4.39  
% 31.68/4.39  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.68/4.39  
% 31.68/4.39  
% 31.68/4.39  ------ 
% 31.68/4.39  Current options:
% 31.68/4.39  ------ 
% 31.68/4.39  
% 31.68/4.39  ------ Input Options
% 31.68/4.39  
% 31.68/4.39  --out_options                           all
% 31.68/4.39  --tptp_safe_out                         true
% 31.68/4.39  --problem_path                          ""
% 31.68/4.39  --include_path                          ""
% 31.68/4.39  --clausifier                            res/vclausify_rel
% 31.68/4.39  --clausifier_options                    ""
% 31.68/4.39  --stdin                                 false
% 31.68/4.39  --stats_out                             all
% 31.68/4.39  
% 31.68/4.39  ------ General Options
% 31.68/4.39  
% 31.68/4.39  --fof                                   false
% 31.68/4.39  --time_out_real                         305.
% 31.68/4.39  --time_out_virtual                      -1.
% 31.68/4.39  --symbol_type_check                     false
% 31.68/4.39  --clausify_out                          false
% 31.68/4.39  --sig_cnt_out                           false
% 31.68/4.39  --trig_cnt_out                          false
% 31.68/4.39  --trig_cnt_out_tolerance                1.
% 31.68/4.39  --trig_cnt_out_sk_spl                   false
% 31.68/4.39  --abstr_cl_out                          false
% 31.68/4.39  
% 31.68/4.39  ------ Global Options
% 31.68/4.39  
% 31.68/4.39  --schedule                              default
% 31.68/4.39  --add_important_lit                     false
% 31.68/4.39  --prop_solver_per_cl                    1000
% 31.68/4.39  --min_unsat_core                        false
% 31.68/4.39  --soft_assumptions                      false
% 31.68/4.39  --soft_lemma_size                       3
% 31.68/4.39  --prop_impl_unit_size                   0
% 31.68/4.39  --prop_impl_unit                        []
% 31.68/4.39  --share_sel_clauses                     true
% 31.68/4.39  --reset_solvers                         false
% 31.68/4.39  --bc_imp_inh                            [conj_cone]
% 31.68/4.39  --conj_cone_tolerance                   3.
% 31.68/4.39  --extra_neg_conj                        none
% 31.68/4.39  --large_theory_mode                     true
% 31.68/4.39  --prolific_symb_bound                   200
% 31.68/4.39  --lt_threshold                          2000
% 31.68/4.39  --clause_weak_htbl                      true
% 31.68/4.39  --gc_record_bc_elim                     false
% 31.68/4.39  
% 31.68/4.39  ------ Preprocessing Options
% 31.68/4.39  
% 31.68/4.39  --preprocessing_flag                    true
% 31.68/4.39  --time_out_prep_mult                    0.1
% 31.68/4.39  --splitting_mode                        input
% 31.68/4.39  --splitting_grd                         true
% 31.68/4.39  --splitting_cvd                         false
% 31.68/4.39  --splitting_cvd_svl                     false
% 31.68/4.39  --splitting_nvd                         32
% 31.68/4.39  --sub_typing                            true
% 31.68/4.39  --prep_gs_sim                           true
% 31.68/4.39  --prep_unflatten                        true
% 31.68/4.39  --prep_res_sim                          true
% 31.68/4.39  --prep_upred                            true
% 31.68/4.39  --prep_sem_filter                       exhaustive
% 31.68/4.39  --prep_sem_filter_out                   false
% 31.68/4.39  --pred_elim                             true
% 31.68/4.39  --res_sim_input                         true
% 31.68/4.39  --eq_ax_congr_red                       true
% 31.68/4.39  --pure_diseq_elim                       true
% 31.68/4.39  --brand_transform                       false
% 31.68/4.39  --non_eq_to_eq                          false
% 31.68/4.39  --prep_def_merge                        true
% 31.68/4.39  --prep_def_merge_prop_impl              false
% 31.68/4.39  --prep_def_merge_mbd                    true
% 31.68/4.39  --prep_def_merge_tr_red                 false
% 31.68/4.39  --prep_def_merge_tr_cl                  false
% 31.68/4.39  --smt_preprocessing                     true
% 31.68/4.39  --smt_ac_axioms                         fast
% 31.68/4.39  --preprocessed_out                      false
% 31.68/4.39  --preprocessed_stats                    false
% 31.68/4.39  
% 31.68/4.39  ------ Abstraction refinement Options
% 31.68/4.39  
% 31.68/4.39  --abstr_ref                             []
% 31.68/4.39  --abstr_ref_prep                        false
% 31.68/4.39  --abstr_ref_until_sat                   false
% 31.68/4.39  --abstr_ref_sig_restrict                funpre
% 31.68/4.39  --abstr_ref_af_restrict_to_split_sk     false
% 31.68/4.39  --abstr_ref_under                       []
% 31.68/4.39  
% 31.68/4.39  ------ SAT Options
% 31.68/4.39  
% 31.68/4.39  --sat_mode                              false
% 31.68/4.39  --sat_fm_restart_options                ""
% 31.68/4.39  --sat_gr_def                            false
% 31.68/4.39  --sat_epr_types                         true
% 31.68/4.39  --sat_non_cyclic_types                  false
% 31.68/4.39  --sat_finite_models                     false
% 31.68/4.39  --sat_fm_lemmas                         false
% 31.68/4.39  --sat_fm_prep                           false
% 31.68/4.39  --sat_fm_uc_incr                        true
% 31.68/4.39  --sat_out_model                         small
% 31.68/4.39  --sat_out_clauses                       false
% 31.68/4.39  
% 31.68/4.39  ------ QBF Options
% 31.68/4.39  
% 31.68/4.39  --qbf_mode                              false
% 31.68/4.39  --qbf_elim_univ                         false
% 31.68/4.39  --qbf_dom_inst                          none
% 31.68/4.39  --qbf_dom_pre_inst                      false
% 31.68/4.39  --qbf_sk_in                             false
% 31.68/4.39  --qbf_pred_elim                         true
% 31.68/4.39  --qbf_split                             512
% 31.68/4.39  
% 31.68/4.39  ------ BMC1 Options
% 31.68/4.39  
% 31.68/4.39  --bmc1_incremental                      false
% 31.68/4.39  --bmc1_axioms                           reachable_all
% 31.68/4.39  --bmc1_min_bound                        0
% 31.68/4.39  --bmc1_max_bound                        -1
% 31.68/4.39  --bmc1_max_bound_default                -1
% 31.68/4.39  --bmc1_symbol_reachability              true
% 31.68/4.39  --bmc1_property_lemmas                  false
% 31.68/4.39  --bmc1_k_induction                      false
% 31.68/4.39  --bmc1_non_equiv_states                 false
% 31.68/4.39  --bmc1_deadlock                         false
% 31.68/4.39  --bmc1_ucm                              false
% 31.68/4.39  --bmc1_add_unsat_core                   none
% 31.68/4.39  --bmc1_unsat_core_children              false
% 31.68/4.39  --bmc1_unsat_core_extrapolate_axioms    false
% 31.68/4.39  --bmc1_out_stat                         full
% 31.68/4.39  --bmc1_ground_init                      false
% 31.68/4.39  --bmc1_pre_inst_next_state              false
% 31.68/4.39  --bmc1_pre_inst_state                   false
% 31.68/4.39  --bmc1_pre_inst_reach_state             false
% 31.68/4.39  --bmc1_out_unsat_core                   false
% 31.68/4.39  --bmc1_aig_witness_out                  false
% 31.68/4.39  --bmc1_verbose                          false
% 31.68/4.39  --bmc1_dump_clauses_tptp                false
% 31.68/4.39  --bmc1_dump_unsat_core_tptp             false
% 31.68/4.39  --bmc1_dump_file                        -
% 31.68/4.39  --bmc1_ucm_expand_uc_limit              128
% 31.68/4.39  --bmc1_ucm_n_expand_iterations          6
% 31.68/4.39  --bmc1_ucm_extend_mode                  1
% 31.68/4.39  --bmc1_ucm_init_mode                    2
% 31.68/4.39  --bmc1_ucm_cone_mode                    none
% 31.68/4.39  --bmc1_ucm_reduced_relation_type        0
% 31.68/4.39  --bmc1_ucm_relax_model                  4
% 31.68/4.39  --bmc1_ucm_full_tr_after_sat            true
% 31.68/4.39  --bmc1_ucm_expand_neg_assumptions       false
% 31.68/4.39  --bmc1_ucm_layered_model                none
% 31.68/4.39  --bmc1_ucm_max_lemma_size               10
% 31.68/4.39  
% 31.68/4.39  ------ AIG Options
% 31.68/4.39  
% 31.68/4.39  --aig_mode                              false
% 31.68/4.39  
% 31.68/4.39  ------ Instantiation Options
% 31.68/4.39  
% 31.68/4.39  --instantiation_flag                    true
% 31.68/4.39  --inst_sos_flag                         true
% 31.68/4.39  --inst_sos_phase                        true
% 31.68/4.39  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.68/4.39  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.68/4.39  --inst_lit_sel_side                     none
% 31.68/4.39  --inst_solver_per_active                1400
% 31.68/4.39  --inst_solver_calls_frac                1.
% 31.68/4.39  --inst_passive_queue_type               priority_queues
% 31.68/4.39  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.68/4.39  --inst_passive_queues_freq              [25;2]
% 31.68/4.39  --inst_dismatching                      true
% 31.68/4.39  --inst_eager_unprocessed_to_passive     true
% 31.68/4.39  --inst_prop_sim_given                   true
% 31.68/4.39  --inst_prop_sim_new                     false
% 31.68/4.39  --inst_subs_new                         false
% 31.68/4.39  --inst_eq_res_simp                      false
% 31.68/4.39  --inst_subs_given                       false
% 31.68/4.39  --inst_orphan_elimination               true
% 31.68/4.39  --inst_learning_loop_flag               true
% 31.68/4.39  --inst_learning_start                   3000
% 31.68/4.39  --inst_learning_factor                  2
% 31.68/4.39  --inst_start_prop_sim_after_learn       3
% 31.68/4.39  --inst_sel_renew                        solver
% 31.68/4.39  --inst_lit_activity_flag                true
% 31.68/4.39  --inst_restr_to_given                   false
% 31.68/4.39  --inst_activity_threshold               500
% 31.68/4.39  --inst_out_proof                        true
% 31.68/4.39  
% 31.68/4.39  ------ Resolution Options
% 31.68/4.39  
% 31.68/4.39  --resolution_flag                       false
% 31.68/4.39  --res_lit_sel                           adaptive
% 31.68/4.39  --res_lit_sel_side                      none
% 31.68/4.39  --res_ordering                          kbo
% 31.68/4.39  --res_to_prop_solver                    active
% 31.68/4.39  --res_prop_simpl_new                    false
% 31.68/4.39  --res_prop_simpl_given                  true
% 31.68/4.39  --res_passive_queue_type                priority_queues
% 31.68/4.39  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.68/4.39  --res_passive_queues_freq               [15;5]
% 31.68/4.39  --res_forward_subs                      full
% 31.68/4.39  --res_backward_subs                     full
% 31.68/4.39  --res_forward_subs_resolution           true
% 31.68/4.39  --res_backward_subs_resolution          true
% 31.68/4.39  --res_orphan_elimination                true
% 31.68/4.39  --res_time_limit                        2.
% 31.68/4.39  --res_out_proof                         true
% 31.68/4.39  
% 31.68/4.39  ------ Superposition Options
% 31.68/4.39  
% 31.68/4.39  --superposition_flag                    true
% 31.68/4.39  --sup_passive_queue_type                priority_queues
% 31.68/4.39  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.68/4.39  --sup_passive_queues_freq               [8;1;4]
% 31.68/4.39  --demod_completeness_check              fast
% 31.68/4.39  --demod_use_ground                      true
% 31.68/4.39  --sup_to_prop_solver                    passive
% 31.68/4.39  --sup_prop_simpl_new                    true
% 31.68/4.39  --sup_prop_simpl_given                  true
% 31.68/4.39  --sup_fun_splitting                     true
% 31.68/4.39  --sup_smt_interval                      50000
% 31.68/4.39  
% 31.68/4.39  ------ Superposition Simplification Setup
% 31.68/4.39  
% 31.68/4.39  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.68/4.39  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.68/4.39  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.68/4.39  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.68/4.39  --sup_full_triv                         [TrivRules;PropSubs]
% 31.68/4.39  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.68/4.39  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.68/4.39  --sup_immed_triv                        [TrivRules]
% 31.68/4.39  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.68/4.39  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.68/4.39  --sup_immed_bw_main                     []
% 31.68/4.39  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.68/4.39  --sup_input_triv                        [Unflattening;TrivRules]
% 31.68/4.39  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.68/4.39  --sup_input_bw                          []
% 31.68/4.39  
% 31.68/4.39  ------ Combination Options
% 31.68/4.39  
% 31.68/4.39  --comb_res_mult                         3
% 31.68/4.39  --comb_sup_mult                         2
% 31.68/4.39  --comb_inst_mult                        10
% 31.68/4.39  
% 31.68/4.39  ------ Debug Options
% 31.68/4.39  
% 31.68/4.39  --dbg_backtrace                         false
% 31.68/4.39  --dbg_dump_prop_clauses                 false
% 31.68/4.39  --dbg_dump_prop_clauses_file            -
% 31.68/4.39  --dbg_out_stat                          false
% 31.68/4.39  
% 31.68/4.39  
% 31.68/4.39  
% 31.68/4.39  
% 31.68/4.39  ------ Proving...
% 31.68/4.39  
% 31.68/4.39  
% 31.68/4.39  % SZS status Theorem for theBenchmark.p
% 31.68/4.39  
% 31.68/4.39  % SZS output start CNFRefutation for theBenchmark.p
% 31.68/4.39  
% 31.68/4.39  fof(f1,axiom,(
% 31.68/4.39    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f17,plain,(
% 31.68/4.39    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 31.68/4.39    inference(ennf_transformation,[],[f1])).
% 31.68/4.39  
% 31.68/4.39  fof(f33,plain,(
% 31.68/4.39    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 31.68/4.39    inference(cnf_transformation,[],[f17])).
% 31.68/4.39  
% 31.68/4.39  fof(f5,axiom,(
% 31.68/4.39    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f37,plain,(
% 31.68/4.39    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 31.68/4.39    inference(cnf_transformation,[],[f5])).
% 31.68/4.39  
% 31.68/4.39  fof(f50,plain,(
% 31.68/4.39    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 31.68/4.39    inference(definition_unfolding,[],[f33,f37])).
% 31.68/4.39  
% 31.68/4.39  fof(f4,axiom,(
% 31.68/4.39    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f20,plain,(
% 31.68/4.39    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 31.68/4.39    inference(ennf_transformation,[],[f4])).
% 31.68/4.39  
% 31.68/4.39  fof(f21,plain,(
% 31.68/4.39    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 31.68/4.39    inference(flattening,[],[f20])).
% 31.68/4.39  
% 31.68/4.39  fof(f36,plain,(
% 31.68/4.39    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 31.68/4.39    inference(cnf_transformation,[],[f21])).
% 31.68/4.39  
% 31.68/4.39  fof(f52,plain,(
% 31.68/4.39    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 31.68/4.39    inference(definition_unfolding,[],[f36,f37])).
% 31.68/4.39  
% 31.68/4.39  fof(f14,conjecture,(
% 31.68/4.39    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f15,negated_conjecture,(
% 31.68/4.39    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 31.68/4.39    inference(negated_conjecture,[],[f14])).
% 31.68/4.39  
% 31.68/4.39  fof(f28,plain,(
% 31.68/4.39    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.68/4.39    inference(ennf_transformation,[],[f15])).
% 31.68/4.39  
% 31.68/4.39  fof(f31,plain,(
% 31.68/4.39    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 31.68/4.39    introduced(choice_axiom,[])).
% 31.68/4.39  
% 31.68/4.39  fof(f32,plain,(
% 31.68/4.39    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.68/4.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).
% 31.68/4.39  
% 31.68/4.39  fof(f48,plain,(
% 31.68/4.39    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.68/4.39    inference(cnf_transformation,[],[f32])).
% 31.68/4.39  
% 31.68/4.39  fof(f11,axiom,(
% 31.68/4.39    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f16,plain,(
% 31.68/4.39    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 31.68/4.39    inference(pure_predicate_removal,[],[f11])).
% 31.68/4.39  
% 31.68/4.39  fof(f25,plain,(
% 31.68/4.39    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.68/4.39    inference(ennf_transformation,[],[f16])).
% 31.68/4.39  
% 31.68/4.39  fof(f45,plain,(
% 31.68/4.39    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.68/4.39    inference(cnf_transformation,[],[f25])).
% 31.68/4.39  
% 31.68/4.39  fof(f8,axiom,(
% 31.68/4.39    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f23,plain,(
% 31.68/4.39    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.68/4.39    inference(ennf_transformation,[],[f8])).
% 31.68/4.39  
% 31.68/4.39  fof(f30,plain,(
% 31.68/4.39    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 31.68/4.39    inference(nnf_transformation,[],[f23])).
% 31.68/4.39  
% 31.68/4.39  fof(f41,plain,(
% 31.68/4.39    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.68/4.39    inference(cnf_transformation,[],[f30])).
% 31.68/4.39  
% 31.68/4.39  fof(f10,axiom,(
% 31.68/4.39    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f44,plain,(
% 31.68/4.39    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.68/4.39    inference(cnf_transformation,[],[f10])).
% 31.68/4.39  
% 31.68/4.39  fof(f6,axiom,(
% 31.68/4.39    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f29,plain,(
% 31.68/4.39    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.68/4.39    inference(nnf_transformation,[],[f6])).
% 31.68/4.39  
% 31.68/4.39  fof(f38,plain,(
% 31.68/4.39    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.68/4.39    inference(cnf_transformation,[],[f29])).
% 31.68/4.39  
% 31.68/4.39  fof(f7,axiom,(
% 31.68/4.39    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f22,plain,(
% 31.68/4.39    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.68/4.39    inference(ennf_transformation,[],[f7])).
% 31.68/4.39  
% 31.68/4.39  fof(f40,plain,(
% 31.68/4.39    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.68/4.39    inference(cnf_transformation,[],[f22])).
% 31.68/4.39  
% 31.68/4.39  fof(f39,plain,(
% 31.68/4.39    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.68/4.39    inference(cnf_transformation,[],[f29])).
% 31.68/4.39  
% 31.68/4.39  fof(f2,axiom,(
% 31.68/4.39    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f18,plain,(
% 31.68/4.39    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 31.68/4.39    inference(ennf_transformation,[],[f2])).
% 31.68/4.39  
% 31.68/4.39  fof(f19,plain,(
% 31.68/4.39    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 31.68/4.39    inference(flattening,[],[f18])).
% 31.68/4.39  
% 31.68/4.39  fof(f34,plain,(
% 31.68/4.39    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 31.68/4.39    inference(cnf_transformation,[],[f19])).
% 31.68/4.39  
% 31.68/4.39  fof(f3,axiom,(
% 31.68/4.39    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f35,plain,(
% 31.68/4.39    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 31.68/4.39    inference(cnf_transformation,[],[f3])).
% 31.68/4.39  
% 31.68/4.39  fof(f51,plain,(
% 31.68/4.39    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 31.68/4.39    inference(definition_unfolding,[],[f35,f37])).
% 31.68/4.39  
% 31.68/4.39  fof(f9,axiom,(
% 31.68/4.39    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f24,plain,(
% 31.68/4.39    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 31.68/4.39    inference(ennf_transformation,[],[f9])).
% 31.68/4.39  
% 31.68/4.39  fof(f43,plain,(
% 31.68/4.39    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 31.68/4.39    inference(cnf_transformation,[],[f24])).
% 31.68/4.39  
% 31.68/4.39  fof(f53,plain,(
% 31.68/4.39    ( ! [X0] : (k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 31.68/4.39    inference(definition_unfolding,[],[f43,f37])).
% 31.68/4.39  
% 31.68/4.39  fof(f49,plain,(
% 31.68/4.39    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 31.68/4.39    inference(cnf_transformation,[],[f32])).
% 31.68/4.39  
% 31.68/4.39  fof(f54,plain,(
% 31.68/4.39    ~r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 31.68/4.39    inference(definition_unfolding,[],[f49,f37])).
% 31.68/4.39  
% 31.68/4.39  fof(f13,axiom,(
% 31.68/4.39    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f27,plain,(
% 31.68/4.39    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.68/4.39    inference(ennf_transformation,[],[f13])).
% 31.68/4.39  
% 31.68/4.39  fof(f47,plain,(
% 31.68/4.39    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.68/4.39    inference(cnf_transformation,[],[f27])).
% 31.68/4.39  
% 31.68/4.39  fof(f12,axiom,(
% 31.68/4.39    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 31.68/4.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.68/4.39  
% 31.68/4.39  fof(f26,plain,(
% 31.68/4.39    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.68/4.39    inference(ennf_transformation,[],[f12])).
% 31.68/4.39  
% 31.68/4.39  fof(f46,plain,(
% 31.68/4.39    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.68/4.39    inference(cnf_transformation,[],[f26])).
% 31.68/4.39  
% 31.68/4.39  cnf(c_0,plain,
% 31.68/4.39      ( ~ r1_tarski(X0,X1)
% 31.68/4.39      | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 31.68/4.39      inference(cnf_transformation,[],[f50]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_375,plain,
% 31.68/4.39      ( ~ r1_tarski(X0_43,X1_43)
% 31.68/4.39      | r1_tarski(X0_43,k5_xboole_0(X2_43,k4_xboole_0(X1_43,X2_43))) ),
% 31.68/4.39      inference(subtyping,[status(esa)],[c_0]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_738,plain,
% 31.68/4.39      ( r1_tarski(X0_43,X1_43) != iProver_top
% 31.68/4.39      | r1_tarski(X0_43,k5_xboole_0(X2_43,k4_xboole_0(X1_43,X2_43))) = iProver_top ),
% 31.68/4.39      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_3,plain,
% 31.68/4.39      ( ~ r1_tarski(X0,X1)
% 31.68/4.39      | ~ r1_tarski(X2,X1)
% 31.68/4.39      | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 31.68/4.39      inference(cnf_transformation,[],[f52]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_372,plain,
% 31.68/4.39      ( ~ r1_tarski(X0_43,X1_43)
% 31.68/4.39      | ~ r1_tarski(X2_43,X1_43)
% 31.68/4.39      | r1_tarski(k5_xboole_0(X0_43,k4_xboole_0(X2_43,X0_43)),X1_43) ),
% 31.68/4.39      inference(subtyping,[status(esa)],[c_3]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_741,plain,
% 31.68/4.39      ( r1_tarski(X0_43,X1_43) != iProver_top
% 31.68/4.39      | r1_tarski(X2_43,X1_43) != iProver_top
% 31.68/4.39      | r1_tarski(k5_xboole_0(X0_43,k4_xboole_0(X2_43,X0_43)),X1_43) = iProver_top ),
% 31.68/4.39      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_15,negated_conjecture,
% 31.68/4.39      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.68/4.39      inference(cnf_transformation,[],[f48]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_364,negated_conjecture,
% 31.68/4.39      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.68/4.39      inference(subtyping,[status(esa)],[c_15]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_749,plain,
% 31.68/4.39      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.68/4.39      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_11,plain,
% 31.68/4.39      ( v4_relat_1(X0,X1)
% 31.68/4.39      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.68/4.39      inference(cnf_transformation,[],[f45]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_8,plain,
% 31.68/4.39      ( ~ v4_relat_1(X0,X1)
% 31.68/4.39      | r1_tarski(k1_relat_1(X0),X1)
% 31.68/4.39      | ~ v1_relat_1(X0) ),
% 31.68/4.39      inference(cnf_transformation,[],[f41]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_215,plain,
% 31.68/4.39      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.68/4.39      | r1_tarski(k1_relat_1(X0),X1)
% 31.68/4.39      | ~ v1_relat_1(X0) ),
% 31.68/4.39      inference(resolution,[status(thm)],[c_11,c_8]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_362,plain,
% 31.68/4.39      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 31.68/4.39      | r1_tarski(k1_relat_1(X0_43),X1_43)
% 31.68/4.39      | ~ v1_relat_1(X0_43) ),
% 31.68/4.39      inference(subtyping,[status(esa)],[c_215]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_751,plain,
% 31.68/4.39      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
% 31.68/4.39      | r1_tarski(k1_relat_1(X0_43),X1_43) = iProver_top
% 31.68/4.39      | v1_relat_1(X0_43) != iProver_top ),
% 31.68/4.39      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_2494,plain,
% 31.68/4.39      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 31.68/4.39      | v1_relat_1(sK2) != iProver_top ),
% 31.68/4.39      inference(superposition,[status(thm)],[c_749,c_751]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_10,plain,
% 31.68/4.39      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.68/4.39      inference(cnf_transformation,[],[f44]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_368,plain,
% 31.68/4.39      ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
% 31.68/4.39      inference(subtyping,[status(esa)],[c_10]) ).
% 31.68/4.39  
% 31.68/4.39  cnf(c_745,plain,
% 31.68/4.39      ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) = iProver_top ),
% 31.68/4.39      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_5,plain,
% 31.68/4.40      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.68/4.40      inference(cnf_transformation,[],[f38]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_370,plain,
% 31.68/4.40      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 31.68/4.40      | r1_tarski(X0_43,X1_43) ),
% 31.68/4.40      inference(subtyping,[status(esa)],[c_5]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_743,plain,
% 31.68/4.40      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 31.68/4.40      | r1_tarski(X0_43,X1_43) = iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_1079,plain,
% 31.68/4.40      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_749,c_743]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_6,plain,
% 31.68/4.40      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.68/4.40      | ~ v1_relat_1(X1)
% 31.68/4.40      | v1_relat_1(X0) ),
% 31.68/4.40      inference(cnf_transformation,[],[f40]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_4,plain,
% 31.68/4.40      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.68/4.40      inference(cnf_transformation,[],[f39]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_127,plain,
% 31.68/4.40      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.68/4.40      inference(prop_impl,[status(thm)],[c_4]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_128,plain,
% 31.68/4.40      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.68/4.40      inference(renaming,[status(thm)],[c_127]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_155,plain,
% 31.68/4.40      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.68/4.40      inference(bin_hyper_res,[status(thm)],[c_6,c_128]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_363,plain,
% 31.68/4.40      ( ~ r1_tarski(X0_43,X1_43)
% 31.68/4.40      | ~ v1_relat_1(X1_43)
% 31.68/4.40      | v1_relat_1(X0_43) ),
% 31.68/4.40      inference(subtyping,[status(esa)],[c_155]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_750,plain,
% 31.68/4.40      ( r1_tarski(X0_43,X1_43) != iProver_top
% 31.68/4.40      | v1_relat_1(X1_43) != iProver_top
% 31.68/4.40      | v1_relat_1(X0_43) = iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_1886,plain,
% 31.68/4.40      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.68/4.40      | v1_relat_1(sK2) = iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_1079,c_750]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_2133,plain,
% 31.68/4.40      ( v1_relat_1(sK2) = iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_745,c_1886]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_2619,plain,
% 31.68/4.40      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 31.68/4.40      inference(global_propositional_subsumption,
% 31.68/4.40                [status(thm)],
% 31.68/4.40                [c_2494,c_2133]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_1,plain,
% 31.68/4.40      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 31.68/4.40      inference(cnf_transformation,[],[f34]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_374,plain,
% 31.68/4.40      ( ~ r1_tarski(X0_43,X1_43)
% 31.68/4.40      | ~ r1_tarski(X1_43,X2_43)
% 31.68/4.40      | r1_tarski(X0_43,X2_43) ),
% 31.68/4.40      inference(subtyping,[status(esa)],[c_1]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_739,plain,
% 31.68/4.40      ( r1_tarski(X0_43,X1_43) != iProver_top
% 31.68/4.40      | r1_tarski(X1_43,X2_43) != iProver_top
% 31.68/4.40      | r1_tarski(X0_43,X2_43) = iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_2624,plain,
% 31.68/4.40      ( r1_tarski(k1_relat_1(sK2),X0_43) = iProver_top
% 31.68/4.40      | r1_tarski(sK0,X0_43) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_2619,c_739]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_2787,plain,
% 31.68/4.40      ( r1_tarski(X0_43,X1_43) != iProver_top
% 31.68/4.40      | r1_tarski(k1_relat_1(sK2),X1_43) = iProver_top
% 31.68/4.40      | r1_tarski(sK0,X0_43) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_2624,c_739]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_3146,plain,
% 31.68/4.40      ( r1_tarski(X0_43,X1_43) != iProver_top
% 31.68/4.40      | r1_tarski(k1_relat_1(sK2),k5_xboole_0(X2_43,k4_xboole_0(X1_43,X2_43))) = iProver_top
% 31.68/4.40      | r1_tarski(sK0,X0_43) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_738,c_2787]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_4095,plain,
% 31.68/4.40      ( r1_tarski(k1_relat_1(sK2),k5_xboole_0(X0_43,k4_xboole_0(sK0,X0_43))) = iProver_top
% 31.68/4.40      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_2619,c_3146]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_2,plain,
% 31.68/4.40      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 31.68/4.40      inference(cnf_transformation,[],[f51]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_373,plain,
% 31.68/4.40      ( r1_tarski(X0_43,k5_xboole_0(X0_43,k4_xboole_0(X1_43,X0_43))) ),
% 31.68/4.40      inference(subtyping,[status(esa)],[c_2]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_740,plain,
% 31.68/4.40      ( r1_tarski(X0_43,k5_xboole_0(X0_43,k4_xboole_0(X1_43,X0_43))) = iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_9,plain,
% 31.68/4.40      ( ~ v1_relat_1(X0)
% 31.68/4.40      | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
% 31.68/4.40      inference(cnf_transformation,[],[f53]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_369,plain,
% 31.68/4.40      ( ~ v1_relat_1(X0_43)
% 31.68/4.40      | k5_xboole_0(k1_relat_1(X0_43),k4_xboole_0(k2_relat_1(X0_43),k1_relat_1(X0_43))) = k3_relat_1(X0_43) ),
% 31.68/4.40      inference(subtyping,[status(esa)],[c_9]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_744,plain,
% 31.68/4.40      ( k5_xboole_0(k1_relat_1(X0_43),k4_xboole_0(k2_relat_1(X0_43),k1_relat_1(X0_43))) = k3_relat_1(X0_43)
% 31.68/4.40      | v1_relat_1(X0_43) != iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_2136,plain,
% 31.68/4.40      ( k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) = k3_relat_1(sK2) ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_2133,c_744]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_2331,plain,
% 31.68/4.40      ( r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
% 31.68/4.40      | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
% 31.68/4.40      | r1_tarski(k1_relat_1(sK2),X0_43) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_2136,c_741]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_8885,plain,
% 31.68/4.40      ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(X0_43,k2_relat_1(sK2)))) = iProver_top
% 31.68/4.40      | r1_tarski(k1_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(X0_43,k2_relat_1(sK2)))) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_740,c_2331]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_24022,plain,
% 31.68/4.40      ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))) = iProver_top
% 31.68/4.40      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_4095,c_8885]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_24015,plain,
% 31.68/4.40      ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(X0_43,k2_relat_1(sK2)))) = iProver_top
% 31.68/4.40      | r1_tarski(k1_relat_1(sK2),X0_43) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_738,c_8885]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_24028,plain,
% 31.68/4.40      ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))) = iProver_top
% 31.68/4.40      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 31.68/4.40      inference(instantiation,[status(thm)],[c_24015]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_24445,plain,
% 31.68/4.40      ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))) = iProver_top ),
% 31.68/4.40      inference(global_propositional_subsumption,
% 31.68/4.40                [status(thm)],
% 31.68/4.40                [c_24022,c_2133,c_2494,c_24028]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_24459,plain,
% 31.68/4.40      ( r1_tarski(k5_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2))),X0_43) != iProver_top
% 31.68/4.40      | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_24445,c_739]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_26840,plain,
% 31.68/4.40      ( r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
% 31.68/4.40      | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
% 31.68/4.40      | r1_tarski(sK0,X0_43) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_741,c_24459]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_27167,plain,
% 31.68/4.40      ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(X0_43,k4_xboole_0(X1_43,X0_43))) = iProver_top
% 31.68/4.40      | r1_tarski(k2_relat_1(sK2),X1_43) != iProver_top
% 31.68/4.40      | r1_tarski(sK0,k5_xboole_0(X0_43,k4_xboole_0(X1_43,X0_43))) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_738,c_26840]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_14,negated_conjecture,
% 31.68/4.40      ( ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 31.68/4.40      inference(cnf_transformation,[],[f54]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_365,negated_conjecture,
% 31.68/4.40      ( ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 31.68/4.40      inference(subtyping,[status(esa)],[c_14]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_748,plain,
% 31.68/4.40      ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_96235,plain,
% 31.68/4.40      ( r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
% 31.68/4.40      | r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_27167,c_748]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_13,plain,
% 31.68/4.40      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.68/4.40      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.68/4.40      inference(cnf_transformation,[],[f47]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_366,plain,
% 31.68/4.40      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 31.68/4.40      | k2_relset_1(X1_43,X2_43,X0_43) = k2_relat_1(X0_43) ),
% 31.68/4.40      inference(subtyping,[status(esa)],[c_13]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_747,plain,
% 31.68/4.40      ( k2_relset_1(X0_43,X1_43,X2_43) = k2_relat_1(X2_43)
% 31.68/4.40      | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_1365,plain,
% 31.68/4.40      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_749,c_747]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_12,plain,
% 31.68/4.40      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.68/4.40      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 31.68/4.40      inference(cnf_transformation,[],[f46]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_367,plain,
% 31.68/4.40      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 31.68/4.40      | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) ),
% 31.68/4.40      inference(subtyping,[status(esa)],[c_12]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_746,plain,
% 31.68/4.40      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
% 31.68/4.40      | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) = iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_1524,plain,
% 31.68/4.40      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 31.68/4.40      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_1365,c_746]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_16,plain,
% 31.68/4.40      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_1637,plain,
% 31.68/4.40      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 31.68/4.40      inference(global_propositional_subsumption,
% 31.68/4.40                [status(thm)],
% 31.68/4.40                [c_1524,c_16]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_1641,plain,
% 31.68/4.40      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 31.68/4.40      inference(superposition,[status(thm)],[c_1637,c_743]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_1501,plain,
% 31.68/4.40      ( r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 31.68/4.40      inference(instantiation,[status(thm)],[c_373]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(c_1502,plain,
% 31.68/4.40      ( r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = iProver_top ),
% 31.68/4.40      inference(predicate_to_equality,[status(thm)],[c_1501]) ).
% 31.68/4.40  
% 31.68/4.40  cnf(contradiction,plain,
% 31.68/4.40      ( $false ),
% 31.68/4.40      inference(minisat,[status(thm)],[c_96235,c_1641,c_1502]) ).
% 31.68/4.40  
% 31.68/4.40  
% 31.68/4.40  % SZS output end CNFRefutation for theBenchmark.p
% 31.68/4.40  
% 31.68/4.40  ------                               Statistics
% 31.68/4.40  
% 31.68/4.40  ------ General
% 31.68/4.40  
% 31.68/4.40  abstr_ref_over_cycles:                  0
% 31.68/4.40  abstr_ref_under_cycles:                 0
% 31.68/4.40  gc_basic_clause_elim:                   0
% 31.68/4.40  forced_gc_time:                         0
% 31.68/4.40  parsing_time:                           0.008
% 31.68/4.40  unif_index_cands_time:                  0.
% 31.68/4.40  unif_index_add_time:                    0.
% 31.68/4.40  orderings_time:                         0.
% 31.68/4.40  out_proof_time:                         0.015
% 31.68/4.40  total_time:                             3.894
% 31.68/4.40  num_of_symbols:                         49
% 31.68/4.40  num_of_terms:                           105502
% 31.68/4.40  
% 31.68/4.40  ------ Preprocessing
% 31.68/4.40  
% 31.68/4.40  num_of_splits:                          0
% 31.68/4.40  num_of_split_atoms:                     0
% 31.68/4.40  num_of_reused_defs:                     0
% 31.68/4.40  num_eq_ax_congr_red:                    17
% 31.68/4.40  num_of_sem_filtered_clauses:            1
% 31.68/4.40  num_of_subtypes:                        3
% 31.68/4.40  monotx_restored_types:                  0
% 31.68/4.40  sat_num_of_epr_types:                   0
% 31.68/4.40  sat_num_of_non_cyclic_types:            0
% 31.68/4.40  sat_guarded_non_collapsed_types:        0
% 31.68/4.40  num_pure_diseq_elim:                    0
% 31.68/4.40  simp_replaced_by:                       0
% 31.68/4.40  res_preprocessed:                       83
% 31.68/4.40  prep_upred:                             0
% 31.68/4.40  prep_unflattend:                        0
% 31.68/4.40  smt_new_axioms:                         0
% 31.68/4.40  pred_elim_cands:                        3
% 31.68/4.40  pred_elim:                              1
% 31.68/4.40  pred_elim_cl:                           2
% 31.68/4.40  pred_elim_cycles:                       3
% 31.68/4.40  merged_defs:                            8
% 31.68/4.40  merged_defs_ncl:                        0
% 31.68/4.40  bin_hyper_res:                          9
% 31.68/4.40  prep_cycles:                            4
% 31.68/4.40  pred_elim_time:                         0.001
% 31.68/4.40  splitting_time:                         0.
% 31.68/4.40  sem_filter_time:                        0.
% 31.68/4.40  monotx_time:                            0.
% 31.68/4.40  subtype_inf_time:                       0.
% 31.68/4.40  
% 31.68/4.40  ------ Problem properties
% 31.68/4.40  
% 31.68/4.40  clauses:                                14
% 31.68/4.40  conjectures:                            2
% 31.68/4.40  epr:                                    2
% 31.68/4.40  horn:                                   14
% 31.68/4.40  ground:                                 2
% 31.68/4.40  unary:                                  4
% 31.68/4.40  binary:                                 6
% 31.68/4.40  lits:                                   28
% 31.68/4.40  lits_eq:                                2
% 31.68/4.40  fd_pure:                                0
% 31.68/4.40  fd_pseudo:                              0
% 31.68/4.40  fd_cond:                                0
% 31.68/4.40  fd_pseudo_cond:                         0
% 31.68/4.40  ac_symbols:                             0
% 31.68/4.40  
% 31.68/4.40  ------ Propositional Solver
% 31.68/4.40  
% 31.68/4.40  prop_solver_calls:                      40
% 31.68/4.40  prop_fast_solver_calls:                 1597
% 31.68/4.40  smt_solver_calls:                       0
% 31.68/4.40  smt_fast_solver_calls:                  0
% 31.68/4.40  prop_num_of_clauses:                    39993
% 31.68/4.40  prop_preprocess_simplified:             51309
% 31.68/4.40  prop_fo_subsumed:                       53
% 31.68/4.40  prop_solver_time:                       0.
% 31.68/4.40  smt_solver_time:                        0.
% 31.68/4.40  smt_fast_solver_time:                   0.
% 31.68/4.40  prop_fast_solver_time:                  0.
% 31.68/4.40  prop_unsat_core_time:                   0.005
% 31.68/4.40  
% 31.68/4.40  ------ QBF
% 31.68/4.40  
% 31.68/4.40  qbf_q_res:                              0
% 31.68/4.40  qbf_num_tautologies:                    0
% 31.68/4.40  qbf_prep_cycles:                        0
% 31.68/4.40  
% 31.68/4.40  ------ BMC1
% 31.68/4.40  
% 31.68/4.40  bmc1_current_bound:                     -1
% 31.68/4.40  bmc1_last_solved_bound:                 -1
% 31.68/4.40  bmc1_unsat_core_size:                   -1
% 31.68/4.40  bmc1_unsat_core_parents_size:           -1
% 31.68/4.40  bmc1_merge_next_fun:                    0
% 31.68/4.40  bmc1_unsat_core_clauses_time:           0.
% 31.68/4.40  
% 31.68/4.40  ------ Instantiation
% 31.68/4.40  
% 31.68/4.40  inst_num_of_clauses:                    8790
% 31.68/4.40  inst_num_in_passive:                    2620
% 31.68/4.40  inst_num_in_active:                     1976
% 31.68/4.40  inst_num_in_unprocessed:                4197
% 31.68/4.40  inst_num_of_loops:                      2090
% 31.68/4.40  inst_num_of_learning_restarts:          0
% 31.68/4.40  inst_num_moves_active_passive:          110
% 31.68/4.40  inst_lit_activity:                      0
% 31.68/4.40  inst_lit_activity_moves:                2
% 31.68/4.40  inst_num_tautologies:                   0
% 31.68/4.40  inst_num_prop_implied:                  0
% 31.68/4.40  inst_num_existing_simplified:           0
% 31.68/4.40  inst_num_eq_res_simplified:             0
% 31.68/4.40  inst_num_child_elim:                    0
% 31.68/4.40  inst_num_of_dismatching_blockings:      22480
% 31.68/4.40  inst_num_of_non_proper_insts:           14866
% 31.68/4.40  inst_num_of_duplicates:                 0
% 31.68/4.40  inst_inst_num_from_inst_to_res:         0
% 31.68/4.40  inst_dismatching_checking_time:         0.
% 31.68/4.40  
% 31.68/4.40  ------ Resolution
% 31.68/4.40  
% 31.68/4.40  res_num_of_clauses:                     0
% 31.68/4.40  res_num_in_passive:                     0
% 31.68/4.40  res_num_in_active:                      0
% 31.68/4.40  res_num_of_loops:                       87
% 31.68/4.40  res_forward_subset_subsumed:            1736
% 31.68/4.40  res_backward_subset_subsumed:           6
% 31.68/4.40  res_forward_subsumed:                   0
% 31.68/4.40  res_backward_subsumed:                  0
% 31.68/4.40  res_forward_subsumption_resolution:     0
% 31.68/4.40  res_backward_subsumption_resolution:    0
% 31.68/4.40  res_clause_to_clause_subsumption:       55610
% 31.68/4.40  res_orphan_elimination:                 0
% 31.68/4.40  res_tautology_del:                      679
% 31.68/4.40  res_num_eq_res_simplified:              0
% 31.68/4.40  res_num_sel_changes:                    0
% 31.68/4.40  res_moves_from_active_to_pass:          0
% 31.68/4.40  
% 31.68/4.40  ------ Superposition
% 31.68/4.40  
% 31.68/4.40  sup_time_total:                         0.
% 31.68/4.40  sup_time_generating:                    0.
% 31.68/4.40  sup_time_sim_full:                      0.
% 31.68/4.40  sup_time_sim_immed:                     0.
% 31.68/4.40  
% 31.68/4.40  sup_num_of_clauses:                     3795
% 31.68/4.40  sup_num_in_active:                      381
% 31.68/4.40  sup_num_in_passive:                     3414
% 31.68/4.40  sup_num_of_loops:                       417
% 31.68/4.40  sup_fw_superposition:                   3628
% 31.68/4.40  sup_bw_superposition:                   2840
% 31.68/4.40  sup_immediate_simplified:               1883
% 31.68/4.40  sup_given_eliminated:                   9
% 31.68/4.40  comparisons_done:                       0
% 31.68/4.40  comparisons_avoided:                    0
% 31.68/4.40  
% 31.68/4.40  ------ Simplifications
% 31.68/4.40  
% 31.68/4.40  
% 31.68/4.40  sim_fw_subset_subsumed:                 873
% 31.68/4.40  sim_bw_subset_subsumed:                 58
% 31.68/4.40  sim_fw_subsumed:                        908
% 31.68/4.40  sim_bw_subsumed:                        176
% 31.68/4.40  sim_fw_subsumption_res:                 0
% 31.68/4.40  sim_bw_subsumption_res:                 0
% 31.68/4.40  sim_tautology_del:                      10
% 31.68/4.40  sim_eq_tautology_del:                   0
% 31.68/4.40  sim_eq_res_simp:                        0
% 31.68/4.40  sim_fw_demodulated:                     2
% 31.68/4.40  sim_bw_demodulated:                     0
% 31.68/4.40  sim_light_normalised:                   19
% 31.68/4.40  sim_joinable_taut:                      0
% 31.68/4.40  sim_joinable_simp:                      0
% 31.68/4.40  sim_ac_normalised:                      0
% 31.68/4.40  sim_smt_subsumption:                    0
% 31.68/4.40  
%------------------------------------------------------------------------------
