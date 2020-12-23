%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:34 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 224 expanded)
%              Number of clauses        :   59 ( 111 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  192 ( 448 expanded)
%              Number of equality atoms :   60 ( 103 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f22])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_170,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_526,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_173,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | k5_relset_1(X1_42,X2_42,X0_42,X3_42) = k7_relat_1(X0_42,X3_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_523,plain,
    ( k5_relset_1(X0_42,X1_42,X2_42,X3_42) = k7_relat_1(X2_42,X3_42)
    | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_173])).

cnf(c_1032,plain,
    ( k5_relset_1(sK0,sK2,sK3,X0_42) = k7_relat_1(sK3,X0_42) ),
    inference(superposition,[status(thm)],[c_526,c_523])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k5_relset_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_175,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | m1_subset_1(k5_relset_1(X1_42,X2_42,X0_42,X3_42),k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_521,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) != iProver_top
    | m1_subset_1(k5_relset_1(X1_42,X2_42,X0_42,X3_42),k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_175])).

cnf(c_1267,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0_42),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1032,c_521])).

cnf(c_12,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1384,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0_42),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1267,c_12])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_179,plain,
    ( r1_tarski(X0_42,X1_42)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_517,plain,
    ( r1_tarski(X0_42,X1_42) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_179])).

cnf(c_1391,plain,
    ( r1_tarski(k7_relat_1(sK3,X0_42),k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_517])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_99,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_99])).

cnf(c_169,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ v1_relat_1(X1_42)
    | v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_122])).

cnf(c_527,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_2471,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0_42)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_527])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_178,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_42,X1_42)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1100,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_1101,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1100])).

cnf(c_2996,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0_42)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2471,c_1101])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_177,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_42,X1_42)),X1_42)
    | ~ v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_519,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_42,X1_42)),X1_42) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_177])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | m1_subset_1(k2_relset_1(X1_42,X2_42,X0_42),k1_zfmisc_1(X2_42)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_520,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_42,X2_42,X0_42),k1_zfmisc_1(X2_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_918,plain,
    ( r1_tarski(k2_relset_1(X0_42,X1_42,X2_42),X1_42) = iProver_top
    | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(superposition,[status(thm)],[c_520,c_517])).

cnf(c_1520,plain,
    ( r1_tarski(k2_relset_1(sK0,sK2,k7_relat_1(sK3,X0_42)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_918])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | k2_relset_1(X1_42,X2_42,X0_42) = k2_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_522,plain,
    ( k2_relset_1(X0_42,X1_42,X2_42) = k2_relat_1(X2_42)
    | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_1393,plain,
    ( k2_relset_1(sK0,sK2,k7_relat_1(sK3,X0_42)) = k2_relat_1(k7_relat_1(sK3,X0_42)) ),
    inference(superposition,[status(thm)],[c_1384,c_522])).

cnf(c_1790,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_42)),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1520,c_1393])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_172,plain,
    ( ~ r1_tarski(k2_relat_1(X0_42),X1_42)
    | ~ r1_tarski(k1_relat_1(X0_42),X2_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X1_42)))
    | ~ v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_524,plain,
    ( r1_tarski(k2_relat_1(X0_42),X1_42) != iProver_top
    | r1_tarski(k1_relat_1(X0_42),X2_42) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X1_42))) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_172])).

cnf(c_10,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_171,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_525,plain,
    ( m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_1260,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1032,c_525])).

cnf(c_1273,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_524,c_1260])).

cnf(c_1795,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_1273])).

cnf(c_1955,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_519,c_1795])).

cnf(c_603,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_604,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_636,plain,
    ( ~ r1_tarski(X0_42,k2_zfmisc_1(X1_42,X2_42))
    | v1_relat_1(X0_42)
    | ~ v1_relat_1(k2_zfmisc_1(X1_42,X2_42)) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_845,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_846,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_1958,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1955,c_12,c_604,c_846,c_1101])).

cnf(c_3003,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2996,c_1958])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.52/1.09  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.09  
% 1.52/1.09  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.52/1.09  
% 1.52/1.09  ------  iProver source info
% 1.52/1.09  
% 1.52/1.09  git: date: 2020-06-30 10:37:57 +0100
% 1.52/1.09  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.52/1.09  git: non_committed_changes: false
% 1.52/1.09  git: last_make_outside_of_git: false
% 1.52/1.09  
% 1.52/1.09  ------ 
% 1.52/1.09  
% 1.52/1.09  ------ Input Options
% 1.52/1.09  
% 1.52/1.09  --out_options                           all
% 1.52/1.09  --tptp_safe_out                         true
% 1.52/1.09  --problem_path                          ""
% 1.52/1.09  --include_path                          ""
% 1.52/1.09  --clausifier                            res/vclausify_rel
% 1.52/1.09  --clausifier_options                    --mode clausify
% 1.52/1.09  --stdin                                 false
% 1.52/1.09  --stats_out                             all
% 1.52/1.09  
% 1.52/1.09  ------ General Options
% 1.52/1.09  
% 1.52/1.09  --fof                                   false
% 1.52/1.09  --time_out_real                         305.
% 1.52/1.09  --time_out_virtual                      -1.
% 1.52/1.09  --symbol_type_check                     false
% 1.52/1.09  --clausify_out                          false
% 1.52/1.09  --sig_cnt_out                           false
% 1.52/1.09  --trig_cnt_out                          false
% 1.52/1.09  --trig_cnt_out_tolerance                1.
% 1.52/1.09  --trig_cnt_out_sk_spl                   false
% 1.52/1.09  --abstr_cl_out                          false
% 1.52/1.09  
% 1.52/1.09  ------ Global Options
% 1.52/1.09  
% 1.52/1.09  --schedule                              default
% 1.52/1.09  --add_important_lit                     false
% 1.52/1.09  --prop_solver_per_cl                    1000
% 1.52/1.09  --min_unsat_core                        false
% 1.52/1.09  --soft_assumptions                      false
% 1.52/1.09  --soft_lemma_size                       3
% 1.52/1.09  --prop_impl_unit_size                   0
% 1.52/1.09  --prop_impl_unit                        []
% 1.52/1.09  --share_sel_clauses                     true
% 1.52/1.09  --reset_solvers                         false
% 1.52/1.09  --bc_imp_inh                            [conj_cone]
% 1.52/1.09  --conj_cone_tolerance                   3.
% 1.52/1.09  --extra_neg_conj                        none
% 1.52/1.09  --large_theory_mode                     true
% 1.52/1.09  --prolific_symb_bound                   200
% 1.52/1.09  --lt_threshold                          2000
% 1.52/1.09  --clause_weak_htbl                      true
% 1.52/1.09  --gc_record_bc_elim                     false
% 1.52/1.09  
% 1.52/1.09  ------ Preprocessing Options
% 1.52/1.09  
% 1.52/1.09  --preprocessing_flag                    true
% 1.52/1.09  --time_out_prep_mult                    0.1
% 1.52/1.09  --splitting_mode                        input
% 1.52/1.09  --splitting_grd                         true
% 1.52/1.09  --splitting_cvd                         false
% 1.52/1.09  --splitting_cvd_svl                     false
% 1.52/1.09  --splitting_nvd                         32
% 1.52/1.09  --sub_typing                            true
% 1.52/1.09  --prep_gs_sim                           true
% 1.52/1.09  --prep_unflatten                        true
% 1.52/1.09  --prep_res_sim                          true
% 1.52/1.09  --prep_upred                            true
% 1.52/1.09  --prep_sem_filter                       exhaustive
% 1.52/1.09  --prep_sem_filter_out                   false
% 1.52/1.09  --pred_elim                             true
% 1.52/1.09  --res_sim_input                         true
% 1.52/1.09  --eq_ax_congr_red                       true
% 1.52/1.09  --pure_diseq_elim                       true
% 1.52/1.09  --brand_transform                       false
% 1.52/1.09  --non_eq_to_eq                          false
% 1.52/1.09  --prep_def_merge                        true
% 1.52/1.09  --prep_def_merge_prop_impl              false
% 1.52/1.09  --prep_def_merge_mbd                    true
% 1.52/1.09  --prep_def_merge_tr_red                 false
% 1.52/1.09  --prep_def_merge_tr_cl                  false
% 1.52/1.09  --smt_preprocessing                     true
% 1.52/1.09  --smt_ac_axioms                         fast
% 1.52/1.09  --preprocessed_out                      false
% 1.52/1.09  --preprocessed_stats                    false
% 1.52/1.09  
% 1.52/1.09  ------ Abstraction refinement Options
% 1.52/1.09  
% 1.52/1.09  --abstr_ref                             []
% 1.52/1.09  --abstr_ref_prep                        false
% 1.52/1.09  --abstr_ref_until_sat                   false
% 1.52/1.09  --abstr_ref_sig_restrict                funpre
% 1.52/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/1.09  --abstr_ref_under                       []
% 1.52/1.09  
% 1.52/1.09  ------ SAT Options
% 1.52/1.09  
% 1.52/1.09  --sat_mode                              false
% 1.52/1.09  --sat_fm_restart_options                ""
% 1.52/1.09  --sat_gr_def                            false
% 1.52/1.09  --sat_epr_types                         true
% 1.52/1.09  --sat_non_cyclic_types                  false
% 1.52/1.09  --sat_finite_models                     false
% 1.52/1.09  --sat_fm_lemmas                         false
% 1.52/1.09  --sat_fm_prep                           false
% 1.52/1.09  --sat_fm_uc_incr                        true
% 1.52/1.09  --sat_out_model                         small
% 1.52/1.09  --sat_out_clauses                       false
% 1.52/1.09  
% 1.52/1.09  ------ QBF Options
% 1.52/1.09  
% 1.52/1.09  --qbf_mode                              false
% 1.52/1.09  --qbf_elim_univ                         false
% 1.52/1.09  --qbf_dom_inst                          none
% 1.52/1.09  --qbf_dom_pre_inst                      false
% 1.52/1.09  --qbf_sk_in                             false
% 1.52/1.09  --qbf_pred_elim                         true
% 1.52/1.09  --qbf_split                             512
% 1.52/1.09  
% 1.52/1.09  ------ BMC1 Options
% 1.52/1.09  
% 1.52/1.09  --bmc1_incremental                      false
% 1.52/1.09  --bmc1_axioms                           reachable_all
% 1.52/1.09  --bmc1_min_bound                        0
% 1.52/1.09  --bmc1_max_bound                        -1
% 1.52/1.09  --bmc1_max_bound_default                -1
% 1.52/1.09  --bmc1_symbol_reachability              true
% 1.52/1.09  --bmc1_property_lemmas                  false
% 1.52/1.09  --bmc1_k_induction                      false
% 1.52/1.09  --bmc1_non_equiv_states                 false
% 1.52/1.09  --bmc1_deadlock                         false
% 1.52/1.09  --bmc1_ucm                              false
% 1.52/1.09  --bmc1_add_unsat_core                   none
% 1.52/1.09  --bmc1_unsat_core_children              false
% 1.52/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/1.09  --bmc1_out_stat                         full
% 1.52/1.09  --bmc1_ground_init                      false
% 1.52/1.09  --bmc1_pre_inst_next_state              false
% 1.52/1.09  --bmc1_pre_inst_state                   false
% 1.52/1.09  --bmc1_pre_inst_reach_state             false
% 1.52/1.09  --bmc1_out_unsat_core                   false
% 1.52/1.09  --bmc1_aig_witness_out                  false
% 1.52/1.09  --bmc1_verbose                          false
% 1.52/1.09  --bmc1_dump_clauses_tptp                false
% 1.52/1.09  --bmc1_dump_unsat_core_tptp             false
% 1.52/1.09  --bmc1_dump_file                        -
% 1.52/1.09  --bmc1_ucm_expand_uc_limit              128
% 1.52/1.09  --bmc1_ucm_n_expand_iterations          6
% 1.52/1.09  --bmc1_ucm_extend_mode                  1
% 1.52/1.09  --bmc1_ucm_init_mode                    2
% 1.52/1.09  --bmc1_ucm_cone_mode                    none
% 1.52/1.09  --bmc1_ucm_reduced_relation_type        0
% 1.52/1.09  --bmc1_ucm_relax_model                  4
% 1.52/1.09  --bmc1_ucm_full_tr_after_sat            true
% 1.52/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/1.09  --bmc1_ucm_layered_model                none
% 1.52/1.09  --bmc1_ucm_max_lemma_size               10
% 1.52/1.09  
% 1.52/1.09  ------ AIG Options
% 1.52/1.09  
% 1.52/1.09  --aig_mode                              false
% 1.52/1.09  
% 1.52/1.09  ------ Instantiation Options
% 1.52/1.09  
% 1.52/1.09  --instantiation_flag                    true
% 1.52/1.09  --inst_sos_flag                         false
% 1.52/1.09  --inst_sos_phase                        true
% 1.52/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/1.09  --inst_lit_sel_side                     num_symb
% 1.52/1.09  --inst_solver_per_active                1400
% 1.52/1.09  --inst_solver_calls_frac                1.
% 1.52/1.09  --inst_passive_queue_type               priority_queues
% 1.52/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/1.09  --inst_passive_queues_freq              [25;2]
% 1.52/1.09  --inst_dismatching                      true
% 1.52/1.09  --inst_eager_unprocessed_to_passive     true
% 1.52/1.09  --inst_prop_sim_given                   true
% 1.52/1.09  --inst_prop_sim_new                     false
% 1.52/1.09  --inst_subs_new                         false
% 1.52/1.09  --inst_eq_res_simp                      false
% 1.52/1.09  --inst_subs_given                       false
% 1.52/1.09  --inst_orphan_elimination               true
% 1.52/1.09  --inst_learning_loop_flag               true
% 1.52/1.09  --inst_learning_start                   3000
% 1.52/1.09  --inst_learning_factor                  2
% 1.52/1.09  --inst_start_prop_sim_after_learn       3
% 1.52/1.09  --inst_sel_renew                        solver
% 1.52/1.09  --inst_lit_activity_flag                true
% 1.52/1.09  --inst_restr_to_given                   false
% 1.52/1.09  --inst_activity_threshold               500
% 1.52/1.09  --inst_out_proof                        true
% 1.52/1.09  
% 1.52/1.09  ------ Resolution Options
% 1.52/1.09  
% 1.52/1.09  --resolution_flag                       true
% 1.52/1.09  --res_lit_sel                           adaptive
% 1.52/1.09  --res_lit_sel_side                      none
% 1.52/1.09  --res_ordering                          kbo
% 1.52/1.09  --res_to_prop_solver                    active
% 1.52/1.09  --res_prop_simpl_new                    false
% 1.52/1.09  --res_prop_simpl_given                  true
% 1.52/1.09  --res_passive_queue_type                priority_queues
% 1.52/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/1.09  --res_passive_queues_freq               [15;5]
% 1.52/1.09  --res_forward_subs                      full
% 1.52/1.09  --res_backward_subs                     full
% 1.52/1.09  --res_forward_subs_resolution           true
% 1.52/1.09  --res_backward_subs_resolution          true
% 1.52/1.09  --res_orphan_elimination                true
% 1.52/1.09  --res_time_limit                        2.
% 1.52/1.09  --res_out_proof                         true
% 1.52/1.09  
% 1.52/1.09  ------ Superposition Options
% 1.52/1.09  
% 1.52/1.09  --superposition_flag                    true
% 1.52/1.09  --sup_passive_queue_type                priority_queues
% 1.52/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/1.09  --sup_passive_queues_freq               [8;1;4]
% 1.52/1.09  --demod_completeness_check              fast
% 1.52/1.09  --demod_use_ground                      true
% 1.52/1.09  --sup_to_prop_solver                    passive
% 1.52/1.09  --sup_prop_simpl_new                    true
% 1.52/1.09  --sup_prop_simpl_given                  true
% 1.52/1.09  --sup_fun_splitting                     false
% 1.52/1.09  --sup_smt_interval                      50000
% 1.52/1.09  
% 1.52/1.09  ------ Superposition Simplification Setup
% 1.52/1.09  
% 1.52/1.09  --sup_indices_passive                   []
% 1.52/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/1.09  --sup_full_bw                           [BwDemod]
% 1.52/1.09  --sup_immed_triv                        [TrivRules]
% 1.52/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/1.09  --sup_immed_bw_main                     []
% 1.52/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/1.09  
% 1.52/1.09  ------ Combination Options
% 1.52/1.09  
% 1.52/1.09  --comb_res_mult                         3
% 1.52/1.09  --comb_sup_mult                         2
% 1.52/1.09  --comb_inst_mult                        10
% 1.52/1.09  
% 1.52/1.09  ------ Debug Options
% 1.52/1.09  
% 1.52/1.09  --dbg_backtrace                         false
% 1.52/1.09  --dbg_dump_prop_clauses                 false
% 1.52/1.09  --dbg_dump_prop_clauses_file            -
% 1.52/1.09  --dbg_out_stat                          false
% 1.52/1.09  ------ Parsing...
% 1.52/1.09  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.52/1.09  
% 1.52/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.52/1.09  
% 1.52/1.09  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.52/1.09  
% 1.52/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.52/1.09  ------ Proving...
% 1.52/1.09  ------ Problem Properties 
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  clauses                                 12
% 1.52/1.09  conjectures                             2
% 1.52/1.09  EPR                                     1
% 1.52/1.09  Horn                                    12
% 1.52/1.09  unary                                   3
% 1.52/1.09  binary                                  7
% 1.52/1.09  lits                                    24
% 1.52/1.09  lits eq                                 2
% 1.52/1.09  fd_pure                                 0
% 1.52/1.09  fd_pseudo                               0
% 1.52/1.09  fd_cond                                 0
% 1.52/1.09  fd_pseudo_cond                          0
% 1.52/1.09  AC symbols                              0
% 1.52/1.09  
% 1.52/1.09  ------ Schedule dynamic 5 is on 
% 1.52/1.09  
% 1.52/1.09  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  ------ 
% 1.52/1.09  Current options:
% 1.52/1.09  ------ 
% 1.52/1.09  
% 1.52/1.09  ------ Input Options
% 1.52/1.09  
% 1.52/1.09  --out_options                           all
% 1.52/1.09  --tptp_safe_out                         true
% 1.52/1.09  --problem_path                          ""
% 1.52/1.09  --include_path                          ""
% 1.52/1.09  --clausifier                            res/vclausify_rel
% 1.52/1.09  --clausifier_options                    --mode clausify
% 1.52/1.09  --stdin                                 false
% 1.52/1.09  --stats_out                             all
% 1.52/1.09  
% 1.52/1.09  ------ General Options
% 1.52/1.09  
% 1.52/1.09  --fof                                   false
% 1.52/1.09  --time_out_real                         305.
% 1.52/1.09  --time_out_virtual                      -1.
% 1.52/1.09  --symbol_type_check                     false
% 1.52/1.09  --clausify_out                          false
% 1.52/1.09  --sig_cnt_out                           false
% 1.52/1.09  --trig_cnt_out                          false
% 1.52/1.09  --trig_cnt_out_tolerance                1.
% 1.52/1.09  --trig_cnt_out_sk_spl                   false
% 1.52/1.09  --abstr_cl_out                          false
% 1.52/1.09  
% 1.52/1.09  ------ Global Options
% 1.52/1.09  
% 1.52/1.09  --schedule                              default
% 1.52/1.09  --add_important_lit                     false
% 1.52/1.09  --prop_solver_per_cl                    1000
% 1.52/1.09  --min_unsat_core                        false
% 1.52/1.09  --soft_assumptions                      false
% 1.52/1.09  --soft_lemma_size                       3
% 1.52/1.09  --prop_impl_unit_size                   0
% 1.52/1.09  --prop_impl_unit                        []
% 1.52/1.09  --share_sel_clauses                     true
% 1.52/1.09  --reset_solvers                         false
% 1.52/1.09  --bc_imp_inh                            [conj_cone]
% 1.52/1.09  --conj_cone_tolerance                   3.
% 1.52/1.09  --extra_neg_conj                        none
% 1.52/1.09  --large_theory_mode                     true
% 1.52/1.09  --prolific_symb_bound                   200
% 1.52/1.09  --lt_threshold                          2000
% 1.52/1.09  --clause_weak_htbl                      true
% 1.52/1.09  --gc_record_bc_elim                     false
% 1.52/1.09  
% 1.52/1.09  ------ Preprocessing Options
% 1.52/1.09  
% 1.52/1.09  --preprocessing_flag                    true
% 1.52/1.09  --time_out_prep_mult                    0.1
% 1.52/1.09  --splitting_mode                        input
% 1.52/1.09  --splitting_grd                         true
% 1.52/1.09  --splitting_cvd                         false
% 1.52/1.09  --splitting_cvd_svl                     false
% 1.52/1.09  --splitting_nvd                         32
% 1.52/1.09  --sub_typing                            true
% 1.52/1.09  --prep_gs_sim                           true
% 1.52/1.09  --prep_unflatten                        true
% 1.52/1.09  --prep_res_sim                          true
% 1.52/1.09  --prep_upred                            true
% 1.52/1.09  --prep_sem_filter                       exhaustive
% 1.52/1.09  --prep_sem_filter_out                   false
% 1.52/1.09  --pred_elim                             true
% 1.52/1.09  --res_sim_input                         true
% 1.52/1.09  --eq_ax_congr_red                       true
% 1.52/1.09  --pure_diseq_elim                       true
% 1.52/1.09  --brand_transform                       false
% 1.52/1.09  --non_eq_to_eq                          false
% 1.52/1.09  --prep_def_merge                        true
% 1.52/1.09  --prep_def_merge_prop_impl              false
% 1.52/1.09  --prep_def_merge_mbd                    true
% 1.52/1.09  --prep_def_merge_tr_red                 false
% 1.52/1.09  --prep_def_merge_tr_cl                  false
% 1.52/1.09  --smt_preprocessing                     true
% 1.52/1.09  --smt_ac_axioms                         fast
% 1.52/1.09  --preprocessed_out                      false
% 1.52/1.09  --preprocessed_stats                    false
% 1.52/1.09  
% 1.52/1.09  ------ Abstraction refinement Options
% 1.52/1.09  
% 1.52/1.09  --abstr_ref                             []
% 1.52/1.09  --abstr_ref_prep                        false
% 1.52/1.09  --abstr_ref_until_sat                   false
% 1.52/1.09  --abstr_ref_sig_restrict                funpre
% 1.52/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/1.09  --abstr_ref_under                       []
% 1.52/1.09  
% 1.52/1.09  ------ SAT Options
% 1.52/1.09  
% 1.52/1.09  --sat_mode                              false
% 1.52/1.09  --sat_fm_restart_options                ""
% 1.52/1.09  --sat_gr_def                            false
% 1.52/1.09  --sat_epr_types                         true
% 1.52/1.09  --sat_non_cyclic_types                  false
% 1.52/1.09  --sat_finite_models                     false
% 1.52/1.09  --sat_fm_lemmas                         false
% 1.52/1.09  --sat_fm_prep                           false
% 1.52/1.09  --sat_fm_uc_incr                        true
% 1.52/1.09  --sat_out_model                         small
% 1.52/1.09  --sat_out_clauses                       false
% 1.52/1.09  
% 1.52/1.09  ------ QBF Options
% 1.52/1.09  
% 1.52/1.09  --qbf_mode                              false
% 1.52/1.09  --qbf_elim_univ                         false
% 1.52/1.09  --qbf_dom_inst                          none
% 1.52/1.09  --qbf_dom_pre_inst                      false
% 1.52/1.09  --qbf_sk_in                             false
% 1.52/1.09  --qbf_pred_elim                         true
% 1.52/1.09  --qbf_split                             512
% 1.52/1.09  
% 1.52/1.09  ------ BMC1 Options
% 1.52/1.09  
% 1.52/1.09  --bmc1_incremental                      false
% 1.52/1.09  --bmc1_axioms                           reachable_all
% 1.52/1.09  --bmc1_min_bound                        0
% 1.52/1.09  --bmc1_max_bound                        -1
% 1.52/1.09  --bmc1_max_bound_default                -1
% 1.52/1.09  --bmc1_symbol_reachability              true
% 1.52/1.09  --bmc1_property_lemmas                  false
% 1.52/1.09  --bmc1_k_induction                      false
% 1.52/1.09  --bmc1_non_equiv_states                 false
% 1.52/1.09  --bmc1_deadlock                         false
% 1.52/1.09  --bmc1_ucm                              false
% 1.52/1.09  --bmc1_add_unsat_core                   none
% 1.52/1.09  --bmc1_unsat_core_children              false
% 1.52/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/1.09  --bmc1_out_stat                         full
% 1.52/1.09  --bmc1_ground_init                      false
% 1.52/1.09  --bmc1_pre_inst_next_state              false
% 1.52/1.09  --bmc1_pre_inst_state                   false
% 1.52/1.09  --bmc1_pre_inst_reach_state             false
% 1.52/1.09  --bmc1_out_unsat_core                   false
% 1.52/1.09  --bmc1_aig_witness_out                  false
% 1.52/1.09  --bmc1_verbose                          false
% 1.52/1.09  --bmc1_dump_clauses_tptp                false
% 1.52/1.09  --bmc1_dump_unsat_core_tptp             false
% 1.52/1.09  --bmc1_dump_file                        -
% 1.52/1.09  --bmc1_ucm_expand_uc_limit              128
% 1.52/1.09  --bmc1_ucm_n_expand_iterations          6
% 1.52/1.09  --bmc1_ucm_extend_mode                  1
% 1.52/1.09  --bmc1_ucm_init_mode                    2
% 1.52/1.09  --bmc1_ucm_cone_mode                    none
% 1.52/1.09  --bmc1_ucm_reduced_relation_type        0
% 1.52/1.09  --bmc1_ucm_relax_model                  4
% 1.52/1.09  --bmc1_ucm_full_tr_after_sat            true
% 1.52/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/1.09  --bmc1_ucm_layered_model                none
% 1.52/1.09  --bmc1_ucm_max_lemma_size               10
% 1.52/1.09  
% 1.52/1.09  ------ AIG Options
% 1.52/1.09  
% 1.52/1.09  --aig_mode                              false
% 1.52/1.09  
% 1.52/1.09  ------ Instantiation Options
% 1.52/1.09  
% 1.52/1.09  --instantiation_flag                    true
% 1.52/1.09  --inst_sos_flag                         false
% 1.52/1.09  --inst_sos_phase                        true
% 1.52/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/1.09  --inst_lit_sel_side                     none
% 1.52/1.09  --inst_solver_per_active                1400
% 1.52/1.09  --inst_solver_calls_frac                1.
% 1.52/1.09  --inst_passive_queue_type               priority_queues
% 1.52/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/1.09  --inst_passive_queues_freq              [25;2]
% 1.52/1.09  --inst_dismatching                      true
% 1.52/1.09  --inst_eager_unprocessed_to_passive     true
% 1.52/1.09  --inst_prop_sim_given                   true
% 1.52/1.09  --inst_prop_sim_new                     false
% 1.52/1.09  --inst_subs_new                         false
% 1.52/1.09  --inst_eq_res_simp                      false
% 1.52/1.09  --inst_subs_given                       false
% 1.52/1.09  --inst_orphan_elimination               true
% 1.52/1.09  --inst_learning_loop_flag               true
% 1.52/1.09  --inst_learning_start                   3000
% 1.52/1.09  --inst_learning_factor                  2
% 1.52/1.09  --inst_start_prop_sim_after_learn       3
% 1.52/1.09  --inst_sel_renew                        solver
% 1.52/1.09  --inst_lit_activity_flag                true
% 1.52/1.09  --inst_restr_to_given                   false
% 1.52/1.09  --inst_activity_threshold               500
% 1.52/1.09  --inst_out_proof                        true
% 1.52/1.09  
% 1.52/1.09  ------ Resolution Options
% 1.52/1.09  
% 1.52/1.09  --resolution_flag                       false
% 1.52/1.09  --res_lit_sel                           adaptive
% 1.52/1.09  --res_lit_sel_side                      none
% 1.52/1.09  --res_ordering                          kbo
% 1.52/1.09  --res_to_prop_solver                    active
% 1.52/1.09  --res_prop_simpl_new                    false
% 1.52/1.09  --res_prop_simpl_given                  true
% 1.52/1.09  --res_passive_queue_type                priority_queues
% 1.52/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/1.09  --res_passive_queues_freq               [15;5]
% 1.52/1.09  --res_forward_subs                      full
% 1.52/1.09  --res_backward_subs                     full
% 1.52/1.09  --res_forward_subs_resolution           true
% 1.52/1.09  --res_backward_subs_resolution          true
% 1.52/1.09  --res_orphan_elimination                true
% 1.52/1.09  --res_time_limit                        2.
% 1.52/1.09  --res_out_proof                         true
% 1.52/1.09  
% 1.52/1.09  ------ Superposition Options
% 1.52/1.09  
% 1.52/1.09  --superposition_flag                    true
% 1.52/1.09  --sup_passive_queue_type                priority_queues
% 1.52/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/1.09  --sup_passive_queues_freq               [8;1;4]
% 1.52/1.09  --demod_completeness_check              fast
% 1.52/1.09  --demod_use_ground                      true
% 1.52/1.09  --sup_to_prop_solver                    passive
% 1.52/1.09  --sup_prop_simpl_new                    true
% 1.52/1.09  --sup_prop_simpl_given                  true
% 1.52/1.09  --sup_fun_splitting                     false
% 1.52/1.09  --sup_smt_interval                      50000
% 1.52/1.09  
% 1.52/1.09  ------ Superposition Simplification Setup
% 1.52/1.09  
% 1.52/1.09  --sup_indices_passive                   []
% 1.52/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/1.09  --sup_full_bw                           [BwDemod]
% 1.52/1.09  --sup_immed_triv                        [TrivRules]
% 1.52/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/1.09  --sup_immed_bw_main                     []
% 1.52/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/1.09  
% 1.52/1.09  ------ Combination Options
% 1.52/1.09  
% 1.52/1.09  --comb_res_mult                         3
% 1.52/1.09  --comb_sup_mult                         2
% 1.52/1.09  --comb_inst_mult                        10
% 1.52/1.09  
% 1.52/1.09  ------ Debug Options
% 1.52/1.09  
% 1.52/1.09  --dbg_backtrace                         false
% 1.52/1.09  --dbg_dump_prop_clauses                 false
% 1.52/1.09  --dbg_dump_prop_clauses_file            -
% 1.52/1.09  --dbg_out_stat                          false
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  ------ Proving...
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  % SZS status Theorem for theBenchmark.p
% 1.52/1.09  
% 1.52/1.09   Resolution empty clause
% 1.52/1.09  
% 1.52/1.09  % SZS output start CNFRefutation for theBenchmark.p
% 1.52/1.09  
% 1.52/1.09  fof(f10,conjecture,(
% 1.52/1.09    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f11,negated_conjecture,(
% 1.52/1.09    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.52/1.09    inference(negated_conjecture,[],[f10])).
% 1.52/1.09  
% 1.52/1.09  fof(f20,plain,(
% 1.52/1.09    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.52/1.09    inference(ennf_transformation,[],[f11])).
% 1.52/1.09  
% 1.52/1.09  fof(f22,plain,(
% 1.52/1.09    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 1.52/1.09    introduced(choice_axiom,[])).
% 1.52/1.09  
% 1.52/1.09  fof(f23,plain,(
% 1.52/1.09    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.52/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f22])).
% 1.52/1.09  
% 1.52/1.09  fof(f34,plain,(
% 1.52/1.09    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.52/1.09    inference(cnf_transformation,[],[f23])).
% 1.52/1.09  
% 1.52/1.09  fof(f8,axiom,(
% 1.52/1.09    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f17,plain,(
% 1.52/1.09    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/1.09    inference(ennf_transformation,[],[f8])).
% 1.52/1.09  
% 1.52/1.09  fof(f32,plain,(
% 1.52/1.09    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/1.09    inference(cnf_transformation,[],[f17])).
% 1.52/1.09  
% 1.52/1.09  fof(f6,axiom,(
% 1.52/1.09    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f15,plain,(
% 1.52/1.09    ! [X0,X1,X2,X3] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/1.09    inference(ennf_transformation,[],[f6])).
% 1.52/1.09  
% 1.52/1.09  fof(f30,plain,(
% 1.52/1.09    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/1.09    inference(cnf_transformation,[],[f15])).
% 1.52/1.09  
% 1.52/1.09  fof(f1,axiom,(
% 1.52/1.09    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f21,plain,(
% 1.52/1.09    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.52/1.09    inference(nnf_transformation,[],[f1])).
% 1.52/1.09  
% 1.52/1.09  fof(f24,plain,(
% 1.52/1.09    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.52/1.09    inference(cnf_transformation,[],[f21])).
% 1.52/1.09  
% 1.52/1.09  fof(f2,axiom,(
% 1.52/1.09    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f12,plain,(
% 1.52/1.09    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.52/1.09    inference(ennf_transformation,[],[f2])).
% 1.52/1.09  
% 1.52/1.09  fof(f26,plain,(
% 1.52/1.09    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/1.09    inference(cnf_transformation,[],[f12])).
% 1.52/1.09  
% 1.52/1.09  fof(f25,plain,(
% 1.52/1.09    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.52/1.09    inference(cnf_transformation,[],[f21])).
% 1.52/1.09  
% 1.52/1.09  fof(f3,axiom,(
% 1.52/1.09    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f27,plain,(
% 1.52/1.09    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.52/1.09    inference(cnf_transformation,[],[f3])).
% 1.52/1.09  
% 1.52/1.09  fof(f4,axiom,(
% 1.52/1.09    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f13,plain,(
% 1.52/1.09    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.52/1.09    inference(ennf_transformation,[],[f4])).
% 1.52/1.09  
% 1.52/1.09  fof(f28,plain,(
% 1.52/1.09    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.52/1.09    inference(cnf_transformation,[],[f13])).
% 1.52/1.09  
% 1.52/1.09  fof(f5,axiom,(
% 1.52/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f14,plain,(
% 1.52/1.09    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/1.09    inference(ennf_transformation,[],[f5])).
% 1.52/1.09  
% 1.52/1.09  fof(f29,plain,(
% 1.52/1.09    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/1.09    inference(cnf_transformation,[],[f14])).
% 1.52/1.09  
% 1.52/1.09  fof(f7,axiom,(
% 1.52/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f16,plain,(
% 1.52/1.09    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/1.09    inference(ennf_transformation,[],[f7])).
% 1.52/1.09  
% 1.52/1.09  fof(f31,plain,(
% 1.52/1.09    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/1.09    inference(cnf_transformation,[],[f16])).
% 1.52/1.09  
% 1.52/1.09  fof(f9,axiom,(
% 1.52/1.09    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.52/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.09  
% 1.52/1.09  fof(f18,plain,(
% 1.52/1.09    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.52/1.09    inference(ennf_transformation,[],[f9])).
% 1.52/1.09  
% 1.52/1.09  fof(f19,plain,(
% 1.52/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.52/1.09    inference(flattening,[],[f18])).
% 1.52/1.09  
% 1.52/1.09  fof(f33,plain,(
% 1.52/1.09    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.52/1.09    inference(cnf_transformation,[],[f19])).
% 1.52/1.09  
% 1.52/1.09  fof(f35,plain,(
% 1.52/1.09    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.52/1.09    inference(cnf_transformation,[],[f23])).
% 1.52/1.09  
% 1.52/1.09  cnf(c_11,negated_conjecture,
% 1.52/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 1.52/1.09      inference(cnf_transformation,[],[f34]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_170,negated_conjecture,
% 1.52/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_11]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_526,plain,
% 1.52/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_8,plain,
% 1.52/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.52/1.09      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.52/1.09      inference(cnf_transformation,[],[f32]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_173,plain,
% 1.52/1.09      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
% 1.52/1.09      | k5_relset_1(X1_42,X2_42,X0_42,X3_42) = k7_relat_1(X0_42,X3_42) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_8]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_523,plain,
% 1.52/1.09      ( k5_relset_1(X0_42,X1_42,X2_42,X3_42) = k7_relat_1(X2_42,X3_42)
% 1.52/1.09      | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_173]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1032,plain,
% 1.52/1.09      ( k5_relset_1(sK0,sK2,sK3,X0_42) = k7_relat_1(sK3,X0_42) ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_526,c_523]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_6,plain,
% 1.52/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.52/1.09      | m1_subset_1(k5_relset_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.52/1.09      inference(cnf_transformation,[],[f30]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_175,plain,
% 1.52/1.09      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
% 1.52/1.09      | m1_subset_1(k5_relset_1(X1_42,X2_42,X0_42,X3_42),k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_6]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_521,plain,
% 1.52/1.09      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) != iProver_top
% 1.52/1.09      | m1_subset_1(k5_relset_1(X1_42,X2_42,X0_42,X3_42),k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) = iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_175]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1267,plain,
% 1.52/1.09      ( m1_subset_1(k7_relat_1(sK3,X0_42),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 1.52/1.09      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_1032,c_521]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_12,plain,
% 1.52/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1384,plain,
% 1.52/1.09      ( m1_subset_1(k7_relat_1(sK3,X0_42),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 1.52/1.09      inference(global_propositional_subsumption,[status(thm)],[c_1267,c_12]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1,plain,
% 1.52/1.09      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.52/1.09      inference(cnf_transformation,[],[f24]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_179,plain,
% 1.52/1.09      ( r1_tarski(X0_42,X1_42) | ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_1]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_517,plain,
% 1.52/1.09      ( r1_tarski(X0_42,X1_42) = iProver_top
% 1.52/1.09      | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_179]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1391,plain,
% 1.52/1.09      ( r1_tarski(k7_relat_1(sK3,X0_42),k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_1384,c_517]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_2,plain,
% 1.52/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 1.52/1.09      inference(cnf_transformation,[],[f26]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_0,plain,
% 1.52/1.09      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.52/1.09      inference(cnf_transformation,[],[f25]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_99,plain,
% 1.52/1.09      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.52/1.09      inference(prop_impl,[status(thm)],[c_0]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_122,plain,
% 1.52/1.09      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 1.52/1.09      inference(bin_hyper_res,[status(thm)],[c_2,c_99]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_169,plain,
% 1.52/1.09      ( ~ r1_tarski(X0_42,X1_42) | ~ v1_relat_1(X1_42) | v1_relat_1(X0_42) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_122]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_527,plain,
% 1.52/1.09      ( r1_tarski(X0_42,X1_42) != iProver_top
% 1.52/1.09      | v1_relat_1(X1_42) != iProver_top
% 1.52/1.09      | v1_relat_1(X0_42) = iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_2471,plain,
% 1.52/1.09      ( v1_relat_1(k7_relat_1(sK3,X0_42)) = iProver_top
% 1.52/1.09      | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_1391,c_527]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_3,plain,
% 1.52/1.09      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.52/1.09      inference(cnf_transformation,[],[f27]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_178,plain,
% 1.52/1.09      ( v1_relat_1(k2_zfmisc_1(X0_42,X1_42)) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_3]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1100,plain,
% 1.52/1.09      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 1.52/1.09      inference(instantiation,[status(thm)],[c_178]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1101,plain,
% 1.52/1.09      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_1100]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_2996,plain,
% 1.52/1.09      ( v1_relat_1(k7_relat_1(sK3,X0_42)) = iProver_top ),
% 1.52/1.09      inference(global_propositional_subsumption,[status(thm)],[c_2471,c_1101]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_4,plain,
% 1.52/1.09      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 1.52/1.09      inference(cnf_transformation,[],[f28]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_177,plain,
% 1.52/1.09      ( r1_tarski(k1_relat_1(k7_relat_1(X0_42,X1_42)),X1_42)
% 1.52/1.09      | ~ v1_relat_1(X0_42) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_4]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_519,plain,
% 1.52/1.09      ( r1_tarski(k1_relat_1(k7_relat_1(X0_42,X1_42)),X1_42) = iProver_top
% 1.52/1.09      | v1_relat_1(X0_42) != iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_177]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_5,plain,
% 1.52/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.52/1.09      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 1.52/1.09      inference(cnf_transformation,[],[f29]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_176,plain,
% 1.52/1.09      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
% 1.52/1.09      | m1_subset_1(k2_relset_1(X1_42,X2_42,X0_42),k1_zfmisc_1(X2_42)) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_5]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_520,plain,
% 1.52/1.09      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) != iProver_top
% 1.52/1.09      | m1_subset_1(k2_relset_1(X1_42,X2_42,X0_42),k1_zfmisc_1(X2_42)) = iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_176]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_918,plain,
% 1.52/1.09      ( r1_tarski(k2_relset_1(X0_42,X1_42,X2_42),X1_42) = iProver_top
% 1.52/1.09      | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_520,c_517]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1520,plain,
% 1.52/1.09      ( r1_tarski(k2_relset_1(sK0,sK2,k7_relat_1(sK3,X0_42)),sK2) = iProver_top ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_1384,c_918]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_7,plain,
% 1.52/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.52/1.09      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.52/1.09      inference(cnf_transformation,[],[f31]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_174,plain,
% 1.52/1.09      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
% 1.52/1.09      | k2_relset_1(X1_42,X2_42,X0_42) = k2_relat_1(X0_42) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_7]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_522,plain,
% 1.52/1.09      ( k2_relset_1(X0_42,X1_42,X2_42) = k2_relat_1(X2_42)
% 1.52/1.09      | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1393,plain,
% 1.52/1.09      ( k2_relset_1(sK0,sK2,k7_relat_1(sK3,X0_42)) = k2_relat_1(k7_relat_1(sK3,X0_42)) ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_1384,c_522]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1790,plain,
% 1.52/1.09      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_42)),sK2) = iProver_top ),
% 1.52/1.09      inference(light_normalisation,[status(thm)],[c_1520,c_1393]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_9,plain,
% 1.52/1.09      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.52/1.09      | ~ r1_tarski(k1_relat_1(X0),X2)
% 1.52/1.09      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.52/1.09      | ~ v1_relat_1(X0) ),
% 1.52/1.09      inference(cnf_transformation,[],[f33]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_172,plain,
% 1.52/1.09      ( ~ r1_tarski(k2_relat_1(X0_42),X1_42)
% 1.52/1.09      | ~ r1_tarski(k1_relat_1(X0_42),X2_42)
% 1.52/1.09      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X1_42)))
% 1.52/1.09      | ~ v1_relat_1(X0_42) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_9]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_524,plain,
% 1.52/1.09      ( r1_tarski(k2_relat_1(X0_42),X1_42) != iProver_top
% 1.52/1.09      | r1_tarski(k1_relat_1(X0_42),X2_42) != iProver_top
% 1.52/1.09      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X1_42))) = iProver_top
% 1.52/1.09      | v1_relat_1(X0_42) != iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_172]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_10,negated_conjecture,
% 1.52/1.09      ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.52/1.09      inference(cnf_transformation,[],[f35]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_171,negated_conjecture,
% 1.52/1.09      ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.52/1.09      inference(subtyping,[status(esa)],[c_10]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_525,plain,
% 1.52/1.09      ( m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1260,plain,
% 1.52/1.09      ( m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 1.52/1.09      inference(demodulation,[status(thm)],[c_1032,c_525]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1273,plain,
% 1.52/1.09      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) != iProver_top
% 1.52/1.09      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top
% 1.52/1.09      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_524,c_1260]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1795,plain,
% 1.52/1.09      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top
% 1.52/1.09      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_1790,c_1273]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1955,plain,
% 1.52/1.09      ( v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top
% 1.52/1.09      | v1_relat_1(sK3) != iProver_top ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_519,c_1795]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_603,plain,
% 1.52/1.09      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
% 1.52/1.09      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 1.52/1.09      inference(instantiation,[status(thm)],[c_179]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_604,plain,
% 1.52/1.09      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) = iProver_top
% 1.52/1.09      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_636,plain,
% 1.52/1.09      ( ~ r1_tarski(X0_42,k2_zfmisc_1(X1_42,X2_42))
% 1.52/1.09      | v1_relat_1(X0_42)
% 1.52/1.09      | ~ v1_relat_1(k2_zfmisc_1(X1_42,X2_42)) ),
% 1.52/1.09      inference(instantiation,[status(thm)],[c_169]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_845,plain,
% 1.52/1.09      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
% 1.52/1.09      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
% 1.52/1.09      | v1_relat_1(sK3) ),
% 1.52/1.09      inference(instantiation,[status(thm)],[c_636]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_846,plain,
% 1.52/1.09      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) != iProver_top
% 1.52/1.09      | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 1.52/1.09      | v1_relat_1(sK3) = iProver_top ),
% 1.52/1.09      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_1958,plain,
% 1.52/1.09      ( v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
% 1.52/1.09      inference(global_propositional_subsumption,
% 1.52/1.09                [status(thm)],
% 1.52/1.09                [c_1955,c_12,c_604,c_846,c_1101]) ).
% 1.52/1.09  
% 1.52/1.09  cnf(c_3003,plain,
% 1.52/1.09      ( $false ),
% 1.52/1.09      inference(superposition,[status(thm)],[c_2996,c_1958]) ).
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  % SZS output end CNFRefutation for theBenchmark.p
% 1.52/1.09  
% 1.52/1.09  ------                               Statistics
% 1.52/1.09  
% 1.52/1.09  ------ General
% 1.52/1.09  
% 1.52/1.09  abstr_ref_over_cycles:                  0
% 1.52/1.09  abstr_ref_under_cycles:                 0
% 1.52/1.09  gc_basic_clause_elim:                   0
% 1.52/1.09  forced_gc_time:                         0
% 1.52/1.09  parsing_time:                           0.01
% 1.52/1.09  unif_index_cands_time:                  0.
% 1.52/1.09  unif_index_add_time:                    0.
% 1.52/1.09  orderings_time:                         0.
% 1.52/1.09  out_proof_time:                         0.022
% 1.52/1.09  total_time:                             0.274
% 1.52/1.09  num_of_symbols:                         47
% 1.52/1.09  num_of_terms:                           4259
% 1.52/1.09  
% 1.52/1.09  ------ Preprocessing
% 1.52/1.09  
% 1.52/1.09  num_of_splits:                          0
% 1.52/1.09  num_of_split_atoms:                     0
% 1.52/1.09  num_of_reused_defs:                     0
% 1.52/1.09  num_eq_ax_congr_red:                    14
% 1.52/1.09  num_of_sem_filtered_clauses:            1
% 1.52/1.09  num_of_subtypes:                        2
% 1.52/1.09  monotx_restored_types:                  0
% 1.52/1.09  sat_num_of_epr_types:                   0
% 1.52/1.09  sat_num_of_non_cyclic_types:            0
% 1.52/1.09  sat_guarded_non_collapsed_types:        0
% 1.52/1.09  num_pure_diseq_elim:                    0
% 1.52/1.09  simp_replaced_by:                       0
% 1.52/1.09  res_preprocessed:                       57
% 1.52/1.09  prep_upred:                             0
% 1.52/1.09  prep_unflattend:                        0
% 1.52/1.09  smt_new_axioms:                         0
% 1.52/1.09  pred_elim_cands:                        3
% 1.52/1.09  pred_elim:                              0
% 1.52/1.09  pred_elim_cl:                           0
% 1.52/1.09  pred_elim_cycles:                       1
% 1.52/1.09  merged_defs:                            6
% 1.52/1.09  merged_defs_ncl:                        0
% 1.52/1.09  bin_hyper_res:                          7
% 1.52/1.09  prep_cycles:                            3
% 1.52/1.09  pred_elim_time:                         0.
% 1.52/1.09  splitting_time:                         0.
% 1.52/1.09  sem_filter_time:                        0.
% 1.52/1.09  monotx_time:                            0.
% 1.52/1.09  subtype_inf_time:                       0.
% 1.52/1.09  
% 1.52/1.09  ------ Problem properties
% 1.52/1.09  
% 1.52/1.09  clauses:                                12
% 1.52/1.09  conjectures:                            2
% 1.52/1.09  epr:                                    1
% 1.52/1.09  horn:                                   12
% 1.52/1.09  ground:                                 2
% 1.52/1.09  unary:                                  3
% 1.52/1.09  binary:                                 7
% 1.52/1.09  lits:                                   24
% 1.52/1.09  lits_eq:                                2
% 1.52/1.09  fd_pure:                                0
% 1.52/1.09  fd_pseudo:                              0
% 1.52/1.09  fd_cond:                                0
% 1.52/1.09  fd_pseudo_cond:                         0
% 1.52/1.09  ac_symbols:                             0
% 1.52/1.09  
% 1.52/1.09  ------ Propositional Solver
% 1.52/1.09  
% 1.52/1.09  prop_solver_calls:                      23
% 1.52/1.09  prop_fast_solver_calls:                 334
% 1.52/1.09  smt_solver_calls:                       0
% 1.52/1.09  smt_fast_solver_calls:                  0
% 1.52/1.09  prop_num_of_clauses:                    1532
% 1.52/1.09  prop_preprocess_simplified:             3264
% 1.52/1.09  prop_fo_subsumed:                       7
% 1.52/1.09  prop_solver_time:                       0.
% 1.52/1.09  smt_solver_time:                        0.
% 1.52/1.09  smt_fast_solver_time:                   0.
% 1.52/1.09  prop_fast_solver_time:                  0.
% 1.52/1.09  prop_unsat_core_time:                   0.
% 1.52/1.09  
% 1.52/1.09  ------ QBF
% 1.52/1.09  
% 1.52/1.09  qbf_q_res:                              0
% 1.52/1.09  qbf_num_tautologies:                    0
% 1.52/1.09  qbf_prep_cycles:                        0
% 1.52/1.09  
% 1.52/1.09  ------ BMC1
% 1.52/1.09  
% 1.52/1.09  bmc1_current_bound:                     -1
% 1.52/1.09  bmc1_last_solved_bound:                 -1
% 1.52/1.09  bmc1_unsat_core_size:                   -1
% 1.52/1.09  bmc1_unsat_core_parents_size:           -1
% 1.52/1.09  bmc1_merge_next_fun:                    0
% 1.52/1.09  bmc1_unsat_core_clauses_time:           0.
% 1.52/1.09  
% 1.52/1.09  ------ Instantiation
% 1.52/1.09  
% 1.52/1.09  inst_num_of_clauses:                    399
% 1.52/1.09  inst_num_in_passive:                    8
% 1.52/1.09  inst_num_in_active:                     199
% 1.52/1.09  inst_num_in_unprocessed:                193
% 1.52/1.09  inst_num_of_loops:                      210
% 1.52/1.09  inst_num_of_learning_restarts:          0
% 1.52/1.09  inst_num_moves_active_passive:          8
% 1.52/1.09  inst_lit_activity:                      0
% 1.52/1.09  inst_lit_activity_moves:                0
% 1.52/1.09  inst_num_tautologies:                   0
% 1.52/1.09  inst_num_prop_implied:                  0
% 1.52/1.09  inst_num_existing_simplified:           0
% 1.52/1.09  inst_num_eq_res_simplified:             0
% 1.52/1.09  inst_num_child_elim:                    0
% 1.52/1.09  inst_num_of_dismatching_blockings:      39
% 1.52/1.09  inst_num_of_non_proper_insts:           267
% 1.52/1.09  inst_num_of_duplicates:                 0
% 1.52/1.09  inst_inst_num_from_inst_to_res:         0
% 1.52/1.09  inst_dismatching_checking_time:         0.
% 1.52/1.09  
% 1.52/1.09  ------ Resolution
% 1.52/1.09  
% 1.52/1.09  res_num_of_clauses:                     0
% 1.52/1.09  res_num_in_passive:                     0
% 1.52/1.09  res_num_in_active:                      0
% 1.52/1.09  res_num_of_loops:                       60
% 1.52/1.09  res_forward_subset_subsumed:            20
% 1.52/1.09  res_backward_subset_subsumed:           2
% 1.52/1.09  res_forward_subsumed:                   0
% 1.52/1.09  res_backward_subsumed:                  0
% 1.52/1.09  res_forward_subsumption_resolution:     0
% 1.52/1.09  res_backward_subsumption_resolution:    0
% 1.52/1.09  res_clause_to_clause_subsumption:       108
% 1.52/1.09  res_orphan_elimination:                 0
% 1.52/1.09  res_tautology_del:                      63
% 1.52/1.09  res_num_eq_res_simplified:              0
% 1.52/1.09  res_num_sel_changes:                    0
% 1.52/1.09  res_moves_from_active_to_pass:          0
% 1.52/1.09  
% 1.52/1.09  ------ Superposition
% 1.52/1.09  
% 1.52/1.09  sup_time_total:                         0.
% 1.52/1.09  sup_time_generating:                    0.
% 1.52/1.09  sup_time_sim_full:                      0.
% 1.52/1.09  sup_time_sim_immed:                     0.
% 1.52/1.09  
% 1.52/1.09  sup_num_of_clauses:                     64
% 1.52/1.09  sup_num_in_active:                      39
% 1.52/1.09  sup_num_in_passive:                     25
% 1.52/1.09  sup_num_of_loops:                       40
% 1.52/1.09  sup_fw_superposition:                   39
% 1.52/1.09  sup_bw_superposition:                   27
% 1.52/1.09  sup_immediate_simplified:               5
% 1.52/1.09  sup_given_eliminated:                   0
% 1.52/1.09  comparisons_done:                       0
% 1.52/1.09  comparisons_avoided:                    0
% 1.52/1.09  
% 1.52/1.09  ------ Simplifications
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  sim_fw_subset_subsumed:                 3
% 1.52/1.09  sim_bw_subset_subsumed:                 0
% 1.52/1.09  sim_fw_subsumed:                        0
% 1.52/1.09  sim_bw_subsumed:                        0
% 1.52/1.09  sim_fw_subsumption_res:                 0
% 1.52/1.09  sim_bw_subsumption_res:                 0
% 1.52/1.09  sim_tautology_del:                      1
% 1.52/1.09  sim_eq_tautology_del:                   0
% 1.52/1.09  sim_eq_res_simp:                        0
% 1.52/1.09  sim_fw_demodulated:                     1
% 1.52/1.09  sim_bw_demodulated:                     2
% 1.52/1.09  sim_light_normalised:                   3
% 1.52/1.09  sim_joinable_taut:                      0
% 1.52/1.09  sim_joinable_simp:                      0
% 1.52/1.09  sim_ac_normalised:                      0
% 1.52/1.09  sim_smt_subsumption:                    0
% 1.52/1.09  
%------------------------------------------------------------------------------
