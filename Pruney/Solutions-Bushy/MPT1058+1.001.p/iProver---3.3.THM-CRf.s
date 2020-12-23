%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1058+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:48 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 105 expanded)
%              Number of clauses        :   43 (  46 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  144 ( 231 expanded)
%              Number of equality atoms :   70 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f33,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_272,plain,
    ( v1_relat_1(k6_relat_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_448,plain,
    ( v1_relat_1(k6_relat_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_266,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_453,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X1,X0),X2) = k10_relat_1(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_269,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | k10_relat_1(k5_relat_1(X1_41,X0_41),X2_41) = k10_relat_1(X1_41,k10_relat_1(X0_41,X2_41)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_451,plain,
    ( k10_relat_1(k5_relat_1(X0_41,X1_41),X2_41) = k10_relat_1(X0_41,k10_relat_1(X1_41,X2_41))
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_753,plain,
    ( k10_relat_1(X0_41,k10_relat_1(sK0,X1_41)) = k10_relat_1(k5_relat_1(X0_41,sK0),X1_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_451])).

cnf(c_872,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X0_43),sK0),X0_41) = k10_relat_1(k6_relat_1(X0_43),k10_relat_1(sK0,X0_41)) ),
    inference(superposition,[status(thm)],[c_448,c_753])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_268,plain,
    ( ~ v1_relat_1(X0_41)
    | k5_relat_1(k6_relat_1(X0_43),X0_41) = k7_relat_1(X0_41,X0_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_452,plain,
    ( k5_relat_1(k6_relat_1(X0_43),X0_41) = k7_relat_1(X0_41,X0_43)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_585,plain,
    ( k5_relat_1(k6_relat_1(X0_43),sK0) = k7_relat_1(sK0,X0_43) ),
    inference(superposition,[status(thm)],[c_453,c_452])).

cnf(c_874,plain,
    ( k10_relat_1(k6_relat_1(X0_43),k10_relat_1(sK0,X0_41)) = k10_relat_1(k7_relat_1(sK0,X0_43),X0_41) ),
    inference(light_normalisation,[status(thm)],[c_872,c_585])).

cnf(c_0,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_273,plain,
    ( m1_subset_1(k6_relat_1(X0_43),k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_43))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_447,plain,
    ( m1_subset_1(k6_relat_1(X0_43),k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_43))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
    | k8_relset_1(X0_43,X1_43,X0_41,X1_41) = k10_relat_1(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_449,plain,
    ( k8_relset_1(X0_43,X1_43,X0_41,X1_41) = k10_relat_1(X0_41,X1_41)
    | m1_subset_1(X0_41,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_707,plain,
    ( k8_relset_1(X0_43,X0_43,k6_relat_1(X0_43),X0_41) = k10_relat_1(k6_relat_1(X0_43),X0_41) ),
    inference(superposition,[status(thm)],[c_447,c_449])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_111,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | k10_relat_1(sK0,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

cnf(c_112,plain,
    ( m1_subset_1(k10_relat_1(sK0,sK2),k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_111])).

cnf(c_265,plain,
    ( m1_subset_1(k10_relat_1(sK0,sK2),k1_zfmisc_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_112])).

cnf(c_454,plain,
    ( m1_subset_1(k10_relat_1(sK0,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_relset_1(X1,X1,k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | k8_relset_1(X0_43,X0_43,k6_relat_1(X0_43),X0_41) = X0_41 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_450,plain,
    ( k8_relset_1(X0_43,X0_43,k6_relat_1(X0_43),X0_41) = X0_41
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_712,plain,
    ( k8_relset_1(sK1,sK1,k6_relat_1(sK1),k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_454,c_450])).

cnf(c_866,plain,
    ( k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_707,c_712])).

cnf(c_1032,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_874,c_866])).

cnf(c_275,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_533,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_276,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_501,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0_41
    | k10_relat_1(sK0,sK2) != X0_41
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_532,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_7,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_267,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1032,c_533,c_532,c_267])).


%------------------------------------------------------------------------------
