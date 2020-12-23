%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:52 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 276 expanded)
%              Number of clauses        :   65 ( 142 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  222 ( 601 expanded)
%              Number of equality atoms :   70 ( 100 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_5,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_188,plain,
    ( r1_tarski(k8_relat_1(X0_42,X1_42),X1_42)
    | ~ v1_relat_1(X1_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_550,plain,
    ( r1_tarski(k8_relat_1(X0_42,X1_42),X1_42) = iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_105,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_130,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_105])).

cnf(c_180,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ v1_relat_1(X1_42)
    | v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_130])).

cnf(c_558,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1881,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k8_relat_1(X1_42,X0_42)) = iProver_top ),
    inference(superposition,[status(thm)],[c_550,c_558])).

cnf(c_4,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_189,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0_42,X1_42)),X0_42)
    | ~ v1_relat_1(X1_42) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_549,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0_42,X1_42)),X0_42) = iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_181,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_557,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_181])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_183,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ m1_subset_1(X1_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X3_42)))
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X3_42))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_555,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | m1_subset_1(X1_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X3_42))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X3_42))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_1143,plain,
    ( r1_tarski(X0_42,sK3) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_555])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | k1_relset_1(X1_42,X2_42,X0_42) = k1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_552,plain,
    ( k1_relset_1(X0_42,X1_42,X2_42) = k1_relat_1(X2_42)
    | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_1401,plain,
    ( k1_relset_1(sK2,sK0,X0_42) = k1_relat_1(X0_42)
    | r1_tarski(X0_42,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_552])).

cnf(c_1550,plain,
    ( k1_relset_1(sK2,sK0,k8_relat_1(X0_42,sK3)) = k1_relat_1(k8_relat_1(X0_42,sK3))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_550,c_1401])).

cnf(c_13,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_191,plain,
    ( r1_tarski(X0_42,X1_42)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_642,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_643,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_670,plain,
    ( ~ r1_tarski(X0_42,k2_zfmisc_1(X1_42,X2_42))
    | v1_relat_1(X0_42)
    | ~ v1_relat_1(k2_zfmisc_1(X1_42,X2_42)) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_749,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_750,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_190,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_42,X1_42)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_794,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_795,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_2470,plain,
    ( k1_relset_1(sK2,sK0,k8_relat_1(X0_42,sK3)) = k1_relat_1(k8_relat_1(X0_42,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1550,c_13,c_643,c_750,c_795])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_187,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | m1_subset_1(k1_relset_1(X1_42,X2_42,X0_42),k1_zfmisc_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_551,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_42,X2_42,X0_42),k1_zfmisc_1(X1_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_547,plain,
    ( r1_tarski(X0_42,X1_42) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_932,plain,
    ( r1_tarski(k1_relset_1(X0_42,X1_42,X2_42),X0_42) = iProver_top
    | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(superposition,[status(thm)],[c_551,c_547])).

cnf(c_2881,plain,
    ( r1_tarski(X0_42,sK3) != iProver_top
    | r1_tarski(k1_relset_1(sK2,sK0,X0_42),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_932])).

cnf(c_3273,plain,
    ( r1_tarski(k8_relat_1(X0_42,sK3),sK3) != iProver_top
    | r1_tarski(k1_relat_1(k8_relat_1(X0_42,sK3)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2470,c_2881])).

cnf(c_977,plain,
    ( r1_tarski(k8_relat_1(X0_42,sK3),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_983,plain,
    ( r1_tarski(k8_relat_1(X0_42,sK3),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_3690,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0_42,sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3273,c_13,c_643,c_750,c_795,c_983])).

cnf(c_9,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_184,plain,
    ( ~ r1_tarski(k1_relat_1(X0_42),X1_42)
    | ~ r1_tarski(k2_relat_1(X0_42),X2_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | ~ v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_554,plain,
    ( r1_tarski(k1_relat_1(X0_42),X1_42) != iProver_top
    | r1_tarski(k2_relat_1(X0_42),X2_42) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | k6_relset_1(X1_42,X2_42,X3_42,X0_42) = k8_relat_1(X3_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_553,plain,
    ( k6_relset_1(X0_42,X1_42,X2_42,X3_42) = k8_relat_1(X2_42,X3_42)
    | m1_subset_1(X3_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_1081,plain,
    ( k6_relset_1(sK2,sK0,X0_42,sK3) = k8_relat_1(X0_42,sK3) ),
    inference(superposition,[status(thm)],[c_557,c_553])).

cnf(c_11,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_182,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_556,plain,
    ( m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_182])).

cnf(c_1249,plain,
    ( m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1081,c_556])).

cnf(c_1686,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top
    | v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_1249])).

cnf(c_3699,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top
    | v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3690,c_1686])).

cnf(c_3722,plain,
    ( v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_3699])).

cnf(c_4737,plain,
    ( v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3722,c_13,c_643,c_750,c_795])).

cnf(c_4742,plain,
    ( v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1881,c_4737])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4742,c_795,c_750,c_643,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:25:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.70/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/0.98  
% 2.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/0.98  
% 2.70/0.98  ------  iProver source info
% 2.70/0.98  
% 2.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/0.98  git: non_committed_changes: false
% 2.70/0.98  git: last_make_outside_of_git: false
% 2.70/0.98  
% 2.70/0.98  ------ 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options
% 2.70/0.98  
% 2.70/0.98  --out_options                           all
% 2.70/0.98  --tptp_safe_out                         true
% 2.70/0.98  --problem_path                          ""
% 2.70/0.98  --include_path                          ""
% 2.70/0.98  --clausifier                            res/vclausify_rel
% 2.70/0.98  --clausifier_options                    --mode clausify
% 2.70/0.98  --stdin                                 false
% 2.70/0.98  --stats_out                             all
% 2.70/0.98  
% 2.70/0.98  ------ General Options
% 2.70/0.98  
% 2.70/0.98  --fof                                   false
% 2.70/0.98  --time_out_real                         305.
% 2.70/0.98  --time_out_virtual                      -1.
% 2.70/0.98  --symbol_type_check                     false
% 2.70/0.98  --clausify_out                          false
% 2.70/0.98  --sig_cnt_out                           false
% 2.70/0.98  --trig_cnt_out                          false
% 2.70/0.98  --trig_cnt_out_tolerance                1.
% 2.70/0.98  --trig_cnt_out_sk_spl                   false
% 2.70/0.98  --abstr_cl_out                          false
% 2.70/0.98  
% 2.70/0.98  ------ Global Options
% 2.70/0.98  
% 2.70/0.98  --schedule                              default
% 2.70/0.98  --add_important_lit                     false
% 2.70/0.98  --prop_solver_per_cl                    1000
% 2.70/0.98  --min_unsat_core                        false
% 2.70/0.98  --soft_assumptions                      false
% 2.70/0.98  --soft_lemma_size                       3
% 2.70/0.98  --prop_impl_unit_size                   0
% 2.70/0.98  --prop_impl_unit                        []
% 2.70/0.98  --share_sel_clauses                     true
% 2.70/0.98  --reset_solvers                         false
% 2.70/0.98  --bc_imp_inh                            [conj_cone]
% 2.70/0.98  --conj_cone_tolerance                   3.
% 2.70/0.98  --extra_neg_conj                        none
% 2.70/0.98  --large_theory_mode                     true
% 2.70/0.98  --prolific_symb_bound                   200
% 2.70/0.98  --lt_threshold                          2000
% 2.70/0.98  --clause_weak_htbl                      true
% 2.70/0.98  --gc_record_bc_elim                     false
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing Options
% 2.70/0.98  
% 2.70/0.98  --preprocessing_flag                    true
% 2.70/0.98  --time_out_prep_mult                    0.1
% 2.70/0.98  --splitting_mode                        input
% 2.70/0.98  --splitting_grd                         true
% 2.70/0.98  --splitting_cvd                         false
% 2.70/0.98  --splitting_cvd_svl                     false
% 2.70/0.98  --splitting_nvd                         32
% 2.70/0.98  --sub_typing                            true
% 2.70/0.98  --prep_gs_sim                           true
% 2.70/0.98  --prep_unflatten                        true
% 2.70/0.98  --prep_res_sim                          true
% 2.70/0.98  --prep_upred                            true
% 2.70/0.98  --prep_sem_filter                       exhaustive
% 2.70/0.98  --prep_sem_filter_out                   false
% 2.70/0.98  --pred_elim                             true
% 2.70/0.98  --res_sim_input                         true
% 2.70/0.98  --eq_ax_congr_red                       true
% 2.70/0.98  --pure_diseq_elim                       true
% 2.70/0.98  --brand_transform                       false
% 2.70/0.98  --non_eq_to_eq                          false
% 2.70/0.98  --prep_def_merge                        true
% 2.70/0.98  --prep_def_merge_prop_impl              false
% 2.70/0.98  --prep_def_merge_mbd                    true
% 2.70/0.98  --prep_def_merge_tr_red                 false
% 2.70/0.98  --prep_def_merge_tr_cl                  false
% 2.70/0.98  --smt_preprocessing                     true
% 2.70/0.98  --smt_ac_axioms                         fast
% 2.70/0.98  --preprocessed_out                      false
% 2.70/0.98  --preprocessed_stats                    false
% 2.70/0.98  
% 2.70/0.98  ------ Abstraction refinement Options
% 2.70/0.98  
% 2.70/0.98  --abstr_ref                             []
% 2.70/0.98  --abstr_ref_prep                        false
% 2.70/0.98  --abstr_ref_until_sat                   false
% 2.70/0.98  --abstr_ref_sig_restrict                funpre
% 2.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.98  --abstr_ref_under                       []
% 2.70/0.98  
% 2.70/0.98  ------ SAT Options
% 2.70/0.98  
% 2.70/0.98  --sat_mode                              false
% 2.70/0.98  --sat_fm_restart_options                ""
% 2.70/0.98  --sat_gr_def                            false
% 2.70/0.98  --sat_epr_types                         true
% 2.70/0.98  --sat_non_cyclic_types                  false
% 2.70/0.98  --sat_finite_models                     false
% 2.70/0.98  --sat_fm_lemmas                         false
% 2.70/0.98  --sat_fm_prep                           false
% 2.70/0.98  --sat_fm_uc_incr                        true
% 2.70/0.98  --sat_out_model                         small
% 2.70/0.98  --sat_out_clauses                       false
% 2.70/0.98  
% 2.70/0.98  ------ QBF Options
% 2.70/0.98  
% 2.70/0.98  --qbf_mode                              false
% 2.70/0.98  --qbf_elim_univ                         false
% 2.70/0.98  --qbf_dom_inst                          none
% 2.70/0.98  --qbf_dom_pre_inst                      false
% 2.70/0.98  --qbf_sk_in                             false
% 2.70/0.98  --qbf_pred_elim                         true
% 2.70/0.98  --qbf_split                             512
% 2.70/0.98  
% 2.70/0.98  ------ BMC1 Options
% 2.70/0.98  
% 2.70/0.98  --bmc1_incremental                      false
% 2.70/0.98  --bmc1_axioms                           reachable_all
% 2.70/0.98  --bmc1_min_bound                        0
% 2.70/0.98  --bmc1_max_bound                        -1
% 2.70/0.98  --bmc1_max_bound_default                -1
% 2.70/0.98  --bmc1_symbol_reachability              true
% 2.70/0.98  --bmc1_property_lemmas                  false
% 2.70/0.98  --bmc1_k_induction                      false
% 2.70/0.98  --bmc1_non_equiv_states                 false
% 2.70/0.98  --bmc1_deadlock                         false
% 2.70/0.98  --bmc1_ucm                              false
% 2.70/0.98  --bmc1_add_unsat_core                   none
% 2.70/0.98  --bmc1_unsat_core_children              false
% 2.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.98  --bmc1_out_stat                         full
% 2.70/0.98  --bmc1_ground_init                      false
% 2.70/0.98  --bmc1_pre_inst_next_state              false
% 2.70/0.98  --bmc1_pre_inst_state                   false
% 2.70/0.98  --bmc1_pre_inst_reach_state             false
% 2.70/0.98  --bmc1_out_unsat_core                   false
% 2.70/0.98  --bmc1_aig_witness_out                  false
% 2.70/0.98  --bmc1_verbose                          false
% 2.70/0.98  --bmc1_dump_clauses_tptp                false
% 2.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.98  --bmc1_dump_file                        -
% 2.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.98  --bmc1_ucm_extend_mode                  1
% 2.70/0.98  --bmc1_ucm_init_mode                    2
% 2.70/0.98  --bmc1_ucm_cone_mode                    none
% 2.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.98  --bmc1_ucm_relax_model                  4
% 2.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.98  --bmc1_ucm_layered_model                none
% 2.70/0.98  --bmc1_ucm_max_lemma_size               10
% 2.70/0.98  
% 2.70/0.98  ------ AIG Options
% 2.70/0.98  
% 2.70/0.98  --aig_mode                              false
% 2.70/0.98  
% 2.70/0.98  ------ Instantiation Options
% 2.70/0.98  
% 2.70/0.98  --instantiation_flag                    true
% 2.70/0.98  --inst_sos_flag                         false
% 2.70/0.98  --inst_sos_phase                        true
% 2.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel_side                     num_symb
% 2.70/0.98  --inst_solver_per_active                1400
% 2.70/0.98  --inst_solver_calls_frac                1.
% 2.70/0.98  --inst_passive_queue_type               priority_queues
% 2.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.98  --inst_passive_queues_freq              [25;2]
% 2.70/0.98  --inst_dismatching                      true
% 2.70/0.98  --inst_eager_unprocessed_to_passive     true
% 2.70/0.98  --inst_prop_sim_given                   true
% 2.70/0.98  --inst_prop_sim_new                     false
% 2.70/0.98  --inst_subs_new                         false
% 2.70/0.98  --inst_eq_res_simp                      false
% 2.70/0.98  --inst_subs_given                       false
% 2.70/0.98  --inst_orphan_elimination               true
% 2.70/0.98  --inst_learning_loop_flag               true
% 2.70/0.98  --inst_learning_start                   3000
% 2.70/0.98  --inst_learning_factor                  2
% 2.70/0.98  --inst_start_prop_sim_after_learn       3
% 2.70/0.98  --inst_sel_renew                        solver
% 2.70/0.98  --inst_lit_activity_flag                true
% 2.70/0.98  --inst_restr_to_given                   false
% 2.70/0.98  --inst_activity_threshold               500
% 2.70/0.98  --inst_out_proof                        true
% 2.70/0.98  
% 2.70/0.98  ------ Resolution Options
% 2.70/0.98  
% 2.70/0.98  --resolution_flag                       true
% 2.70/0.98  --res_lit_sel                           adaptive
% 2.70/0.98  --res_lit_sel_side                      none
% 2.70/0.98  --res_ordering                          kbo
% 2.70/0.98  --res_to_prop_solver                    active
% 2.70/0.98  --res_prop_simpl_new                    false
% 2.70/0.98  --res_prop_simpl_given                  true
% 2.70/0.98  --res_passive_queue_type                priority_queues
% 2.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.98  --res_passive_queues_freq               [15;5]
% 2.70/0.98  --res_forward_subs                      full
% 2.70/0.98  --res_backward_subs                     full
% 2.70/0.98  --res_forward_subs_resolution           true
% 2.70/0.98  --res_backward_subs_resolution          true
% 2.70/0.98  --res_orphan_elimination                true
% 2.70/0.98  --res_time_limit                        2.
% 2.70/0.98  --res_out_proof                         true
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Options
% 2.70/0.98  
% 2.70/0.98  --superposition_flag                    true
% 2.70/0.98  --sup_passive_queue_type                priority_queues
% 2.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.98  --demod_completeness_check              fast
% 2.70/0.98  --demod_use_ground                      true
% 2.70/0.98  --sup_to_prop_solver                    passive
% 2.70/0.98  --sup_prop_simpl_new                    true
% 2.70/0.98  --sup_prop_simpl_given                  true
% 2.70/0.98  --sup_fun_splitting                     false
% 2.70/0.98  --sup_smt_interval                      50000
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Simplification Setup
% 2.70/0.98  
% 2.70/0.98  --sup_indices_passive                   []
% 2.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_full_bw                           [BwDemod]
% 2.70/0.98  --sup_immed_triv                        [TrivRules]
% 2.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_immed_bw_main                     []
% 2.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  
% 2.70/0.98  ------ Combination Options
% 2.70/0.98  
% 2.70/0.98  --comb_res_mult                         3
% 2.70/0.98  --comb_sup_mult                         2
% 2.70/0.98  --comb_inst_mult                        10
% 2.70/0.98  
% 2.70/0.98  ------ Debug Options
% 2.70/0.98  
% 2.70/0.98  --dbg_backtrace                         false
% 2.70/0.98  --dbg_dump_prop_clauses                 false
% 2.70/0.98  --dbg_dump_prop_clauses_file            -
% 2.70/0.98  --dbg_out_stat                          false
% 2.70/0.98  ------ Parsing...
% 2.70/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/0.98  ------ Proving...
% 2.70/0.98  ------ Problem Properties 
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  clauses                                 13
% 2.70/0.98  conjectures                             2
% 2.70/0.98  EPR                                     1
% 2.70/0.98  Horn                                    13
% 2.70/0.98  unary                                   3
% 2.70/0.98  binary                                  7
% 2.70/0.98  lits                                    27
% 2.70/0.98  lits eq                                 2
% 2.70/0.98  fd_pure                                 0
% 2.70/0.98  fd_pseudo                               0
% 2.70/0.98  fd_cond                                 0
% 2.70/0.98  fd_pseudo_cond                          0
% 2.70/0.98  AC symbols                              0
% 2.70/0.98  
% 2.70/0.98  ------ Schedule dynamic 5 is on 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  ------ 
% 2.70/0.98  Current options:
% 2.70/0.98  ------ 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options
% 2.70/0.98  
% 2.70/0.98  --out_options                           all
% 2.70/0.98  --tptp_safe_out                         true
% 2.70/0.98  --problem_path                          ""
% 2.70/0.98  --include_path                          ""
% 2.70/0.98  --clausifier                            res/vclausify_rel
% 2.70/0.98  --clausifier_options                    --mode clausify
% 2.70/0.98  --stdin                                 false
% 2.70/0.98  --stats_out                             all
% 2.70/0.98  
% 2.70/0.98  ------ General Options
% 2.70/0.98  
% 2.70/0.98  --fof                                   false
% 2.70/0.98  --time_out_real                         305.
% 2.70/0.98  --time_out_virtual                      -1.
% 2.70/0.98  --symbol_type_check                     false
% 2.70/0.98  --clausify_out                          false
% 2.70/0.98  --sig_cnt_out                           false
% 2.70/0.98  --trig_cnt_out                          false
% 2.70/0.98  --trig_cnt_out_tolerance                1.
% 2.70/0.98  --trig_cnt_out_sk_spl                   false
% 2.70/0.98  --abstr_cl_out                          false
% 2.70/0.98  
% 2.70/0.98  ------ Global Options
% 2.70/0.98  
% 2.70/0.98  --schedule                              default
% 2.70/0.98  --add_important_lit                     false
% 2.70/0.98  --prop_solver_per_cl                    1000
% 2.70/0.98  --min_unsat_core                        false
% 2.70/0.98  --soft_assumptions                      false
% 2.70/0.98  --soft_lemma_size                       3
% 2.70/0.98  --prop_impl_unit_size                   0
% 2.70/0.98  --prop_impl_unit                        []
% 2.70/0.98  --share_sel_clauses                     true
% 2.70/0.98  --reset_solvers                         false
% 2.70/0.98  --bc_imp_inh                            [conj_cone]
% 2.70/0.98  --conj_cone_tolerance                   3.
% 2.70/0.98  --extra_neg_conj                        none
% 2.70/0.98  --large_theory_mode                     true
% 2.70/0.98  --prolific_symb_bound                   200
% 2.70/0.98  --lt_threshold                          2000
% 2.70/0.98  --clause_weak_htbl                      true
% 2.70/0.98  --gc_record_bc_elim                     false
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing Options
% 2.70/0.98  
% 2.70/0.98  --preprocessing_flag                    true
% 2.70/0.98  --time_out_prep_mult                    0.1
% 2.70/0.98  --splitting_mode                        input
% 2.70/0.98  --splitting_grd                         true
% 2.70/0.98  --splitting_cvd                         false
% 2.70/0.98  --splitting_cvd_svl                     false
% 2.70/0.98  --splitting_nvd                         32
% 2.70/0.98  --sub_typing                            true
% 2.70/0.98  --prep_gs_sim                           true
% 2.70/0.98  --prep_unflatten                        true
% 2.70/0.98  --prep_res_sim                          true
% 2.70/0.98  --prep_upred                            true
% 2.70/0.98  --prep_sem_filter                       exhaustive
% 2.70/0.98  --prep_sem_filter_out                   false
% 2.70/0.98  --pred_elim                             true
% 2.70/0.98  --res_sim_input                         true
% 2.70/0.98  --eq_ax_congr_red                       true
% 2.70/0.98  --pure_diseq_elim                       true
% 2.70/0.98  --brand_transform                       false
% 2.70/0.98  --non_eq_to_eq                          false
% 2.70/0.98  --prep_def_merge                        true
% 2.70/0.98  --prep_def_merge_prop_impl              false
% 2.70/0.98  --prep_def_merge_mbd                    true
% 2.70/0.98  --prep_def_merge_tr_red                 false
% 2.70/0.98  --prep_def_merge_tr_cl                  false
% 2.70/0.98  --smt_preprocessing                     true
% 2.70/0.98  --smt_ac_axioms                         fast
% 2.70/0.98  --preprocessed_out                      false
% 2.70/0.98  --preprocessed_stats                    false
% 2.70/0.98  
% 2.70/0.98  ------ Abstraction refinement Options
% 2.70/0.98  
% 2.70/0.98  --abstr_ref                             []
% 2.70/0.98  --abstr_ref_prep                        false
% 2.70/0.98  --abstr_ref_until_sat                   false
% 2.70/0.98  --abstr_ref_sig_restrict                funpre
% 2.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.98  --abstr_ref_under                       []
% 2.70/0.98  
% 2.70/0.98  ------ SAT Options
% 2.70/0.98  
% 2.70/0.98  --sat_mode                              false
% 2.70/0.98  --sat_fm_restart_options                ""
% 2.70/0.98  --sat_gr_def                            false
% 2.70/0.98  --sat_epr_types                         true
% 2.70/0.98  --sat_non_cyclic_types                  false
% 2.70/0.98  --sat_finite_models                     false
% 2.70/0.98  --sat_fm_lemmas                         false
% 2.70/0.98  --sat_fm_prep                           false
% 2.70/0.98  --sat_fm_uc_incr                        true
% 2.70/0.98  --sat_out_model                         small
% 2.70/0.98  --sat_out_clauses                       false
% 2.70/0.98  
% 2.70/0.98  ------ QBF Options
% 2.70/0.98  
% 2.70/0.98  --qbf_mode                              false
% 2.70/0.98  --qbf_elim_univ                         false
% 2.70/0.98  --qbf_dom_inst                          none
% 2.70/0.98  --qbf_dom_pre_inst                      false
% 2.70/0.98  --qbf_sk_in                             false
% 2.70/0.98  --qbf_pred_elim                         true
% 2.70/0.98  --qbf_split                             512
% 2.70/0.98  
% 2.70/0.98  ------ BMC1 Options
% 2.70/0.98  
% 2.70/0.98  --bmc1_incremental                      false
% 2.70/0.98  --bmc1_axioms                           reachable_all
% 2.70/0.98  --bmc1_min_bound                        0
% 2.70/0.98  --bmc1_max_bound                        -1
% 2.70/0.98  --bmc1_max_bound_default                -1
% 2.70/0.98  --bmc1_symbol_reachability              true
% 2.70/0.98  --bmc1_property_lemmas                  false
% 2.70/0.98  --bmc1_k_induction                      false
% 2.70/0.98  --bmc1_non_equiv_states                 false
% 2.70/0.98  --bmc1_deadlock                         false
% 2.70/0.98  --bmc1_ucm                              false
% 2.70/0.98  --bmc1_add_unsat_core                   none
% 2.70/0.98  --bmc1_unsat_core_children              false
% 2.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.98  --bmc1_out_stat                         full
% 2.70/0.98  --bmc1_ground_init                      false
% 2.70/0.98  --bmc1_pre_inst_next_state              false
% 2.70/0.98  --bmc1_pre_inst_state                   false
% 2.70/0.98  --bmc1_pre_inst_reach_state             false
% 2.70/0.98  --bmc1_out_unsat_core                   false
% 2.70/0.98  --bmc1_aig_witness_out                  false
% 2.70/0.98  --bmc1_verbose                          false
% 2.70/0.98  --bmc1_dump_clauses_tptp                false
% 2.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.98  --bmc1_dump_file                        -
% 2.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.98  --bmc1_ucm_extend_mode                  1
% 2.70/0.98  --bmc1_ucm_init_mode                    2
% 2.70/0.98  --bmc1_ucm_cone_mode                    none
% 2.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.98  --bmc1_ucm_relax_model                  4
% 2.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.98  --bmc1_ucm_layered_model                none
% 2.70/0.98  --bmc1_ucm_max_lemma_size               10
% 2.70/0.98  
% 2.70/0.98  ------ AIG Options
% 2.70/0.98  
% 2.70/0.98  --aig_mode                              false
% 2.70/0.98  
% 2.70/0.98  ------ Instantiation Options
% 2.70/0.98  
% 2.70/0.98  --instantiation_flag                    true
% 2.70/0.98  --inst_sos_flag                         false
% 2.70/0.98  --inst_sos_phase                        true
% 2.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel_side                     none
% 2.70/0.98  --inst_solver_per_active                1400
% 2.70/0.98  --inst_solver_calls_frac                1.
% 2.70/0.98  --inst_passive_queue_type               priority_queues
% 2.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.98  --inst_passive_queues_freq              [25;2]
% 2.70/0.98  --inst_dismatching                      true
% 2.70/0.98  --inst_eager_unprocessed_to_passive     true
% 2.70/0.98  --inst_prop_sim_given                   true
% 2.70/0.98  --inst_prop_sim_new                     false
% 2.70/0.98  --inst_subs_new                         false
% 2.70/0.98  --inst_eq_res_simp                      false
% 2.70/0.98  --inst_subs_given                       false
% 2.70/0.98  --inst_orphan_elimination               true
% 2.70/0.98  --inst_learning_loop_flag               true
% 2.70/0.98  --inst_learning_start                   3000
% 2.70/0.98  --inst_learning_factor                  2
% 2.70/0.98  --inst_start_prop_sim_after_learn       3
% 2.70/0.98  --inst_sel_renew                        solver
% 2.70/0.98  --inst_lit_activity_flag                true
% 2.70/0.98  --inst_restr_to_given                   false
% 2.70/0.98  --inst_activity_threshold               500
% 2.70/0.98  --inst_out_proof                        true
% 2.70/0.98  
% 2.70/0.98  ------ Resolution Options
% 2.70/0.98  
% 2.70/0.98  --resolution_flag                       false
% 2.70/0.98  --res_lit_sel                           adaptive
% 2.70/0.98  --res_lit_sel_side                      none
% 2.70/0.98  --res_ordering                          kbo
% 2.70/0.98  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     false
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   []
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_full_bw                           [BwDemod]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ Proving...
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS status Theorem for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  fof(f5,axiom,(
% 2.70/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f15,plain,(
% 2.70/0.99    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 2.70/0.99    inference(ennf_transformation,[],[f5])).
% 2.70/0.99  
% 2.70/0.99  fof(f32,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f15])).
% 2.70/0.99  
% 2.70/0.99  fof(f2,axiom,(
% 2.70/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f13,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f2])).
% 2.70/0.99  
% 2.70/0.99  fof(f29,plain,(
% 2.70/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f13])).
% 2.70/0.99  
% 2.70/0.99  fof(f1,axiom,(
% 2.70/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f24,plain,(
% 2.70/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.70/0.99    inference(nnf_transformation,[],[f1])).
% 2.70/0.99  
% 2.70/0.99  fof(f28,plain,(
% 2.70/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f24])).
% 2.70/0.99  
% 2.70/0.99  fof(f4,axiom,(
% 2.70/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f14,plain,(
% 2.70/0.99    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 2.70/0.99    inference(ennf_transformation,[],[f4])).
% 2.70/0.99  
% 2.70/0.99  fof(f31,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f14])).
% 2.70/0.99  
% 2.70/0.99  fof(f11,conjecture,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f12,negated_conjecture,(
% 2.70/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 2.70/0.99    inference(negated_conjecture,[],[f11])).
% 2.70/0.99  
% 2.70/0.99  fof(f23,plain,(
% 2.70/0.99    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.70/0.99    inference(ennf_transformation,[],[f12])).
% 2.70/0.99  
% 2.70/0.99  fof(f25,plain,(
% 2.70/0.99    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f26,plain,(
% 2.70/0.99    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25])).
% 2.70/0.99  
% 2.70/0.99  fof(f38,plain,(
% 2.70/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.70/0.99    inference(cnf_transformation,[],[f26])).
% 2.70/0.99  
% 2.70/0.99  fof(f10,axiom,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f21,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 2.70/0.99    inference(ennf_transformation,[],[f10])).
% 2.70/0.99  
% 2.70/0.99  fof(f22,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 2.70/0.99    inference(flattening,[],[f21])).
% 2.70/0.99  
% 2.70/0.99  fof(f37,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f22])).
% 2.70/0.99  
% 2.70/0.99  fof(f7,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f17,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f7])).
% 2.70/0.99  
% 2.70/0.99  fof(f34,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f17])).
% 2.70/0.99  
% 2.70/0.99  fof(f27,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f24])).
% 2.70/0.99  
% 2.70/0.99  fof(f3,axiom,(
% 2.70/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f30,plain,(
% 2.70/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f3])).
% 2.70/0.99  
% 2.70/0.99  fof(f6,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f16,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f6])).
% 2.70/0.99  
% 2.70/0.99  fof(f33,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f16])).
% 2.70/0.99  
% 2.70/0.99  fof(f9,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f19,plain,(
% 2.70/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.70/0.99    inference(ennf_transformation,[],[f9])).
% 2.70/0.99  
% 2.70/0.99  fof(f20,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.70/0.99    inference(flattening,[],[f19])).
% 2.70/0.99  
% 2.70/0.99  fof(f36,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f20])).
% 2.70/0.99  
% 2.70/0.99  fof(f8,axiom,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f18,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f8])).
% 2.70/0.99  
% 2.70/0.99  fof(f35,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f18])).
% 2.70/0.99  
% 2.70/0.99  fof(f39,plain,(
% 2.70/0.99    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.70/0.99    inference(cnf_transformation,[],[f26])).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5,plain,
% 2.70/0.99      ( r1_tarski(k8_relat_1(X0,X1),X1) | ~ v1_relat_1(X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_188,plain,
% 2.70/0.99      ( r1_tarski(k8_relat_1(X0_42,X1_42),X1_42) | ~ v1_relat_1(X1_42) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_550,plain,
% 2.70/0.99      ( r1_tarski(k8_relat_1(X0_42,X1_42),X1_42) = iProver_top
% 2.70/0.99      | v1_relat_1(X1_42) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.70/0.99      | ~ v1_relat_1(X1)
% 2.70/0.99      | v1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_0,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_105,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.70/0.99      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_130,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.70/0.99      inference(bin_hyper_res,[status(thm)],[c_2,c_105]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_180,plain,
% 2.70/0.99      ( ~ r1_tarski(X0_42,X1_42)
% 2.70/0.99      | ~ v1_relat_1(X1_42)
% 2.70/0.99      | v1_relat_1(X0_42) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_130]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_558,plain,
% 2.70/0.99      ( r1_tarski(X0_42,X1_42) != iProver_top
% 2.70/0.99      | v1_relat_1(X1_42) != iProver_top
% 2.70/0.99      | v1_relat_1(X0_42) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1881,plain,
% 2.70/0.99      ( v1_relat_1(X0_42) != iProver_top
% 2.70/0.99      | v1_relat_1(k8_relat_1(X1_42,X0_42)) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_550,c_558]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4,plain,
% 2.70/0.99      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~ v1_relat_1(X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_189,plain,
% 2.70/0.99      ( r1_tarski(k2_relat_1(k8_relat_1(X0_42,X1_42)),X0_42)
% 2.70/0.99      | ~ v1_relat_1(X1_42) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_549,plain,
% 2.70/0.99      ( r1_tarski(k2_relat_1(k8_relat_1(X0_42,X1_42)),X0_42) = iProver_top
% 2.70/0.99      | v1_relat_1(X1_42) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_12,negated_conjecture,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_181,negated_conjecture,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_557,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_181]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_10,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_183,plain,
% 2.70/0.99      ( ~ r1_tarski(X0_42,X1_42)
% 2.70/0.99      | ~ m1_subset_1(X1_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X3_42)))
% 2.70/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X3_42))) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_555,plain,
% 2.70/0.99      ( r1_tarski(X0_42,X1_42) != iProver_top
% 2.70/0.99      | m1_subset_1(X1_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X3_42))) != iProver_top
% 2.70/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X2_42,X3_42))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1143,plain,
% 2.70/0.99      ( r1_tarski(X0_42,sK3) != iProver_top
% 2.70/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_557,c_555]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_7,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_186,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
% 2.70/0.99      | k1_relset_1(X1_42,X2_42,X0_42) = k1_relat_1(X0_42) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_552,plain,
% 2.70/0.99      ( k1_relset_1(X0_42,X1_42,X2_42) = k1_relat_1(X2_42)
% 2.70/0.99      | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1401,plain,
% 2.70/0.99      ( k1_relset_1(sK2,sK0,X0_42) = k1_relat_1(X0_42)
% 2.70/0.99      | r1_tarski(X0_42,sK3) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1143,c_552]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1550,plain,
% 2.70/0.99      ( k1_relset_1(sK2,sK0,k8_relat_1(X0_42,sK3)) = k1_relat_1(k8_relat_1(X0_42,sK3))
% 2.70/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_550,c_1401]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_13,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1,plain,
% 2.70/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_191,plain,
% 2.70/0.99      ( r1_tarski(X0_42,X1_42)
% 2.70/0.99      | ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_642,plain,
% 2.70/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
% 2.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_191]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_643,plain,
% 2.70/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) = iProver_top
% 2.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_670,plain,
% 2.70/0.99      ( ~ r1_tarski(X0_42,k2_zfmisc_1(X1_42,X2_42))
% 2.70/0.99      | v1_relat_1(X0_42)
% 2.70/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1_42,X2_42)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_180]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_749,plain,
% 2.70/0.99      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
% 2.70/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
% 2.70/0.99      | v1_relat_1(sK3) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_670]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_750,plain,
% 2.70/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) != iProver_top
% 2.70/0.99      | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
% 2.70/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3,plain,
% 2.70/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_190,plain,
% 2.70/0.99      ( v1_relat_1(k2_zfmisc_1(X0_42,X1_42)) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_794,plain,
% 2.70/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_190]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_795,plain,
% 2.70/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2470,plain,
% 2.70/0.99      ( k1_relset_1(sK2,sK0,k8_relat_1(X0_42,sK3)) = k1_relat_1(k8_relat_1(X0_42,sK3)) ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_1550,c_13,c_643,c_750,c_795]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_6,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_187,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
% 2.70/0.99      | m1_subset_1(k1_relset_1(X1_42,X2_42,X0_42),k1_zfmisc_1(X1_42)) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_551,plain,
% 2.70/0.99      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) != iProver_top
% 2.70/0.99      | m1_subset_1(k1_relset_1(X1_42,X2_42,X0_42),k1_zfmisc_1(X1_42)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_547,plain,
% 2.70/0.99      ( r1_tarski(X0_42,X1_42) = iProver_top
% 2.70/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_932,plain,
% 2.70/0.99      ( r1_tarski(k1_relset_1(X0_42,X1_42,X2_42),X0_42) = iProver_top
% 2.70/0.99      | m1_subset_1(X2_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_551,c_547]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2881,plain,
% 2.70/0.99      ( r1_tarski(X0_42,sK3) != iProver_top
% 2.70/0.99      | r1_tarski(k1_relset_1(sK2,sK0,X0_42),sK2) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1143,c_932]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3273,plain,
% 2.70/0.99      ( r1_tarski(k8_relat_1(X0_42,sK3),sK3) != iProver_top
% 2.70/0.99      | r1_tarski(k1_relat_1(k8_relat_1(X0_42,sK3)),sK2) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2470,c_2881]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_977,plain,
% 2.70/0.99      ( r1_tarski(k8_relat_1(X0_42,sK3),sK3) | ~ v1_relat_1(sK3) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_188]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_983,plain,
% 2.70/0.99      ( r1_tarski(k8_relat_1(X0_42,sK3),sK3) = iProver_top
% 2.70/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3690,plain,
% 2.70/0.99      ( r1_tarski(k1_relat_1(k8_relat_1(X0_42,sK3)),sK2) = iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3273,c_13,c_643,c_750,c_795,c_983]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_9,plain,
% 2.70/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.70/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ v1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_184,plain,
% 2.70/0.99      ( ~ r1_tarski(k1_relat_1(X0_42),X1_42)
% 2.70/0.99      | ~ r1_tarski(k2_relat_1(X0_42),X2_42)
% 2.70/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
% 2.70/0.99      | ~ v1_relat_1(X0_42) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_554,plain,
% 2.70/0.99      ( r1_tarski(k1_relat_1(X0_42),X1_42) != iProver_top
% 2.70/0.99      | r1_tarski(k2_relat_1(X0_42),X2_42) != iProver_top
% 2.70/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) = iProver_top
% 2.70/0.99      | v1_relat_1(X0_42) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_8,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_185,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
% 2.70/0.99      | k6_relset_1(X1_42,X2_42,X3_42,X0_42) = k8_relat_1(X3_42,X0_42) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_553,plain,
% 2.70/0.99      ( k6_relset_1(X0_42,X1_42,X2_42,X3_42) = k8_relat_1(X2_42,X3_42)
% 2.70/0.99      | m1_subset_1(X3_42,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1081,plain,
% 2.70/0.99      ( k6_relset_1(sK2,sK0,X0_42,sK3) = k8_relat_1(X0_42,sK3) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_557,c_553]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_11,negated_conjecture,
% 2.70/0.99      ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_182,negated_conjecture,
% 2.70/0.99      ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_556,plain,
% 2.70/0.99      ( m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_182]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1249,plain,
% 2.70/0.99      ( m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_1081,c_556]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1686,plain,
% 2.70/0.99      ( r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2) != iProver_top
% 2.70/0.99      | r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top
% 2.70/0.99      | v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_554,c_1249]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3699,plain,
% 2.70/0.99      ( r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top
% 2.70/0.99      | v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_3690,c_1686]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3722,plain,
% 2.70/0.99      ( v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top
% 2.70/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_549,c_3699]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4737,plain,
% 2.70/0.99      ( v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3722,c_13,c_643,c_750,c_795]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4742,plain,
% 2.70/0.99      ( v1_relat_1(sK3) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1881,c_4737]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(contradiction,plain,
% 2.70/0.99      ( $false ),
% 2.70/0.99      inference(minisat,[status(thm)],[c_4742,c_795,c_750,c_643,c_13]) ).
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  ------                               Statistics
% 2.70/0.99  
% 2.70/0.99  ------ General
% 2.70/0.99  
% 2.70/0.99  abstr_ref_over_cycles:                  0
% 2.70/0.99  abstr_ref_under_cycles:                 0
% 2.70/0.99  gc_basic_clause_elim:                   0
% 2.70/0.99  forced_gc_time:                         0
% 2.70/0.99  parsing_time:                           0.008
% 2.70/0.99  unif_index_cands_time:                  0.
% 2.70/0.99  unif_index_add_time:                    0.
% 2.70/0.99  orderings_time:                         0.
% 2.70/0.99  out_proof_time:                         0.01
% 2.70/0.99  total_time:                             0.244
% 2.70/0.99  num_of_symbols:                         47
% 2.70/0.99  num_of_terms:                           7065
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing
% 2.70/0.99  
% 2.70/0.99  num_of_splits:                          0
% 2.70/0.99  num_of_split_atoms:                     0
% 2.70/0.99  num_of_reused_defs:                     0
% 2.70/0.99  num_eq_ax_congr_red:                    14
% 2.70/0.99  num_of_sem_filtered_clauses:            1
% 2.70/0.99  num_of_subtypes:                        2
% 2.70/0.99  monotx_restored_types:                  0
% 2.70/0.99  sat_num_of_epr_types:                   0
% 2.70/0.99  sat_num_of_non_cyclic_types:            0
% 2.70/0.99  sat_guarded_non_collapsed_types:        0
% 2.70/0.99  num_pure_diseq_elim:                    0
% 2.70/0.99  simp_replaced_by:                       0
% 2.70/0.99  res_preprocessed:                       60
% 2.70/0.99  prep_upred:                             0
% 2.70/0.99  prep_unflattend:                        0
% 2.70/0.99  smt_new_axioms:                         0
% 2.70/0.99  pred_elim_cands:                        3
% 2.70/0.99  pred_elim:                              0
% 2.70/0.99  pred_elim_cl:                           0
% 2.70/0.99  pred_elim_cycles:                       1
% 2.70/0.99  merged_defs:                            6
% 2.70/0.99  merged_defs_ncl:                        0
% 2.70/0.99  bin_hyper_res:                          7
% 2.70/0.99  prep_cycles:                            3
% 2.70/0.99  pred_elim_time:                         0.
% 2.70/0.99  splitting_time:                         0.
% 2.70/0.99  sem_filter_time:                        0.
% 2.70/0.99  monotx_time:                            0.
% 2.70/0.99  subtype_inf_time:                       0.
% 2.70/0.99  
% 2.70/0.99  ------ Problem properties
% 2.70/0.99  
% 2.70/0.99  clauses:                                13
% 2.70/0.99  conjectures:                            2
% 2.70/0.99  epr:                                    1
% 2.70/0.99  horn:                                   13
% 2.70/0.99  ground:                                 2
% 2.70/0.99  unary:                                  3
% 2.70/0.99  binary:                                 7
% 2.70/0.99  lits:                                   27
% 2.70/0.99  lits_eq:                                2
% 2.70/0.99  fd_pure:                                0
% 2.70/0.99  fd_pseudo:                              0
% 2.70/0.99  fd_cond:                                0
% 2.70/0.99  fd_pseudo_cond:                         0
% 2.70/0.99  ac_symbols:                             0
% 2.70/0.99  
% 2.70/0.99  ------ Propositional Solver
% 2.70/0.99  
% 2.70/0.99  prop_solver_calls:                      25
% 2.70/0.99  prop_fast_solver_calls:                 374
% 2.70/0.99  smt_solver_calls:                       0
% 2.70/0.99  smt_fast_solver_calls:                  0
% 2.70/0.99  prop_num_of_clauses:                    2469
% 2.70/0.99  prop_preprocess_simplified:             5039
% 2.70/0.99  prop_fo_subsumed:                       8
% 2.70/0.99  prop_solver_time:                       0.
% 2.70/0.99  smt_solver_time:                        0.
% 2.70/0.99  smt_fast_solver_time:                   0.
% 2.70/0.99  prop_fast_solver_time:                  0.
% 2.70/0.99  prop_unsat_core_time:                   0.
% 2.70/0.99  
% 2.70/0.99  ------ QBF
% 2.70/0.99  
% 2.70/0.99  qbf_q_res:                              0
% 2.70/0.99  qbf_num_tautologies:                    0
% 2.70/0.99  qbf_prep_cycles:                        0
% 2.70/0.99  
% 2.70/0.99  ------ BMC1
% 2.70/0.99  
% 2.70/0.99  bmc1_current_bound:                     -1
% 2.70/0.99  bmc1_last_solved_bound:                 -1
% 2.70/0.99  bmc1_unsat_core_size:                   -1
% 2.70/0.99  bmc1_unsat_core_parents_size:           -1
% 2.70/0.99  bmc1_merge_next_fun:                    0
% 2.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation
% 2.70/0.99  
% 2.70/0.99  inst_num_of_clauses:                    616
% 2.70/0.99  inst_num_in_passive:                    169
% 2.70/0.99  inst_num_in_active:                     237
% 2.70/0.99  inst_num_in_unprocessed:                211
% 2.70/0.99  inst_num_of_loops:                      250
% 2.70/0.99  inst_num_of_learning_restarts:          0
% 2.70/0.99  inst_num_moves_active_passive:          10
% 2.70/0.99  inst_lit_activity:                      0
% 2.70/0.99  inst_lit_activity_moves:                0
% 2.70/0.99  inst_num_tautologies:                   0
% 2.70/0.99  inst_num_prop_implied:                  0
% 2.70/0.99  inst_num_existing_simplified:           0
% 2.70/0.99  inst_num_eq_res_simplified:             0
% 2.70/0.99  inst_num_child_elim:                    0
% 2.70/0.99  inst_num_of_dismatching_blockings:      98
% 2.70/0.99  inst_num_of_non_proper_insts:           371
% 2.70/0.99  inst_num_of_duplicates:                 0
% 2.70/0.99  inst_inst_num_from_inst_to_res:         0
% 2.70/0.99  inst_dismatching_checking_time:         0.
% 2.70/0.99  
% 2.70/0.99  ------ Resolution
% 2.70/0.99  
% 2.70/0.99  res_num_of_clauses:                     0
% 2.70/0.99  res_num_in_passive:                     0
% 2.70/0.99  res_num_in_active:                      0
% 2.70/0.99  res_num_of_loops:                       63
% 2.70/0.99  res_forward_subset_subsumed:            17
% 2.70/0.99  res_backward_subset_subsumed:           2
% 2.70/0.99  res_forward_subsumed:                   0
% 2.70/0.99  res_backward_subsumed:                  0
% 2.70/0.99  res_forward_subsumption_resolution:     0
% 2.70/0.99  res_backward_subsumption_resolution:    0
% 2.70/0.99  res_clause_to_clause_subsumption:       242
% 2.70/0.99  res_orphan_elimination:                 0
% 2.70/0.99  res_tautology_del:                      59
% 2.70/0.99  res_num_eq_res_simplified:              0
% 2.70/0.99  res_num_sel_changes:                    0
% 2.70/0.99  res_moves_from_active_to_pass:          0
% 2.70/0.99  
% 2.70/0.99  ------ Superposition
% 2.70/0.99  
% 2.70/0.99  sup_time_total:                         0.
% 2.70/0.99  sup_time_generating:                    0.
% 2.70/0.99  sup_time_sim_full:                      0.
% 2.70/0.99  sup_time_sim_immed:                     0.
% 2.70/0.99  
% 2.70/0.99  sup_num_of_clauses:                     99
% 2.70/0.99  sup_num_in_active:                      47
% 2.70/0.99  sup_num_in_passive:                     52
% 2.70/0.99  sup_num_of_loops:                       48
% 2.70/0.99  sup_fw_superposition:                   53
% 2.70/0.99  sup_bw_superposition:                   47
% 2.70/0.99  sup_immediate_simplified:               7
% 2.70/0.99  sup_given_eliminated:                   0
% 2.70/0.99  comparisons_done:                       0
% 2.70/0.99  comparisons_avoided:                    0
% 2.70/0.99  
% 2.70/0.99  ------ Simplifications
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  sim_fw_subset_subsumed:                 4
% 2.70/0.99  sim_bw_subset_subsumed:                 1
% 2.70/0.99  sim_fw_subsumed:                        2
% 2.70/0.99  sim_bw_subsumed:                        0
% 2.70/0.99  sim_fw_subsumption_res:                 0
% 2.70/0.99  sim_bw_subsumption_res:                 0
% 2.70/0.99  sim_tautology_del:                      1
% 2.70/0.99  sim_eq_tautology_del:                   0
% 2.70/0.99  sim_eq_res_simp:                        0
% 2.70/0.99  sim_fw_demodulated:                     0
% 2.70/0.99  sim_bw_demodulated:                     2
% 2.70/0.99  sim_light_normalised:                   1
% 2.70/0.99  sim_joinable_taut:                      0
% 2.70/0.99  sim_joinable_simp:                      0
% 2.70/0.99  sim_ac_normalised:                      0
% 2.70/0.99  sim_smt_subsumption:                    0
% 2.70/0.99  
%------------------------------------------------------------------------------
