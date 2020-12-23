%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:32 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 282 expanded)
%              Number of clauses        :   73 ( 127 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  274 ( 663 expanded)
%              Number of equality atoms :   97 ( 144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f33])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f39,f47])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_300,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_585,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_302,plain,
    ( m1_subset_1(k6_partfun1(X0_44),k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_44))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_583,plain,
    ( m1_subset_1(k6_partfun1(X0_44),k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_44))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | ~ m1_subset_1(X3_44,k1_zfmisc_1(k2_zfmisc_1(X4_44,X5_44)))
    | k4_relset_1(X4_44,X5_44,X1_44,X2_44,X3_44,X0_44) = k5_relat_1(X3_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_581,plain,
    ( k4_relset_1(X0_44,X1_44,X2_44,X3_44,X4_44,X5_44) = k5_relat_1(X4_44,X5_44)
    | m1_subset_1(X5_44,k1_zfmisc_1(k2_zfmisc_1(X2_44,X3_44))) != iProver_top
    | m1_subset_1(X4_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_1160,plain,
    ( k4_relset_1(X0_44,X1_44,X2_44,X2_44,X3_44,k6_partfun1(X2_44)) = k5_relat_1(X3_44,k6_partfun1(X2_44))
    | m1_subset_1(X3_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_581])).

cnf(c_4962,plain,
    ( k4_relset_1(sK0,sK1,X0_44,X0_44,sK2,k6_partfun1(X0_44)) = k5_relat_1(sK2,k6_partfun1(X0_44)) ),
    inference(superposition,[status(thm)],[c_585,c_1160])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | k1_relset_1(X1_44,X2_44,X0_44) = k1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_579,plain,
    ( k1_relset_1(X0_44,X1_44,X2_44) = k1_relat_1(X2_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_785,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_585,c_579])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | m1_subset_1(k1_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_577,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_965,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_577])).

cnf(c_14,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1513,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_965,c_14])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_166,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k5_relat_1(k6_partfun1(X3),X2) = X2
    | k1_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_167,plain,
    ( ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_166])).

cnf(c_299,plain,
    ( ~ m1_subset_1(k1_relat_1(X0_44),k1_zfmisc_1(X1_44))
    | ~ v1_relat_1(X0_44)
    | k5_relat_1(k6_partfun1(X1_44),X0_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_167])).

cnf(c_586,plain,
    ( k5_relat_1(k6_partfun1(X0_44),X1_44) = X1_44
    | m1_subset_1(k1_relat_1(X1_44),k1_zfmisc_1(X0_44)) != iProver_top
    | v1_relat_1(X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_1524,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1513,c_586])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ v1_relat_1(X1_44)
    | v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | v1_relat_1(X0_44)
    | ~ v1_relat_1(k2_zfmisc_1(X1_44,X2_44)) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_764,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_309,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_812,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_992,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_965])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_44))
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k6_partfun1(X0_44),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_1042,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_1865,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1524,c_13,c_764,c_812,c_992,c_1042])).

cnf(c_1159,plain,
    ( k4_relset_1(X0_44,X1_44,sK0,sK1,X2_44,sK2) = k5_relat_1(X2_44,sK2)
    | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_581])).

cnf(c_1369,plain,
    ( k4_relset_1(X0_44,X0_44,sK0,sK1,k6_partfun1(X0_44),sK2) = k5_relat_1(k6_partfun1(X0_44),sK2) ),
    inference(superposition,[status(thm)],[c_583,c_1159])).

cnf(c_12,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_301,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_584,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_1434,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1369,c_584])).

cnf(c_1868,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1865,c_1434])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_303,plain,
    ( r2_relset_1(X0_44,X1_44,X2_44,X2_44)
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)))
    | ~ m1_subset_1(X3_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_735,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_869,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_870,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_869])).

cnf(c_1983,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1868,c_14,c_870])).

cnf(c_4995,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4962,c_1983])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | k2_relset_1(X1_44,X2_44,X0_44) = k2_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_580,plain,
    ( k2_relset_1(X0_44,X1_44,X2_44) = k2_relat_1(X2_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_862,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_585,c_580])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | m1_subset_1(k2_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X2_44)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_578,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X2_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_1196,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_578])).

cnf(c_1650,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1196,c_14])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k5_relat_1(X2,k6_partfun1(X3)) = X2
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_182,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_298,plain,
    ( ~ m1_subset_1(k2_relat_1(X0_44),k1_zfmisc_1(X1_44))
    | ~ v1_relat_1(X0_44)
    | k5_relat_1(X0_44,k6_partfun1(X1_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_182])).

cnf(c_587,plain,
    ( k5_relat_1(X0_44,k6_partfun1(X1_44)) = X0_44
    | m1_subset_1(k2_relat_1(X0_44),k1_zfmisc_1(X1_44)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_2363,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_587])).

cnf(c_765,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_813,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_2583,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2363,c_14,c_765,c_813])).

cnf(c_4996,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4995,c_2583])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4996,c_870,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.34/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/0.99  
% 2.34/0.99  ------  iProver source info
% 2.34/0.99  
% 2.34/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.34/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/0.99  git: non_committed_changes: false
% 2.34/0.99  git: last_make_outside_of_git: false
% 2.34/0.99  
% 2.34/0.99  ------ 
% 2.34/0.99  
% 2.34/0.99  ------ Input Options
% 2.34/0.99  
% 2.34/0.99  --out_options                           all
% 2.34/0.99  --tptp_safe_out                         true
% 2.34/0.99  --problem_path                          ""
% 2.34/0.99  --include_path                          ""
% 2.34/0.99  --clausifier                            res/vclausify_rel
% 2.34/0.99  --clausifier_options                    --mode clausify
% 2.34/0.99  --stdin                                 false
% 2.34/0.99  --stats_out                             all
% 2.34/0.99  
% 2.34/0.99  ------ General Options
% 2.34/0.99  
% 2.34/0.99  --fof                                   false
% 2.34/0.99  --time_out_real                         305.
% 2.34/0.99  --time_out_virtual                      -1.
% 2.34/0.99  --symbol_type_check                     false
% 2.34/0.99  --clausify_out                          false
% 2.34/0.99  --sig_cnt_out                           false
% 2.34/0.99  --trig_cnt_out                          false
% 2.34/0.99  --trig_cnt_out_tolerance                1.
% 2.34/0.99  --trig_cnt_out_sk_spl                   false
% 2.34/0.99  --abstr_cl_out                          false
% 2.34/0.99  
% 2.34/0.99  ------ Global Options
% 2.34/0.99  
% 2.34/0.99  --schedule                              default
% 2.34/0.99  --add_important_lit                     false
% 2.34/0.99  --prop_solver_per_cl                    1000
% 2.34/0.99  --min_unsat_core                        false
% 2.34/0.99  --soft_assumptions                      false
% 2.34/0.99  --soft_lemma_size                       3
% 2.34/0.99  --prop_impl_unit_size                   0
% 2.34/0.99  --prop_impl_unit                        []
% 2.34/0.99  --share_sel_clauses                     true
% 2.34/0.99  --reset_solvers                         false
% 2.34/0.99  --bc_imp_inh                            [conj_cone]
% 2.34/0.99  --conj_cone_tolerance                   3.
% 2.34/0.99  --extra_neg_conj                        none
% 2.34/0.99  --large_theory_mode                     true
% 2.34/0.99  --prolific_symb_bound                   200
% 2.34/0.99  --lt_threshold                          2000
% 2.34/0.99  --clause_weak_htbl                      true
% 2.34/0.99  --gc_record_bc_elim                     false
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing Options
% 2.34/0.99  
% 2.34/0.99  --preprocessing_flag                    true
% 2.34/0.99  --time_out_prep_mult                    0.1
% 2.34/0.99  --splitting_mode                        input
% 2.34/0.99  --splitting_grd                         true
% 2.34/0.99  --splitting_cvd                         false
% 2.34/0.99  --splitting_cvd_svl                     false
% 2.34/0.99  --splitting_nvd                         32
% 2.34/0.99  --sub_typing                            true
% 2.34/0.99  --prep_gs_sim                           true
% 2.34/0.99  --prep_unflatten                        true
% 2.34/0.99  --prep_res_sim                          true
% 2.34/0.99  --prep_upred                            true
% 2.34/0.99  --prep_sem_filter                       exhaustive
% 2.34/0.99  --prep_sem_filter_out                   false
% 2.34/0.99  --pred_elim                             true
% 2.34/0.99  --res_sim_input                         true
% 2.34/0.99  --eq_ax_congr_red                       true
% 2.34/0.99  --pure_diseq_elim                       true
% 2.34/0.99  --brand_transform                       false
% 2.34/0.99  --non_eq_to_eq                          false
% 2.34/0.99  --prep_def_merge                        true
% 2.34/0.99  --prep_def_merge_prop_impl              false
% 2.34/0.99  --prep_def_merge_mbd                    true
% 2.34/0.99  --prep_def_merge_tr_red                 false
% 2.34/0.99  --prep_def_merge_tr_cl                  false
% 2.34/0.99  --smt_preprocessing                     true
% 2.34/0.99  --smt_ac_axioms                         fast
% 2.34/0.99  --preprocessed_out                      false
% 2.34/0.99  --preprocessed_stats                    false
% 2.34/0.99  
% 2.34/0.99  ------ Abstraction refinement Options
% 2.34/0.99  
% 2.34/0.99  --abstr_ref                             []
% 2.34/0.99  --abstr_ref_prep                        false
% 2.34/0.99  --abstr_ref_until_sat                   false
% 2.34/0.99  --abstr_ref_sig_restrict                funpre
% 2.34/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.99  --abstr_ref_under                       []
% 2.34/0.99  
% 2.34/0.99  ------ SAT Options
% 2.34/0.99  
% 2.34/0.99  --sat_mode                              false
% 2.34/0.99  --sat_fm_restart_options                ""
% 2.34/0.99  --sat_gr_def                            false
% 2.34/0.99  --sat_epr_types                         true
% 2.34/0.99  --sat_non_cyclic_types                  false
% 2.34/0.99  --sat_finite_models                     false
% 2.34/0.99  --sat_fm_lemmas                         false
% 2.34/0.99  --sat_fm_prep                           false
% 2.34/0.99  --sat_fm_uc_incr                        true
% 2.34/0.99  --sat_out_model                         small
% 2.34/0.99  --sat_out_clauses                       false
% 2.34/0.99  
% 2.34/0.99  ------ QBF Options
% 2.34/0.99  
% 2.34/0.99  --qbf_mode                              false
% 2.34/0.99  --qbf_elim_univ                         false
% 2.34/0.99  --qbf_dom_inst                          none
% 2.34/0.99  --qbf_dom_pre_inst                      false
% 2.34/0.99  --qbf_sk_in                             false
% 2.34/0.99  --qbf_pred_elim                         true
% 2.34/0.99  --qbf_split                             512
% 2.34/0.99  
% 2.34/0.99  ------ BMC1 Options
% 2.34/0.99  
% 2.34/0.99  --bmc1_incremental                      false
% 2.34/0.99  --bmc1_axioms                           reachable_all
% 2.34/0.99  --bmc1_min_bound                        0
% 2.34/0.99  --bmc1_max_bound                        -1
% 2.34/0.99  --bmc1_max_bound_default                -1
% 2.34/0.99  --bmc1_symbol_reachability              true
% 2.34/0.99  --bmc1_property_lemmas                  false
% 2.34/0.99  --bmc1_k_induction                      false
% 2.34/0.99  --bmc1_non_equiv_states                 false
% 2.34/0.99  --bmc1_deadlock                         false
% 2.34/0.99  --bmc1_ucm                              false
% 2.34/0.99  --bmc1_add_unsat_core                   none
% 2.34/0.99  --bmc1_unsat_core_children              false
% 2.34/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.99  --bmc1_out_stat                         full
% 2.34/0.99  --bmc1_ground_init                      false
% 2.34/0.99  --bmc1_pre_inst_next_state              false
% 2.34/0.99  --bmc1_pre_inst_state                   false
% 2.34/0.99  --bmc1_pre_inst_reach_state             false
% 2.34/0.99  --bmc1_out_unsat_core                   false
% 2.34/0.99  --bmc1_aig_witness_out                  false
% 2.34/0.99  --bmc1_verbose                          false
% 2.34/0.99  --bmc1_dump_clauses_tptp                false
% 2.34/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.99  --bmc1_dump_file                        -
% 2.34/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.99  --bmc1_ucm_extend_mode                  1
% 2.34/0.99  --bmc1_ucm_init_mode                    2
% 2.34/0.99  --bmc1_ucm_cone_mode                    none
% 2.34/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.99  --bmc1_ucm_relax_model                  4
% 2.34/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.99  --bmc1_ucm_layered_model                none
% 2.34/0.99  --bmc1_ucm_max_lemma_size               10
% 2.34/0.99  
% 2.34/0.99  ------ AIG Options
% 2.34/0.99  
% 2.34/0.99  --aig_mode                              false
% 2.34/0.99  
% 2.34/0.99  ------ Instantiation Options
% 2.34/0.99  
% 2.34/0.99  --instantiation_flag                    true
% 2.34/0.99  --inst_sos_flag                         false
% 2.34/0.99  --inst_sos_phase                        true
% 2.34/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel_side                     num_symb
% 2.34/0.99  --inst_solver_per_active                1400
% 2.34/0.99  --inst_solver_calls_frac                1.
% 2.34/0.99  --inst_passive_queue_type               priority_queues
% 2.34/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.99  --inst_passive_queues_freq              [25;2]
% 2.34/0.99  --inst_dismatching                      true
% 2.34/0.99  --inst_eager_unprocessed_to_passive     true
% 2.34/0.99  --inst_prop_sim_given                   true
% 2.34/0.99  --inst_prop_sim_new                     false
% 2.34/0.99  --inst_subs_new                         false
% 2.34/0.99  --inst_eq_res_simp                      false
% 2.34/0.99  --inst_subs_given                       false
% 2.34/0.99  --inst_orphan_elimination               true
% 2.34/0.99  --inst_learning_loop_flag               true
% 2.34/0.99  --inst_learning_start                   3000
% 2.34/0.99  --inst_learning_factor                  2
% 2.34/0.99  --inst_start_prop_sim_after_learn       3
% 2.34/0.99  --inst_sel_renew                        solver
% 2.34/0.99  --inst_lit_activity_flag                true
% 2.34/0.99  --inst_restr_to_given                   false
% 2.34/0.99  --inst_activity_threshold               500
% 2.34/0.99  --inst_out_proof                        true
% 2.34/0.99  
% 2.34/0.99  ------ Resolution Options
% 2.34/0.99  
% 2.34/0.99  --resolution_flag                       true
% 2.34/0.99  --res_lit_sel                           adaptive
% 2.34/0.99  --res_lit_sel_side                      none
% 2.34/0.99  --res_ordering                          kbo
% 2.34/0.99  --res_to_prop_solver                    active
% 2.34/0.99  --res_prop_simpl_new                    false
% 2.34/0.99  --res_prop_simpl_given                  true
% 2.34/0.99  --res_passive_queue_type                priority_queues
% 2.34/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.99  --res_passive_queues_freq               [15;5]
% 2.34/0.99  --res_forward_subs                      full
% 2.34/0.99  --res_backward_subs                     full
% 2.34/0.99  --res_forward_subs_resolution           true
% 2.34/0.99  --res_backward_subs_resolution          true
% 2.34/0.99  --res_orphan_elimination                true
% 2.34/0.99  --res_time_limit                        2.
% 2.34/0.99  --res_out_proof                         true
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Options
% 2.34/0.99  
% 2.34/0.99  --superposition_flag                    true
% 2.34/0.99  --sup_passive_queue_type                priority_queues
% 2.34/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.99  --demod_completeness_check              fast
% 2.34/0.99  --demod_use_ground                      true
% 2.34/0.99  --sup_to_prop_solver                    passive
% 2.34/0.99  --sup_prop_simpl_new                    true
% 2.34/0.99  --sup_prop_simpl_given                  true
% 2.34/0.99  --sup_fun_splitting                     false
% 2.34/0.99  --sup_smt_interval                      50000
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Simplification Setup
% 2.34/0.99  
% 2.34/0.99  --sup_indices_passive                   []
% 2.34/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_full_bw                           [BwDemod]
% 2.34/0.99  --sup_immed_triv                        [TrivRules]
% 2.34/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_immed_bw_main                     []
% 2.34/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  
% 2.34/0.99  ------ Combination Options
% 2.34/0.99  
% 2.34/0.99  --comb_res_mult                         3
% 2.34/0.99  --comb_sup_mult                         2
% 2.34/0.99  --comb_inst_mult                        10
% 2.34/0.99  
% 2.34/0.99  ------ Debug Options
% 2.34/0.99  
% 2.34/0.99  --dbg_backtrace                         false
% 2.34/0.99  --dbg_dump_prop_clauses                 false
% 2.34/0.99  --dbg_dump_prop_clauses_file            -
% 2.34/0.99  --dbg_out_stat                          false
% 2.34/0.99  ------ Parsing...
% 2.34/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/0.99  ------ Proving...
% 2.34/0.99  ------ Problem Properties 
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  clauses                                 13
% 2.34/0.99  conjectures                             2
% 2.34/0.99  EPR                                     0
% 2.34/0.99  Horn                                    13
% 2.34/0.99  unary                                   3
% 2.34/0.99  binary                                  5
% 2.34/0.99  lits                                    28
% 2.34/0.99  lits eq                                 5
% 2.34/0.99  fd_pure                                 0
% 2.34/0.99  fd_pseudo                               0
% 2.34/0.99  fd_cond                                 0
% 2.34/0.99  fd_pseudo_cond                          0
% 2.34/0.99  AC symbols                              0
% 2.34/0.99  
% 2.34/0.99  ------ Schedule dynamic 5 is on 
% 2.34/0.99  
% 2.34/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  ------ 
% 2.34/0.99  Current options:
% 2.34/0.99  ------ 
% 2.34/0.99  
% 2.34/0.99  ------ Input Options
% 2.34/0.99  
% 2.34/0.99  --out_options                           all
% 2.34/0.99  --tptp_safe_out                         true
% 2.34/0.99  --problem_path                          ""
% 2.34/0.99  --include_path                          ""
% 2.34/0.99  --clausifier                            res/vclausify_rel
% 2.34/0.99  --clausifier_options                    --mode clausify
% 2.34/0.99  --stdin                                 false
% 2.34/0.99  --stats_out                             all
% 2.34/0.99  
% 2.34/0.99  ------ General Options
% 2.34/0.99  
% 2.34/0.99  --fof                                   false
% 2.34/0.99  --time_out_real                         305.
% 2.34/0.99  --time_out_virtual                      -1.
% 2.34/0.99  --symbol_type_check                     false
% 2.34/0.99  --clausify_out                          false
% 2.34/0.99  --sig_cnt_out                           false
% 2.34/0.99  --trig_cnt_out                          false
% 2.34/0.99  --trig_cnt_out_tolerance                1.
% 2.34/0.99  --trig_cnt_out_sk_spl                   false
% 2.34/0.99  --abstr_cl_out                          false
% 2.34/0.99  
% 2.34/0.99  ------ Global Options
% 2.34/0.99  
% 2.34/0.99  --schedule                              default
% 2.34/0.99  --add_important_lit                     false
% 2.34/0.99  --prop_solver_per_cl                    1000
% 2.34/0.99  --min_unsat_core                        false
% 2.34/0.99  --soft_assumptions                      false
% 2.34/0.99  --soft_lemma_size                       3
% 2.34/0.99  --prop_impl_unit_size                   0
% 2.34/0.99  --prop_impl_unit                        []
% 2.34/0.99  --share_sel_clauses                     true
% 2.34/0.99  --reset_solvers                         false
% 2.34/0.99  --bc_imp_inh                            [conj_cone]
% 2.34/0.99  --conj_cone_tolerance                   3.
% 2.34/0.99  --extra_neg_conj                        none
% 2.34/0.99  --large_theory_mode                     true
% 2.34/0.99  --prolific_symb_bound                   200
% 2.34/0.99  --lt_threshold                          2000
% 2.34/0.99  --clause_weak_htbl                      true
% 2.34/0.99  --gc_record_bc_elim                     false
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing Options
% 2.34/0.99  
% 2.34/0.99  --preprocessing_flag                    true
% 2.34/0.99  --time_out_prep_mult                    0.1
% 2.34/0.99  --splitting_mode                        input
% 2.34/0.99  --splitting_grd                         true
% 2.34/0.99  --splitting_cvd                         false
% 2.34/0.99  --splitting_cvd_svl                     false
% 2.34/0.99  --splitting_nvd                         32
% 2.34/0.99  --sub_typing                            true
% 2.34/0.99  --prep_gs_sim                           true
% 2.34/0.99  --prep_unflatten                        true
% 2.34/0.99  --prep_res_sim                          true
% 2.34/0.99  --prep_upred                            true
% 2.34/0.99  --prep_sem_filter                       exhaustive
% 2.34/0.99  --prep_sem_filter_out                   false
% 2.34/0.99  --pred_elim                             true
% 2.34/0.99  --res_sim_input                         true
% 2.34/0.99  --eq_ax_congr_red                       true
% 2.34/0.99  --pure_diseq_elim                       true
% 2.34/0.99  --brand_transform                       false
% 2.34/0.99  --non_eq_to_eq                          false
% 2.34/0.99  --prep_def_merge                        true
% 2.34/0.99  --prep_def_merge_prop_impl              false
% 2.34/0.99  --prep_def_merge_mbd                    true
% 2.34/0.99  --prep_def_merge_tr_red                 false
% 2.34/0.99  --prep_def_merge_tr_cl                  false
% 2.34/0.99  --smt_preprocessing                     true
% 2.34/0.99  --smt_ac_axioms                         fast
% 2.34/0.99  --preprocessed_out                      false
% 2.34/0.99  --preprocessed_stats                    false
% 2.34/0.99  
% 2.34/0.99  ------ Abstraction refinement Options
% 2.34/0.99  
% 2.34/0.99  --abstr_ref                             []
% 2.34/0.99  --abstr_ref_prep                        false
% 2.34/0.99  --abstr_ref_until_sat                   false
% 2.34/0.99  --abstr_ref_sig_restrict                funpre
% 2.34/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.99  --abstr_ref_under                       []
% 2.34/0.99  
% 2.34/0.99  ------ SAT Options
% 2.34/0.99  
% 2.34/0.99  --sat_mode                              false
% 2.34/0.99  --sat_fm_restart_options                ""
% 2.34/0.99  --sat_gr_def                            false
% 2.34/0.99  --sat_epr_types                         true
% 2.34/0.99  --sat_non_cyclic_types                  false
% 2.34/0.99  --sat_finite_models                     false
% 2.34/0.99  --sat_fm_lemmas                         false
% 2.34/0.99  --sat_fm_prep                           false
% 2.34/0.99  --sat_fm_uc_incr                        true
% 2.34/0.99  --sat_out_model                         small
% 2.34/0.99  --sat_out_clauses                       false
% 2.34/0.99  
% 2.34/0.99  ------ QBF Options
% 2.34/0.99  
% 2.34/0.99  --qbf_mode                              false
% 2.34/0.99  --qbf_elim_univ                         false
% 2.34/0.99  --qbf_dom_inst                          none
% 2.34/0.99  --qbf_dom_pre_inst                      false
% 2.34/0.99  --qbf_sk_in                             false
% 2.34/0.99  --qbf_pred_elim                         true
% 2.34/0.99  --qbf_split                             512
% 2.34/0.99  
% 2.34/0.99  ------ BMC1 Options
% 2.34/0.99  
% 2.34/0.99  --bmc1_incremental                      false
% 2.34/0.99  --bmc1_axioms                           reachable_all
% 2.34/0.99  --bmc1_min_bound                        0
% 2.34/0.99  --bmc1_max_bound                        -1
% 2.34/0.99  --bmc1_max_bound_default                -1
% 2.34/0.99  --bmc1_symbol_reachability              true
% 2.34/0.99  --bmc1_property_lemmas                  false
% 2.34/0.99  --bmc1_k_induction                      false
% 2.34/0.99  --bmc1_non_equiv_states                 false
% 2.34/0.99  --bmc1_deadlock                         false
% 2.34/0.99  --bmc1_ucm                              false
% 2.34/0.99  --bmc1_add_unsat_core                   none
% 2.34/0.99  --bmc1_unsat_core_children              false
% 2.34/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.99  --bmc1_out_stat                         full
% 2.34/0.99  --bmc1_ground_init                      false
% 2.34/0.99  --bmc1_pre_inst_next_state              false
% 2.34/0.99  --bmc1_pre_inst_state                   false
% 2.34/0.99  --bmc1_pre_inst_reach_state             false
% 2.34/0.99  --bmc1_out_unsat_core                   false
% 2.34/0.99  --bmc1_aig_witness_out                  false
% 2.34/0.99  --bmc1_verbose                          false
% 2.34/0.99  --bmc1_dump_clauses_tptp                false
% 2.34/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.99  --bmc1_dump_file                        -
% 2.34/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.99  --bmc1_ucm_extend_mode                  1
% 2.34/0.99  --bmc1_ucm_init_mode                    2
% 2.34/0.99  --bmc1_ucm_cone_mode                    none
% 2.34/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.99  --bmc1_ucm_relax_model                  4
% 2.34/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.99  --bmc1_ucm_layered_model                none
% 2.34/0.99  --bmc1_ucm_max_lemma_size               10
% 2.34/0.99  
% 2.34/0.99  ------ AIG Options
% 2.34/0.99  
% 2.34/0.99  --aig_mode                              false
% 2.34/0.99  
% 2.34/0.99  ------ Instantiation Options
% 2.34/0.99  
% 2.34/0.99  --instantiation_flag                    true
% 2.34/0.99  --inst_sos_flag                         false
% 2.34/0.99  --inst_sos_phase                        true
% 2.34/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel_side                     none
% 2.34/0.99  --inst_solver_per_active                1400
% 2.34/0.99  --inst_solver_calls_frac                1.
% 2.34/0.99  --inst_passive_queue_type               priority_queues
% 2.34/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.99  --inst_passive_queues_freq              [25;2]
% 2.34/0.99  --inst_dismatching                      true
% 2.34/0.99  --inst_eager_unprocessed_to_passive     true
% 2.34/0.99  --inst_prop_sim_given                   true
% 2.34/0.99  --inst_prop_sim_new                     false
% 2.34/0.99  --inst_subs_new                         false
% 2.34/0.99  --inst_eq_res_simp                      false
% 2.34/0.99  --inst_subs_given                       false
% 2.34/0.99  --inst_orphan_elimination               true
% 2.34/0.99  --inst_learning_loop_flag               true
% 2.34/0.99  --inst_learning_start                   3000
% 2.34/0.99  --inst_learning_factor                  2
% 2.34/0.99  --inst_start_prop_sim_after_learn       3
% 2.34/0.99  --inst_sel_renew                        solver
% 2.34/0.99  --inst_lit_activity_flag                true
% 2.34/0.99  --inst_restr_to_given                   false
% 2.34/0.99  --inst_activity_threshold               500
% 2.34/0.99  --inst_out_proof                        true
% 2.34/0.99  
% 2.34/0.99  ------ Resolution Options
% 2.34/0.99  
% 2.34/0.99  --resolution_flag                       false
% 2.34/0.99  --res_lit_sel                           adaptive
% 2.34/0.99  --res_lit_sel_side                      none
% 2.34/0.99  --res_ordering                          kbo
% 2.34/0.99  --res_to_prop_solver                    active
% 2.34/0.99  --res_prop_simpl_new                    false
% 2.34/0.99  --res_prop_simpl_given                  true
% 2.34/0.99  --res_passive_queue_type                priority_queues
% 2.34/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.99  --res_passive_queues_freq               [15;5]
% 2.34/0.99  --res_forward_subs                      full
% 2.34/0.99  --res_backward_subs                     full
% 2.34/0.99  --res_forward_subs_resolution           true
% 2.34/0.99  --res_backward_subs_resolution          true
% 2.34/0.99  --res_orphan_elimination                true
% 2.34/0.99  --res_time_limit                        2.
% 2.34/0.99  --res_out_proof                         true
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Options
% 2.34/0.99  
% 2.34/0.99  --superposition_flag                    true
% 2.34/0.99  --sup_passive_queue_type                priority_queues
% 2.34/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.99  --demod_completeness_check              fast
% 2.34/0.99  --demod_use_ground                      true
% 2.34/0.99  --sup_to_prop_solver                    passive
% 2.34/0.99  --sup_prop_simpl_new                    true
% 2.34/0.99  --sup_prop_simpl_given                  true
% 2.34/0.99  --sup_fun_splitting                     false
% 2.34/0.99  --sup_smt_interval                      50000
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Simplification Setup
% 2.34/0.99  
% 2.34/0.99  --sup_indices_passive                   []
% 2.34/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_full_bw                           [BwDemod]
% 2.34/0.99  --sup_immed_triv                        [TrivRules]
% 2.34/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_immed_bw_main                     []
% 2.34/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  
% 2.34/0.99  ------ Combination Options
% 2.34/0.99  
% 2.34/0.99  --comb_res_mult                         3
% 2.34/0.99  --comb_sup_mult                         2
% 2.34/0.99  --comb_inst_mult                        10
% 2.34/0.99  
% 2.34/0.99  ------ Debug Options
% 2.34/0.99  
% 2.34/0.99  --dbg_backtrace                         false
% 2.34/0.99  --dbg_dump_prop_clauses                 false
% 2.34/0.99  --dbg_dump_prop_clauses_file            -
% 2.34/0.99  --dbg_out_stat                          false
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  ------ Proving...
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  % SZS status Theorem for theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  fof(f14,conjecture,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f15,negated_conjecture,(
% 2.34/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 2.34/0.99    inference(negated_conjecture,[],[f14])).
% 2.34/0.99  
% 2.34/0.99  fof(f32,plain,(
% 2.34/0.99    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.99    inference(ennf_transformation,[],[f15])).
% 2.34/0.99  
% 2.34/0.99  fof(f33,plain,(
% 2.34/0.99    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f34,plain,(
% 2.34/0.99    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f33])).
% 2.34/0.99  
% 2.34/0.99  fof(f48,plain,(
% 2.34/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.34/0.99    inference(cnf_transformation,[],[f34])).
% 2.34/0.99  
% 2.34/0.99  fof(f12,axiom,(
% 2.34/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f17,plain,(
% 2.34/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.34/0.99    inference(pure_predicate_removal,[],[f12])).
% 2.34/0.99  
% 2.34/0.99  fof(f46,plain,(
% 2.34/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f17])).
% 2.34/0.99  
% 2.34/0.99  fof(f10,axiom,(
% 2.34/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f28,plain,(
% 2.34/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.34/0.99    inference(ennf_transformation,[],[f10])).
% 2.34/0.99  
% 2.34/0.99  fof(f29,plain,(
% 2.34/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.99    inference(flattening,[],[f28])).
% 2.34/0.99  
% 2.34/0.99  fof(f44,plain,(
% 2.34/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f29])).
% 2.34/0.99  
% 2.34/0.99  fof(f8,axiom,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f26,plain,(
% 2.34/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.99    inference(ennf_transformation,[],[f8])).
% 2.34/0.99  
% 2.34/0.99  fof(f42,plain,(
% 2.34/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f26])).
% 2.34/0.99  
% 2.34/0.99  fof(f6,axiom,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f24,plain,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.99    inference(ennf_transformation,[],[f6])).
% 2.34/0.99  
% 2.34/0.99  fof(f40,plain,(
% 2.34/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f24])).
% 2.34/0.99  
% 2.34/0.99  fof(f1,axiom,(
% 2.34/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f16,plain,(
% 2.34/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.34/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.34/0.99  
% 2.34/0.99  fof(f18,plain,(
% 2.34/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.34/0.99    inference(ennf_transformation,[],[f16])).
% 2.34/0.99  
% 2.34/0.99  fof(f35,plain,(
% 2.34/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f18])).
% 2.34/0.99  
% 2.34/0.99  fof(f4,axiom,(
% 2.34/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f20,plain,(
% 2.34/0.99    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.34/0.99    inference(ennf_transformation,[],[f4])).
% 2.34/0.99  
% 2.34/0.99  fof(f21,plain,(
% 2.34/0.99    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.34/0.99    inference(flattening,[],[f20])).
% 2.34/0.99  
% 2.34/0.99  fof(f38,plain,(
% 2.34/0.99    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f21])).
% 2.34/0.99  
% 2.34/0.99  fof(f13,axiom,(
% 2.34/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f47,plain,(
% 2.34/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f13])).
% 2.34/0.99  
% 2.34/0.99  fof(f50,plain,(
% 2.34/0.99    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.34/0.99    inference(definition_unfolding,[],[f38,f47])).
% 2.34/0.99  
% 2.34/0.99  fof(f2,axiom,(
% 2.34/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f19,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.34/0.99    inference(ennf_transformation,[],[f2])).
% 2.34/0.99  
% 2.34/0.99  fof(f36,plain,(
% 2.34/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f19])).
% 2.34/0.99  
% 2.34/0.99  fof(f3,axiom,(
% 2.34/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f37,plain,(
% 2.34/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f3])).
% 2.34/0.99  
% 2.34/0.99  fof(f49,plain,(
% 2.34/0.99    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 2.34/0.99    inference(cnf_transformation,[],[f34])).
% 2.34/0.99  
% 2.34/0.99  fof(f11,axiom,(
% 2.34/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f30,plain,(
% 2.34/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.34/0.99    inference(ennf_transformation,[],[f11])).
% 2.34/0.99  
% 2.34/0.99  fof(f31,plain,(
% 2.34/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.99    inference(flattening,[],[f30])).
% 2.34/0.99  
% 2.34/0.99  fof(f45,plain,(
% 2.34/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f9,axiom,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f27,plain,(
% 2.34/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.99    inference(ennf_transformation,[],[f9])).
% 2.34/0.99  
% 2.34/0.99  fof(f43,plain,(
% 2.34/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f27])).
% 2.34/0.99  
% 2.34/0.99  fof(f7,axiom,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f25,plain,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.99    inference(ennf_transformation,[],[f7])).
% 2.34/0.99  
% 2.34/0.99  fof(f41,plain,(
% 2.34/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f25])).
% 2.34/0.99  
% 2.34/0.99  fof(f5,axiom,(
% 2.34/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.34/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f22,plain,(
% 2.34/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.34/0.99    inference(ennf_transformation,[],[f5])).
% 2.34/0.99  
% 2.34/0.99  fof(f23,plain,(
% 2.34/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.34/0.99    inference(flattening,[],[f22])).
% 2.34/0.99  
% 2.34/0.99  fof(f39,plain,(
% 2.34/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f23])).
% 2.34/0.99  
% 2.34/0.99  fof(f51,plain,(
% 2.34/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.34/0.99    inference(definition_unfolding,[],[f39,f47])).
% 2.34/0.99  
% 2.34/0.99  cnf(c_13,negated_conjecture,
% 2.34/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.34/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_300,negated_conjecture,
% 2.34/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_585,plain,
% 2.34/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_11,plain,
% 2.34/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.34/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_302,plain,
% 2.34/0.99      ( m1_subset_1(k6_partfun1(X0_44),k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_44))) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_583,plain,
% 2.34/0.99      ( m1_subset_1(k6_partfun1(X0_44),k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_44))) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_9,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.34/0.99      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_304,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.34/0.99      | ~ m1_subset_1(X3_44,k1_zfmisc_1(k2_zfmisc_1(X4_44,X5_44)))
% 2.34/0.99      | k4_relset_1(X4_44,X5_44,X1_44,X2_44,X3_44,X0_44) = k5_relat_1(X3_44,X0_44) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_581,plain,
% 2.34/0.99      ( k4_relset_1(X0_44,X1_44,X2_44,X3_44,X4_44,X5_44) = k5_relat_1(X4_44,X5_44)
% 2.34/0.99      | m1_subset_1(X5_44,k1_zfmisc_1(k2_zfmisc_1(X2_44,X3_44))) != iProver_top
% 2.34/0.99      | m1_subset_1(X4_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1160,plain,
% 2.34/0.99      ( k4_relset_1(X0_44,X1_44,X2_44,X2_44,X3_44,k6_partfun1(X2_44)) = k5_relat_1(X3_44,k6_partfun1(X2_44))
% 2.34/0.99      | m1_subset_1(X3_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_583,c_581]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_4962,plain,
% 2.34/0.99      ( k4_relset_1(sK0,sK1,X0_44,X0_44,sK2,k6_partfun1(X0_44)) = k5_relat_1(sK2,k6_partfun1(X0_44)) ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_585,c_1160]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_306,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.34/0.99      | k1_relset_1(X1_44,X2_44,X0_44) = k1_relat_1(X0_44) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_579,plain,
% 2.34/0.99      ( k1_relset_1(X0_44,X1_44,X2_44) = k1_relat_1(X2_44)
% 2.34/0.99      | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_785,plain,
% 2.34/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_585,c_579]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_5,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.34/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_308,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.34/0.99      | m1_subset_1(k1_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_577,plain,
% 2.34/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
% 2.34/0.99      | m1_subset_1(k1_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_965,plain,
% 2.34/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_785,c_577]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_14,plain,
% 2.34/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1513,plain,
% 2.34/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_965,c_14]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_0,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.34/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3,plain,
% 2.34/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.34/0.99      | ~ v1_relat_1(X0)
% 2.34/0.99      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 2.34/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_166,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.34/0.99      | ~ v1_relat_1(X2)
% 2.34/0.99      | X3 != X1
% 2.34/0.99      | k5_relat_1(k6_partfun1(X3),X2) = X2
% 2.34/0.99      | k1_relat_1(X2) != X0 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_167,plain,
% 2.34/0.99      ( ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
% 2.34/0.99      | ~ v1_relat_1(X0)
% 2.34/0.99      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_166]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_299,plain,
% 2.34/0.99      ( ~ m1_subset_1(k1_relat_1(X0_44),k1_zfmisc_1(X1_44))
% 2.34/0.99      | ~ v1_relat_1(X0_44)
% 2.34/0.99      | k5_relat_1(k6_partfun1(X1_44),X0_44) = X0_44 ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_167]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_586,plain,
% 2.34/0.99      ( k5_relat_1(k6_partfun1(X0_44),X1_44) = X1_44
% 2.34/0.99      | m1_subset_1(k1_relat_1(X1_44),k1_zfmisc_1(X0_44)) != iProver_top
% 2.34/0.99      | v1_relat_1(X1_44) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1524,plain,
% 2.34/0.99      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2
% 2.34/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_1513,c_586]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.34/0.99      | ~ v1_relat_1(X1)
% 2.34/0.99      | v1_relat_1(X0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_310,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 2.34/0.99      | ~ v1_relat_1(X1_44)
% 2.34/0.99      | v1_relat_1(X0_44) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_673,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.34/0.99      | v1_relat_1(X0_44)
% 2.34/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1_44,X2_44)) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_310]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_764,plain,
% 2.34/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.34/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.34/0.99      | v1_relat_1(sK2) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_673]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2,plain,
% 2.34/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.34/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_309,plain,
% 2.34/0.99      ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_812,plain,
% 2.34/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_309]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_992,plain,
% 2.34/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.34/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_965]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1035,plain,
% 2.34/0.99      ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_44))
% 2.34/0.99      | ~ v1_relat_1(sK2)
% 2.34/0.99      | k5_relat_1(k6_partfun1(X0_44),sK2) = sK2 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_299]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1042,plain,
% 2.34/0.99      ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
% 2.34/0.99      | ~ v1_relat_1(sK2)
% 2.34/0.99      | k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_1035]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1865,plain,
% 2.34/0.99      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_1524,c_13,c_764,c_812,c_992,c_1042]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1159,plain,
% 2.34/0.99      ( k4_relset_1(X0_44,X1_44,sK0,sK1,X2_44,sK2) = k5_relat_1(X2_44,sK2)
% 2.34/0.99      | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_585,c_581]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1369,plain,
% 2.34/0.99      ( k4_relset_1(X0_44,X0_44,sK0,sK1,k6_partfun1(X0_44),sK2) = k5_relat_1(k6_partfun1(X0_44),sK2) ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_583,c_1159]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_12,negated_conjecture,
% 2.34/0.99      ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
% 2.34/0.99      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
% 2.34/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_301,negated_conjecture,
% 2.34/0.99      ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
% 2.34/0.99      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_584,plain,
% 2.34/0.99      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
% 2.34/0.99      | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1434,plain,
% 2.34/0.99      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
% 2.34/0.99      | r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) != iProver_top ),
% 2.34/0.99      inference(demodulation,[status(thm)],[c_1369,c_584]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1868,plain,
% 2.34/0.99      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
% 2.34/0.99      | r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
% 2.34/0.99      inference(demodulation,[status(thm)],[c_1865,c_1434]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_10,plain,
% 2.34/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.34/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_303,plain,
% 2.34/0.99      ( r2_relset_1(X0_44,X1_44,X2_44,X2_44)
% 2.34/0.99      | ~ m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)))
% 2.34/0.99      | ~ m1_subset_1(X3_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_735,plain,
% 2.34/0.99      ( r2_relset_1(sK0,sK1,sK2,sK2)
% 2.34/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_303]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_869,plain,
% 2.34/0.99      ( r2_relset_1(sK0,sK1,sK2,sK2)
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_735]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_870,plain,
% 2.34/0.99      ( r2_relset_1(sK0,sK1,sK2,sK2) = iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_869]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1983,plain,
% 2.34/0.99      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_1868,c_14,c_870]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_4995,plain,
% 2.34/0.99      ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) != iProver_top ),
% 2.34/0.99      inference(demodulation,[status(thm)],[c_4962,c_1983]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_8,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_305,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.34/0.99      | k2_relset_1(X1_44,X2_44,X0_44) = k2_relat_1(X0_44) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_580,plain,
% 2.34/0.99      ( k2_relset_1(X0_44,X1_44,X2_44) = k2_relat_1(X2_44)
% 2.34/0.99      | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_862,plain,
% 2.34/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_585,c_580]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.34/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_307,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.34/0.99      | m1_subset_1(k2_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X2_44)) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_578,plain,
% 2.34/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
% 2.34/0.99      | m1_subset_1(k2_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X2_44)) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1196,plain,
% 2.34/0.99      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_862,c_578]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1650,plain,
% 2.34/0.99      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_1196,c_14]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_4,plain,
% 2.34/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.34/0.99      | ~ v1_relat_1(X0)
% 2.34/0.99      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 2.34/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_181,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.34/0.99      | ~ v1_relat_1(X2)
% 2.34/0.99      | X3 != X1
% 2.34/0.99      | k5_relat_1(X2,k6_partfun1(X3)) = X2
% 2.34/0.99      | k2_relat_1(X2) != X0 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_182,plain,
% 2.34/0.99      ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
% 2.34/0.99      | ~ v1_relat_1(X0)
% 2.34/0.99      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_181]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_298,plain,
% 2.34/0.99      ( ~ m1_subset_1(k2_relat_1(X0_44),k1_zfmisc_1(X1_44))
% 2.34/0.99      | ~ v1_relat_1(X0_44)
% 2.34/0.99      | k5_relat_1(X0_44,k6_partfun1(X1_44)) = X0_44 ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_182]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_587,plain,
% 2.34/0.99      ( k5_relat_1(X0_44,k6_partfun1(X1_44)) = X0_44
% 2.34/0.99      | m1_subset_1(k2_relat_1(X0_44),k1_zfmisc_1(X1_44)) != iProver_top
% 2.34/0.99      | v1_relat_1(X0_44) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2363,plain,
% 2.34/0.99      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2
% 2.34/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_1650,c_587]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_765,plain,
% 2.34/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.34/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.34/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_813,plain,
% 2.34/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2583,plain,
% 2.34/0.99      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_2363,c_14,c_765,c_813]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_4996,plain,
% 2.34/0.99      ( r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
% 2.34/0.99      inference(light_normalisation,[status(thm)],[c_4995,c_2583]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(contradiction,plain,
% 2.34/0.99      ( $false ),
% 2.34/0.99      inference(minisat,[status(thm)],[c_4996,c_870,c_14]) ).
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  ------                               Statistics
% 2.34/0.99  
% 2.34/0.99  ------ General
% 2.34/0.99  
% 2.34/0.99  abstr_ref_over_cycles:                  0
% 2.34/0.99  abstr_ref_under_cycles:                 0
% 2.34/0.99  gc_basic_clause_elim:                   0
% 2.34/0.99  forced_gc_time:                         0
% 2.34/0.99  parsing_time:                           0.01
% 2.34/0.99  unif_index_cands_time:                  0.
% 2.34/0.99  unif_index_add_time:                    0.
% 2.34/0.99  orderings_time:                         0.
% 2.34/0.99  out_proof_time:                         0.007
% 2.34/0.99  total_time:                             0.203
% 2.34/0.99  num_of_symbols:                         49
% 2.34/0.99  num_of_terms:                           9296
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing
% 2.34/0.99  
% 2.34/0.99  num_of_splits:                          0
% 2.34/0.99  num_of_split_atoms:                     0
% 2.34/0.99  num_of_reused_defs:                     0
% 2.34/0.99  num_eq_ax_congr_red:                    25
% 2.34/0.99  num_of_sem_filtered_clauses:            1
% 2.34/0.99  num_of_subtypes:                        2
% 2.34/0.99  monotx_restored_types:                  1
% 2.34/0.99  sat_num_of_epr_types:                   0
% 2.34/0.99  sat_num_of_non_cyclic_types:            0
% 2.34/0.99  sat_guarded_non_collapsed_types:        0
% 2.34/0.99  num_pure_diseq_elim:                    0
% 2.34/0.99  simp_replaced_by:                       0
% 2.34/0.99  res_preprocessed:                       76
% 2.34/0.99  prep_upred:                             0
% 2.34/0.99  prep_unflattend:                        4
% 2.34/0.99  smt_new_axioms:                         0
% 2.34/0.99  pred_elim_cands:                        3
% 2.34/0.99  pred_elim:                              1
% 2.34/0.99  pred_elim_cl:                           1
% 2.34/0.99  pred_elim_cycles:                       3
% 2.34/0.99  merged_defs:                            0
% 2.34/0.99  merged_defs_ncl:                        0
% 2.34/0.99  bin_hyper_res:                          0
% 2.34/0.99  prep_cycles:                            4
% 2.34/0.99  pred_elim_time:                         0.001
% 2.34/0.99  splitting_time:                         0.
% 2.34/0.99  sem_filter_time:                        0.
% 2.34/0.99  monotx_time:                            0.
% 2.34/0.99  subtype_inf_time:                       0.001
% 2.34/0.99  
% 2.34/0.99  ------ Problem properties
% 2.34/0.99  
% 2.34/0.99  clauses:                                13
% 2.34/0.99  conjectures:                            2
% 2.34/0.99  epr:                                    0
% 2.34/0.99  horn:                                   13
% 2.34/0.99  ground:                                 2
% 2.34/0.99  unary:                                  3
% 2.34/0.99  binary:                                 5
% 2.34/0.99  lits:                                   28
% 2.34/0.99  lits_eq:                                5
% 2.34/0.99  fd_pure:                                0
% 2.34/0.99  fd_pseudo:                              0
% 2.34/0.99  fd_cond:                                0
% 2.34/0.99  fd_pseudo_cond:                         0
% 2.34/0.99  ac_symbols:                             0
% 2.34/0.99  
% 2.34/0.99  ------ Propositional Solver
% 2.34/0.99  
% 2.34/0.99  prop_solver_calls:                      30
% 2.34/0.99  prop_fast_solver_calls:                 508
% 2.34/0.99  smt_solver_calls:                       0
% 2.34/0.99  smt_fast_solver_calls:                  0
% 2.34/0.99  prop_num_of_clauses:                    2460
% 2.34/0.99  prop_preprocess_simplified:             5127
% 2.34/0.99  prop_fo_subsumed:                       10
% 2.34/0.99  prop_solver_time:                       0.
% 2.34/0.99  smt_solver_time:                        0.
% 2.34/0.99  smt_fast_solver_time:                   0.
% 2.34/0.99  prop_fast_solver_time:                  0.
% 2.34/0.99  prop_unsat_core_time:                   0.
% 2.34/0.99  
% 2.34/0.99  ------ QBF
% 2.34/0.99  
% 2.34/0.99  qbf_q_res:                              0
% 2.34/0.99  qbf_num_tautologies:                    0
% 2.34/0.99  qbf_prep_cycles:                        0
% 2.34/0.99  
% 2.34/0.99  ------ BMC1
% 2.34/0.99  
% 2.34/0.99  bmc1_current_bound:                     -1
% 2.34/0.99  bmc1_last_solved_bound:                 -1
% 2.34/0.99  bmc1_unsat_core_size:                   -1
% 2.34/0.99  bmc1_unsat_core_parents_size:           -1
% 2.34/0.99  bmc1_merge_next_fun:                    0
% 2.34/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.34/0.99  
% 2.34/0.99  ------ Instantiation
% 2.34/0.99  
% 2.34/0.99  inst_num_of_clauses:                    678
% 2.34/0.99  inst_num_in_passive:                    132
% 2.34/0.99  inst_num_in_active:                     305
% 2.34/0.99  inst_num_in_unprocessed:                241
% 2.34/0.99  inst_num_of_loops:                      330
% 2.34/0.99  inst_num_of_learning_restarts:          0
% 2.34/0.99  inst_num_moves_active_passive:          21
% 2.34/0.99  inst_lit_activity:                      0
% 2.34/0.99  inst_lit_activity_moves:                0
% 2.34/0.99  inst_num_tautologies:                   0
% 2.34/0.99  inst_num_prop_implied:                  0
% 2.34/0.99  inst_num_existing_simplified:           0
% 2.34/0.99  inst_num_eq_res_simplified:             0
% 2.34/0.99  inst_num_child_elim:                    0
% 2.34/0.99  inst_num_of_dismatching_blockings:      184
% 2.34/0.99  inst_num_of_non_proper_insts:           470
% 2.34/0.99  inst_num_of_duplicates:                 0
% 2.34/0.99  inst_inst_num_from_inst_to_res:         0
% 2.34/0.99  inst_dismatching_checking_time:         0.
% 2.34/0.99  
% 2.34/0.99  ------ Resolution
% 2.34/0.99  
% 2.34/0.99  res_num_of_clauses:                     0
% 2.34/0.99  res_num_in_passive:                     0
% 2.34/0.99  res_num_in_active:                      0
% 2.34/0.99  res_num_of_loops:                       80
% 2.34/0.99  res_forward_subset_subsumed:            52
% 2.34/0.99  res_backward_subset_subsumed:           2
% 2.34/0.99  res_forward_subsumed:                   0
% 2.34/0.99  res_backward_subsumed:                  0
% 2.34/0.99  res_forward_subsumption_resolution:     0
% 2.34/0.99  res_backward_subsumption_resolution:    0
% 2.34/0.99  res_clause_to_clause_subsumption:       358
% 2.34/0.99  res_orphan_elimination:                 0
% 2.34/0.99  res_tautology_del:                      52
% 2.34/0.99  res_num_eq_res_simplified:              0
% 2.34/0.99  res_num_sel_changes:                    0
% 2.34/0.99  res_moves_from_active_to_pass:          0
% 2.34/0.99  
% 2.34/0.99  ------ Superposition
% 2.34/0.99  
% 2.34/0.99  sup_time_total:                         0.
% 2.34/0.99  sup_time_generating:                    0.
% 2.34/0.99  sup_time_sim_full:                      0.
% 2.34/0.99  sup_time_sim_immed:                     0.
% 2.34/0.99  
% 2.34/0.99  sup_num_of_clauses:                     140
% 2.34/0.99  sup_num_in_active:                      61
% 2.34/0.99  sup_num_in_passive:                     79
% 2.34/0.99  sup_num_of_loops:                       65
% 2.34/0.99  sup_fw_superposition:                   105
% 2.34/0.99  sup_bw_superposition:                   43
% 2.34/0.99  sup_immediate_simplified:               49
% 2.34/0.99  sup_given_eliminated:                   0
% 2.34/0.99  comparisons_done:                       0
% 2.34/0.99  comparisons_avoided:                    0
% 2.34/0.99  
% 2.34/0.99  ------ Simplifications
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  sim_fw_subset_subsumed:                 0
% 2.34/0.99  sim_bw_subset_subsumed:                 0
% 2.34/0.99  sim_fw_subsumed:                        0
% 2.34/0.99  sim_bw_subsumed:                        0
% 2.34/0.99  sim_fw_subsumption_res:                 1
% 2.34/0.99  sim_bw_subsumption_res:                 0
% 2.34/0.99  sim_tautology_del:                      0
% 2.34/0.99  sim_eq_tautology_del:                   2
% 2.34/0.99  sim_eq_res_simp:                        0
% 2.34/0.99  sim_fw_demodulated:                     33
% 2.34/0.99  sim_bw_demodulated:                     15
% 2.34/0.99  sim_light_normalised:                   7
% 2.34/0.99  sim_joinable_taut:                      0
% 2.34/0.99  sim_joinable_simp:                      0
% 2.34/0.99  sim_ac_normalised:                      0
% 2.34/0.99  sim_smt_subsumption:                    0
% 2.34/0.99  
%------------------------------------------------------------------------------
