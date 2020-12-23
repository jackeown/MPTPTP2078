%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:14 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 426 expanded)
%              Number of clauses        :   78 ( 181 expanded)
%              Number of leaves         :   18 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  291 (1033 expanded)
%              Number of equality atoms :  154 ( 485 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_692,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_705,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1223,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_705])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_883,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1227,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_1228,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_825,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1296,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_1319,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1371,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1372,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_882,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1376,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_1377,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1376])).

cnf(c_1384,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1223,c_22,c_1228,c_1319,c_1372,c_1377])).

cnf(c_706,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_700,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2487,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_700])).

cnf(c_3902,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_1384,c_2487])).

cnf(c_4,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_704,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_701,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2637,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_701])).

cnf(c_2722,plain,
    ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_704,c_2637])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2730,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2722,c_10])).

cnf(c_4298,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3902,c_2730])).

cnf(c_695,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1440,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_695])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_8])).

cnf(c_691,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_2094,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_691])).

cnf(c_2918,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_22,c_1228,c_1319,c_1372,c_1377])).

cnf(c_2919,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2918])).

cnf(c_2926,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_706,c_2919])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_702,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1389,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1384,c_702])).

cnf(c_3105,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2926,c_1389])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_696,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1530,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_692,c_696])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_699,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1102,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_692,c_699])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_698,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1026,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_692,c_698])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1226,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1026,c_20])).

cnf(c_1346,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1102,c_1226])).

cnf(c_1764,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1530,c_1346])).

cnf(c_1765,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1764,c_1530])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_693,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1625,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
    inference(superposition,[status(thm)],[c_692,c_693])).

cnf(c_1626,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1625,c_1026])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_694,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1630,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
    inference(superposition,[status(thm)],[c_692,c_694])).

cnf(c_1631,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1630,c_1102])).

cnf(c_2302,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1530,c_1631])).

cnf(c_2986,plain,
    ( k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1765,c_1626,c_2302])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_697,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1535,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_692,c_697])).

cnf(c_2987,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2986,c_1535])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4298,c_3105,c_2987])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:34:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.69/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/1.00  
% 2.69/1.00  ------  iProver source info
% 2.69/1.00  
% 2.69/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.69/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/1.00  git: non_committed_changes: false
% 2.69/1.00  git: last_make_outside_of_git: false
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options
% 2.69/1.00  
% 2.69/1.00  --out_options                           all
% 2.69/1.00  --tptp_safe_out                         true
% 2.69/1.00  --problem_path                          ""
% 2.69/1.00  --include_path                          ""
% 2.69/1.00  --clausifier                            res/vclausify_rel
% 2.69/1.00  --clausifier_options                    --mode clausify
% 2.69/1.00  --stdin                                 false
% 2.69/1.00  --stats_out                             all
% 2.69/1.00  
% 2.69/1.00  ------ General Options
% 2.69/1.00  
% 2.69/1.00  --fof                                   false
% 2.69/1.00  --time_out_real                         305.
% 2.69/1.00  --time_out_virtual                      -1.
% 2.69/1.00  --symbol_type_check                     false
% 2.69/1.00  --clausify_out                          false
% 2.69/1.00  --sig_cnt_out                           false
% 2.69/1.00  --trig_cnt_out                          false
% 2.69/1.00  --trig_cnt_out_tolerance                1.
% 2.69/1.00  --trig_cnt_out_sk_spl                   false
% 2.69/1.00  --abstr_cl_out                          false
% 2.69/1.00  
% 2.69/1.00  ------ Global Options
% 2.69/1.00  
% 2.69/1.00  --schedule                              default
% 2.69/1.00  --add_important_lit                     false
% 2.69/1.00  --prop_solver_per_cl                    1000
% 2.69/1.00  --min_unsat_core                        false
% 2.69/1.00  --soft_assumptions                      false
% 2.69/1.00  --soft_lemma_size                       3
% 2.69/1.00  --prop_impl_unit_size                   0
% 2.69/1.00  --prop_impl_unit                        []
% 2.69/1.00  --share_sel_clauses                     true
% 2.69/1.00  --reset_solvers                         false
% 2.69/1.00  --bc_imp_inh                            [conj_cone]
% 2.69/1.00  --conj_cone_tolerance                   3.
% 2.69/1.00  --extra_neg_conj                        none
% 2.69/1.00  --large_theory_mode                     true
% 2.69/1.00  --prolific_symb_bound                   200
% 2.69/1.00  --lt_threshold                          2000
% 2.69/1.00  --clause_weak_htbl                      true
% 2.69/1.00  --gc_record_bc_elim                     false
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing Options
% 2.69/1.00  
% 2.69/1.00  --preprocessing_flag                    true
% 2.69/1.00  --time_out_prep_mult                    0.1
% 2.69/1.00  --splitting_mode                        input
% 2.69/1.00  --splitting_grd                         true
% 2.69/1.00  --splitting_cvd                         false
% 2.69/1.00  --splitting_cvd_svl                     false
% 2.69/1.00  --splitting_nvd                         32
% 2.69/1.00  --sub_typing                            true
% 2.69/1.00  --prep_gs_sim                           true
% 2.69/1.00  --prep_unflatten                        true
% 2.69/1.00  --prep_res_sim                          true
% 2.69/1.00  --prep_upred                            true
% 2.69/1.00  --prep_sem_filter                       exhaustive
% 2.69/1.00  --prep_sem_filter_out                   false
% 2.69/1.00  --pred_elim                             true
% 2.69/1.00  --res_sim_input                         true
% 2.69/1.00  --eq_ax_congr_red                       true
% 2.69/1.00  --pure_diseq_elim                       true
% 2.69/1.00  --brand_transform                       false
% 2.69/1.00  --non_eq_to_eq                          false
% 2.69/1.00  --prep_def_merge                        true
% 2.69/1.00  --prep_def_merge_prop_impl              false
% 2.69/1.00  --prep_def_merge_mbd                    true
% 2.69/1.00  --prep_def_merge_tr_red                 false
% 2.69/1.00  --prep_def_merge_tr_cl                  false
% 2.69/1.00  --smt_preprocessing                     true
% 2.69/1.00  --smt_ac_axioms                         fast
% 2.69/1.00  --preprocessed_out                      false
% 2.69/1.00  --preprocessed_stats                    false
% 2.69/1.00  
% 2.69/1.00  ------ Abstraction refinement Options
% 2.69/1.00  
% 2.69/1.00  --abstr_ref                             []
% 2.69/1.00  --abstr_ref_prep                        false
% 2.69/1.00  --abstr_ref_until_sat                   false
% 2.69/1.00  --abstr_ref_sig_restrict                funpre
% 2.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.00  --abstr_ref_under                       []
% 2.69/1.00  
% 2.69/1.00  ------ SAT Options
% 2.69/1.00  
% 2.69/1.00  --sat_mode                              false
% 2.69/1.00  --sat_fm_restart_options                ""
% 2.69/1.00  --sat_gr_def                            false
% 2.69/1.00  --sat_epr_types                         true
% 2.69/1.00  --sat_non_cyclic_types                  false
% 2.69/1.00  --sat_finite_models                     false
% 2.69/1.00  --sat_fm_lemmas                         false
% 2.69/1.00  --sat_fm_prep                           false
% 2.69/1.00  --sat_fm_uc_incr                        true
% 2.69/1.00  --sat_out_model                         small
% 2.69/1.00  --sat_out_clauses                       false
% 2.69/1.00  
% 2.69/1.00  ------ QBF Options
% 2.69/1.00  
% 2.69/1.00  --qbf_mode                              false
% 2.69/1.00  --qbf_elim_univ                         false
% 2.69/1.00  --qbf_dom_inst                          none
% 2.69/1.00  --qbf_dom_pre_inst                      false
% 2.69/1.00  --qbf_sk_in                             false
% 2.69/1.00  --qbf_pred_elim                         true
% 2.69/1.00  --qbf_split                             512
% 2.69/1.00  
% 2.69/1.00  ------ BMC1 Options
% 2.69/1.00  
% 2.69/1.00  --bmc1_incremental                      false
% 2.69/1.00  --bmc1_axioms                           reachable_all
% 2.69/1.00  --bmc1_min_bound                        0
% 2.69/1.00  --bmc1_max_bound                        -1
% 2.69/1.00  --bmc1_max_bound_default                -1
% 2.69/1.00  --bmc1_symbol_reachability              true
% 2.69/1.00  --bmc1_property_lemmas                  false
% 2.69/1.00  --bmc1_k_induction                      false
% 2.69/1.00  --bmc1_non_equiv_states                 false
% 2.69/1.00  --bmc1_deadlock                         false
% 2.69/1.00  --bmc1_ucm                              false
% 2.69/1.00  --bmc1_add_unsat_core                   none
% 2.69/1.00  --bmc1_unsat_core_children              false
% 2.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.00  --bmc1_out_stat                         full
% 2.69/1.00  --bmc1_ground_init                      false
% 2.69/1.00  --bmc1_pre_inst_next_state              false
% 2.69/1.00  --bmc1_pre_inst_state                   false
% 2.69/1.00  --bmc1_pre_inst_reach_state             false
% 2.69/1.00  --bmc1_out_unsat_core                   false
% 2.69/1.00  --bmc1_aig_witness_out                  false
% 2.69/1.00  --bmc1_verbose                          false
% 2.69/1.00  --bmc1_dump_clauses_tptp                false
% 2.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.00  --bmc1_dump_file                        -
% 2.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.00  --bmc1_ucm_extend_mode                  1
% 2.69/1.00  --bmc1_ucm_init_mode                    2
% 2.69/1.00  --bmc1_ucm_cone_mode                    none
% 2.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.00  --bmc1_ucm_relax_model                  4
% 2.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.00  --bmc1_ucm_layered_model                none
% 2.69/1.00  --bmc1_ucm_max_lemma_size               10
% 2.69/1.00  
% 2.69/1.00  ------ AIG Options
% 2.69/1.00  
% 2.69/1.00  --aig_mode                              false
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation Options
% 2.69/1.00  
% 2.69/1.00  --instantiation_flag                    true
% 2.69/1.00  --inst_sos_flag                         false
% 2.69/1.00  --inst_sos_phase                        true
% 2.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel_side                     num_symb
% 2.69/1.00  --inst_solver_per_active                1400
% 2.69/1.00  --inst_solver_calls_frac                1.
% 2.69/1.00  --inst_passive_queue_type               priority_queues
% 2.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.00  --inst_passive_queues_freq              [25;2]
% 2.69/1.00  --inst_dismatching                      true
% 2.69/1.00  --inst_eager_unprocessed_to_passive     true
% 2.69/1.00  --inst_prop_sim_given                   true
% 2.69/1.00  --inst_prop_sim_new                     false
% 2.69/1.00  --inst_subs_new                         false
% 2.69/1.00  --inst_eq_res_simp                      false
% 2.69/1.00  --inst_subs_given                       false
% 2.69/1.00  --inst_orphan_elimination               true
% 2.69/1.00  --inst_learning_loop_flag               true
% 2.69/1.00  --inst_learning_start                   3000
% 2.69/1.00  --inst_learning_factor                  2
% 2.69/1.00  --inst_start_prop_sim_after_learn       3
% 2.69/1.00  --inst_sel_renew                        solver
% 2.69/1.00  --inst_lit_activity_flag                true
% 2.69/1.00  --inst_restr_to_given                   false
% 2.69/1.00  --inst_activity_threshold               500
% 2.69/1.00  --inst_out_proof                        true
% 2.69/1.00  
% 2.69/1.00  ------ Resolution Options
% 2.69/1.00  
% 2.69/1.00  --resolution_flag                       true
% 2.69/1.00  --res_lit_sel                           adaptive
% 2.69/1.00  --res_lit_sel_side                      none
% 2.69/1.00  --res_ordering                          kbo
% 2.69/1.00  --res_to_prop_solver                    active
% 2.69/1.00  --res_prop_simpl_new                    false
% 2.69/1.00  --res_prop_simpl_given                  true
% 2.69/1.00  --res_passive_queue_type                priority_queues
% 2.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.00  --res_passive_queues_freq               [15;5]
% 2.69/1.00  --res_forward_subs                      full
% 2.69/1.00  --res_backward_subs                     full
% 2.69/1.00  --res_forward_subs_resolution           true
% 2.69/1.00  --res_backward_subs_resolution          true
% 2.69/1.00  --res_orphan_elimination                true
% 2.69/1.00  --res_time_limit                        2.
% 2.69/1.00  --res_out_proof                         true
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Options
% 2.69/1.00  
% 2.69/1.00  --superposition_flag                    true
% 2.69/1.00  --sup_passive_queue_type                priority_queues
% 2.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.00  --demod_completeness_check              fast
% 2.69/1.00  --demod_use_ground                      true
% 2.69/1.00  --sup_to_prop_solver                    passive
% 2.69/1.00  --sup_prop_simpl_new                    true
% 2.69/1.00  --sup_prop_simpl_given                  true
% 2.69/1.00  --sup_fun_splitting                     false
% 2.69/1.00  --sup_smt_interval                      50000
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Simplification Setup
% 2.69/1.00  
% 2.69/1.00  --sup_indices_passive                   []
% 2.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_full_bw                           [BwDemod]
% 2.69/1.00  --sup_immed_triv                        [TrivRules]
% 2.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_immed_bw_main                     []
% 2.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  
% 2.69/1.00  ------ Combination Options
% 2.69/1.00  
% 2.69/1.00  --comb_res_mult                         3
% 2.69/1.00  --comb_sup_mult                         2
% 2.69/1.00  --comb_inst_mult                        10
% 2.69/1.00  
% 2.69/1.00  ------ Debug Options
% 2.69/1.00  
% 2.69/1.00  --dbg_backtrace                         false
% 2.69/1.00  --dbg_dump_prop_clauses                 false
% 2.69/1.00  --dbg_dump_prop_clauses_file            -
% 2.69/1.00  --dbg_out_stat                          false
% 2.69/1.00  ------ Parsing...
% 2.69/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/1.00  ------ Proving...
% 2.69/1.00  ------ Problem Properties 
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  clauses                                 20
% 2.69/1.00  conjectures                             2
% 2.69/1.00  EPR                                     2
% 2.69/1.00  Horn                                    20
% 2.69/1.00  unary                                   6
% 2.69/1.00  binary                                  8
% 2.69/1.00  lits                                    40
% 2.69/1.00  lits eq                                 15
% 2.69/1.00  fd_pure                                 0
% 2.69/1.00  fd_pseudo                               0
% 2.69/1.00  fd_cond                                 0
% 2.69/1.00  fd_pseudo_cond                          1
% 2.69/1.00  AC symbols                              0
% 2.69/1.00  
% 2.69/1.00  ------ Schedule dynamic 5 is on 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  Current options:
% 2.69/1.00  ------ 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options
% 2.69/1.00  
% 2.69/1.00  --out_options                           all
% 2.69/1.00  --tptp_safe_out                         true
% 2.69/1.00  --problem_path                          ""
% 2.69/1.00  --include_path                          ""
% 2.69/1.00  --clausifier                            res/vclausify_rel
% 2.69/1.00  --clausifier_options                    --mode clausify
% 2.69/1.00  --stdin                                 false
% 2.69/1.00  --stats_out                             all
% 2.69/1.00  
% 2.69/1.00  ------ General Options
% 2.69/1.00  
% 2.69/1.00  --fof                                   false
% 2.69/1.00  --time_out_real                         305.
% 2.69/1.00  --time_out_virtual                      -1.
% 2.69/1.00  --symbol_type_check                     false
% 2.69/1.00  --clausify_out                          false
% 2.69/1.00  --sig_cnt_out                           false
% 2.69/1.00  --trig_cnt_out                          false
% 2.69/1.00  --trig_cnt_out_tolerance                1.
% 2.69/1.00  --trig_cnt_out_sk_spl                   false
% 2.69/1.00  --abstr_cl_out                          false
% 2.69/1.00  
% 2.69/1.00  ------ Global Options
% 2.69/1.00  
% 2.69/1.00  --schedule                              default
% 2.69/1.00  --add_important_lit                     false
% 2.69/1.00  --prop_solver_per_cl                    1000
% 2.69/1.00  --min_unsat_core                        false
% 2.69/1.00  --soft_assumptions                      false
% 2.69/1.00  --soft_lemma_size                       3
% 2.69/1.00  --prop_impl_unit_size                   0
% 2.69/1.00  --prop_impl_unit                        []
% 2.69/1.00  --share_sel_clauses                     true
% 2.69/1.00  --reset_solvers                         false
% 2.69/1.00  --bc_imp_inh                            [conj_cone]
% 2.69/1.00  --conj_cone_tolerance                   3.
% 2.69/1.00  --extra_neg_conj                        none
% 2.69/1.00  --large_theory_mode                     true
% 2.69/1.00  --prolific_symb_bound                   200
% 2.69/1.00  --lt_threshold                          2000
% 2.69/1.00  --clause_weak_htbl                      true
% 2.69/1.00  --gc_record_bc_elim                     false
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing Options
% 2.69/1.00  
% 2.69/1.00  --preprocessing_flag                    true
% 2.69/1.00  --time_out_prep_mult                    0.1
% 2.69/1.00  --splitting_mode                        input
% 2.69/1.00  --splitting_grd                         true
% 2.69/1.00  --splitting_cvd                         false
% 2.69/1.00  --splitting_cvd_svl                     false
% 2.69/1.00  --splitting_nvd                         32
% 2.69/1.00  --sub_typing                            true
% 2.69/1.00  --prep_gs_sim                           true
% 2.69/1.00  --prep_unflatten                        true
% 2.69/1.00  --prep_res_sim                          true
% 2.69/1.00  --prep_upred                            true
% 2.69/1.00  --prep_sem_filter                       exhaustive
% 2.69/1.00  --prep_sem_filter_out                   false
% 2.69/1.00  --pred_elim                             true
% 2.69/1.00  --res_sim_input                         true
% 2.69/1.00  --eq_ax_congr_red                       true
% 2.69/1.00  --pure_diseq_elim                       true
% 2.69/1.00  --brand_transform                       false
% 2.69/1.00  --non_eq_to_eq                          false
% 2.69/1.00  --prep_def_merge                        true
% 2.69/1.00  --prep_def_merge_prop_impl              false
% 2.69/1.00  --prep_def_merge_mbd                    true
% 2.69/1.00  --prep_def_merge_tr_red                 false
% 2.69/1.00  --prep_def_merge_tr_cl                  false
% 2.69/1.00  --smt_preprocessing                     true
% 2.69/1.00  --smt_ac_axioms                         fast
% 2.69/1.00  --preprocessed_out                      false
% 2.69/1.00  --preprocessed_stats                    false
% 2.69/1.00  
% 2.69/1.00  ------ Abstraction refinement Options
% 2.69/1.00  
% 2.69/1.00  --abstr_ref                             []
% 2.69/1.00  --abstr_ref_prep                        false
% 2.69/1.00  --abstr_ref_until_sat                   false
% 2.69/1.00  --abstr_ref_sig_restrict                funpre
% 2.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.00  --abstr_ref_under                       []
% 2.69/1.00  
% 2.69/1.00  ------ SAT Options
% 2.69/1.00  
% 2.69/1.00  --sat_mode                              false
% 2.69/1.00  --sat_fm_restart_options                ""
% 2.69/1.00  --sat_gr_def                            false
% 2.69/1.00  --sat_epr_types                         true
% 2.69/1.00  --sat_non_cyclic_types                  false
% 2.69/1.00  --sat_finite_models                     false
% 2.69/1.00  --sat_fm_lemmas                         false
% 2.69/1.00  --sat_fm_prep                           false
% 2.69/1.00  --sat_fm_uc_incr                        true
% 2.69/1.00  --sat_out_model                         small
% 2.69/1.00  --sat_out_clauses                       false
% 2.69/1.00  
% 2.69/1.00  ------ QBF Options
% 2.69/1.00  
% 2.69/1.00  --qbf_mode                              false
% 2.69/1.00  --qbf_elim_univ                         false
% 2.69/1.00  --qbf_dom_inst                          none
% 2.69/1.00  --qbf_dom_pre_inst                      false
% 2.69/1.00  --qbf_sk_in                             false
% 2.69/1.00  --qbf_pred_elim                         true
% 2.69/1.00  --qbf_split                             512
% 2.69/1.00  
% 2.69/1.00  ------ BMC1 Options
% 2.69/1.00  
% 2.69/1.00  --bmc1_incremental                      false
% 2.69/1.00  --bmc1_axioms                           reachable_all
% 2.69/1.00  --bmc1_min_bound                        0
% 2.69/1.00  --bmc1_max_bound                        -1
% 2.69/1.00  --bmc1_max_bound_default                -1
% 2.69/1.00  --bmc1_symbol_reachability              true
% 2.69/1.00  --bmc1_property_lemmas                  false
% 2.69/1.00  --bmc1_k_induction                      false
% 2.69/1.00  --bmc1_non_equiv_states                 false
% 2.69/1.00  --bmc1_deadlock                         false
% 2.69/1.00  --bmc1_ucm                              false
% 2.69/1.00  --bmc1_add_unsat_core                   none
% 2.69/1.00  --bmc1_unsat_core_children              false
% 2.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.00  --bmc1_out_stat                         full
% 2.69/1.00  --bmc1_ground_init                      false
% 2.69/1.00  --bmc1_pre_inst_next_state              false
% 2.69/1.00  --bmc1_pre_inst_state                   false
% 2.69/1.00  --bmc1_pre_inst_reach_state             false
% 2.69/1.00  --bmc1_out_unsat_core                   false
% 2.69/1.00  --bmc1_aig_witness_out                  false
% 2.69/1.00  --bmc1_verbose                          false
% 2.69/1.00  --bmc1_dump_clauses_tptp                false
% 2.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.00  --bmc1_dump_file                        -
% 2.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.00  --bmc1_ucm_extend_mode                  1
% 2.69/1.00  --bmc1_ucm_init_mode                    2
% 2.69/1.00  --bmc1_ucm_cone_mode                    none
% 2.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.00  --bmc1_ucm_relax_model                  4
% 2.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.00  --bmc1_ucm_layered_model                none
% 2.69/1.00  --bmc1_ucm_max_lemma_size               10
% 2.69/1.00  
% 2.69/1.00  ------ AIG Options
% 2.69/1.00  
% 2.69/1.00  --aig_mode                              false
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation Options
% 2.69/1.00  
% 2.69/1.00  --instantiation_flag                    true
% 2.69/1.00  --inst_sos_flag                         false
% 2.69/1.00  --inst_sos_phase                        true
% 2.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel_side                     none
% 2.69/1.00  --inst_solver_per_active                1400
% 2.69/1.00  --inst_solver_calls_frac                1.
% 2.69/1.00  --inst_passive_queue_type               priority_queues
% 2.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.00  --inst_passive_queues_freq              [25;2]
% 2.69/1.00  --inst_dismatching                      true
% 2.69/1.00  --inst_eager_unprocessed_to_passive     true
% 2.69/1.00  --inst_prop_sim_given                   true
% 2.69/1.00  --inst_prop_sim_new                     false
% 2.69/1.00  --inst_subs_new                         false
% 2.69/1.00  --inst_eq_res_simp                      false
% 2.69/1.00  --inst_subs_given                       false
% 2.69/1.00  --inst_orphan_elimination               true
% 2.69/1.00  --inst_learning_loop_flag               true
% 2.69/1.00  --inst_learning_start                   3000
% 2.69/1.00  --inst_learning_factor                  2
% 2.69/1.00  --inst_start_prop_sim_after_learn       3
% 2.69/1.00  --inst_sel_renew                        solver
% 2.69/1.00  --inst_lit_activity_flag                true
% 2.69/1.00  --inst_restr_to_given                   false
% 2.69/1.00  --inst_activity_threshold               500
% 2.69/1.00  --inst_out_proof                        true
% 2.69/1.00  
% 2.69/1.00  ------ Resolution Options
% 2.69/1.00  
% 2.69/1.00  --resolution_flag                       false
% 2.69/1.00  --res_lit_sel                           adaptive
% 2.69/1.00  --res_lit_sel_side                      none
% 2.69/1.00  --res_ordering                          kbo
% 2.69/1.00  --res_to_prop_solver                    active
% 2.69/1.00  --res_prop_simpl_new                    false
% 2.69/1.00  --res_prop_simpl_given                  true
% 2.69/1.00  --res_passive_queue_type                priority_queues
% 2.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.00  --res_passive_queues_freq               [15;5]
% 2.69/1.00  --res_forward_subs                      full
% 2.69/1.00  --res_backward_subs                     full
% 2.69/1.00  --res_forward_subs_resolution           true
% 2.69/1.00  --res_backward_subs_resolution          true
% 2.69/1.00  --res_orphan_elimination                true
% 2.69/1.00  --res_time_limit                        2.
% 2.69/1.00  --res_out_proof                         true
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Options
% 2.69/1.00  
% 2.69/1.00  --superposition_flag                    true
% 2.69/1.00  --sup_passive_queue_type                priority_queues
% 2.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.00  --demod_completeness_check              fast
% 2.69/1.00  --demod_use_ground                      true
% 2.69/1.00  --sup_to_prop_solver                    passive
% 2.69/1.00  --sup_prop_simpl_new                    true
% 2.69/1.00  --sup_prop_simpl_given                  true
% 2.69/1.00  --sup_fun_splitting                     false
% 2.69/1.00  --sup_smt_interval                      50000
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Simplification Setup
% 2.69/1.00  
% 2.69/1.00  --sup_indices_passive                   []
% 2.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_full_bw                           [BwDemod]
% 2.69/1.00  --sup_immed_triv                        [TrivRules]
% 2.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_immed_bw_main                     []
% 2.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  
% 2.69/1.00  ------ Combination Options
% 2.69/1.00  
% 2.69/1.00  --comb_res_mult                         3
% 2.69/1.00  --comb_sup_mult                         2
% 2.69/1.00  --comb_inst_mult                        10
% 2.69/1.00  
% 2.69/1.00  ------ Debug Options
% 2.69/1.00  
% 2.69/1.00  --dbg_backtrace                         false
% 2.69/1.00  --dbg_dump_prop_clauses                 false
% 2.69/1.00  --dbg_dump_prop_clauses_file            -
% 2.69/1.00  --dbg_out_stat                          false
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ Proving...
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  % SZS status Theorem for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  fof(f17,conjecture,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f18,negated_conjecture,(
% 2.69/1.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.69/1.00    inference(negated_conjecture,[],[f17])).
% 2.69/1.00  
% 2.69/1.00  fof(f35,plain,(
% 2.69/1.00    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.69/1.00    inference(ennf_transformation,[],[f18])).
% 2.69/1.00  
% 2.69/1.00  fof(f38,plain,(
% 2.69/1.00    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f39,plain,(
% 2.69/1.00    (k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38])).
% 2.69/1.00  
% 2.69/1.00  fof(f60,plain,(
% 2.69/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.69/1.00    inference(cnf_transformation,[],[f39])).
% 2.69/1.00  
% 2.69/1.00  fof(f2,axiom,(
% 2.69/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f20,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f2])).
% 2.69/1.00  
% 2.69/1.00  fof(f43,plain,(
% 2.69/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f15,axiom,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f32,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.69/1.00    inference(ennf_transformation,[],[f15])).
% 2.69/1.00  
% 2.69/1.00  fof(f33,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.69/1.00    inference(flattening,[],[f32])).
% 2.69/1.00  
% 2.69/1.00  fof(f57,plain,(
% 2.69/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f33])).
% 2.69/1.00  
% 2.69/1.00  fof(f4,axiom,(
% 2.69/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f45,plain,(
% 2.69/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f4])).
% 2.69/1.00  
% 2.69/1.00  fof(f1,axiom,(
% 2.69/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f36,plain,(
% 2.69/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/1.00    inference(nnf_transformation,[],[f1])).
% 2.69/1.00  
% 2.69/1.00  fof(f37,plain,(
% 2.69/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/1.00    inference(flattening,[],[f36])).
% 2.69/1.00  
% 2.69/1.00  fof(f41,plain,(
% 2.69/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f62,plain,(
% 2.69/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.69/1.00    inference(equality_resolution,[],[f41])).
% 2.69/1.00  
% 2.69/1.00  fof(f9,axiom,(
% 2.69/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f25,plain,(
% 2.69/1.00    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.69/1.00    inference(ennf_transformation,[],[f9])).
% 2.69/1.00  
% 2.69/1.00  fof(f26,plain,(
% 2.69/1.00    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.69/1.00    inference(flattening,[],[f25])).
% 2.69/1.00  
% 2.69/1.00  fof(f51,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f26])).
% 2.69/1.00  
% 2.69/1.00  fof(f3,axiom,(
% 2.69/1.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f44,plain,(
% 2.69/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f3])).
% 2.69/1.00  
% 2.69/1.00  fof(f6,axiom,(
% 2.69/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f22,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f6])).
% 2.69/1.00  
% 2.69/1.00  fof(f47,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f8,axiom,(
% 2.69/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f49,plain,(
% 2.69/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.69/1.00    inference(cnf_transformation,[],[f8])).
% 2.69/1.00  
% 2.69/1.00  fof(f10,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f19,plain,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.69/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.69/1.00  
% 2.69/1.00  fof(f27,plain,(
% 2.69/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.00    inference(ennf_transformation,[],[f19])).
% 2.69/1.00  
% 2.69/1.00  fof(f52,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f27])).
% 2.69/1.00  
% 2.69/1.00  fof(f7,axiom,(
% 2.69/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f23,plain,(
% 2.69/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.69/1.00    inference(ennf_transformation,[],[f7])).
% 2.69/1.00  
% 2.69/1.00  fof(f24,plain,(
% 2.69/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/1.00    inference(flattening,[],[f23])).
% 2.69/1.00  
% 2.69/1.00  fof(f48,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f24])).
% 2.69/1.00  
% 2.69/1.00  fof(f5,axiom,(
% 2.69/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f21,plain,(
% 2.69/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/1.00    inference(ennf_transformation,[],[f5])).
% 2.69/1.00  
% 2.69/1.00  fof(f46,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f21])).
% 2.69/1.00  
% 2.69/1.00  fof(f14,axiom,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f31,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.00    inference(ennf_transformation,[],[f14])).
% 2.69/1.00  
% 2.69/1.00  fof(f56,plain,(
% 2.69/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f31])).
% 2.69/1.00  
% 2.69/1.00  fof(f11,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f28,plain,(
% 2.69/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.00    inference(ennf_transformation,[],[f11])).
% 2.69/1.00  
% 2.69/1.00  fof(f53,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f28])).
% 2.69/1.00  
% 2.69/1.00  fof(f12,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f29,plain,(
% 2.69/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.00    inference(ennf_transformation,[],[f12])).
% 2.69/1.00  
% 2.69/1.00  fof(f54,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f29])).
% 2.69/1.00  
% 2.69/1.00  fof(f61,plain,(
% 2.69/1.00    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 2.69/1.00    inference(cnf_transformation,[],[f39])).
% 2.69/1.00  
% 2.69/1.00  fof(f16,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f34,plain,(
% 2.69/1.00    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.00    inference(ennf_transformation,[],[f16])).
% 2.69/1.00  
% 2.69/1.00  fof(f58,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f34])).
% 2.69/1.00  
% 2.69/1.00  fof(f59,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f34])).
% 2.69/1.00  
% 2.69/1.00  fof(f13,axiom,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f30,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.00    inference(ennf_transformation,[],[f13])).
% 2.69/1.00  
% 2.69/1.00  fof(f55,plain,(
% 2.69/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f30])).
% 2.69/1.00  
% 2.69/1.00  cnf(c_21,negated_conjecture,
% 2.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.69/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_692,plain,
% 2.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/1.00      | ~ v1_relat_1(X1)
% 2.69/1.00      | v1_relat_1(X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_705,plain,
% 2.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.69/1.00      | v1_relat_1(X1) != iProver_top
% 2.69/1.00      | v1_relat_1(X0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1223,plain,
% 2.69/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.69/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_692,c_705]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_22,plain,
% 2.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_17,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.69/1.00      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 2.69/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_883,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 2.69/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1227,plain,
% 2.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
% 2.69/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.69/1.00      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_883]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1228,plain,
% 2.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) = iProver_top
% 2.69/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.69/1.00      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_825,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | v1_relat_1(X0)
% 2.69/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1296,plain,
% 2.69/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
% 2.69/1.00      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))
% 2.69/1.00      | v1_relat_1(sK2) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_825]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1319,plain,
% 2.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) != iProver_top
% 2.69/1.00      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)) != iProver_top
% 2.69/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_5,plain,
% 2.69/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1371,plain,
% 2.69/1.00      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1372,plain,
% 2.69/1.00      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1,plain,
% 2.69/1.00      ( r1_tarski(X0,X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_882,plain,
% 2.69/1.00      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1376,plain,
% 2.69/1.00      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_882]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1377,plain,
% 2.69/1.00      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1376]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1384,plain,
% 2.69/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_1223,c_22,c_1228,c_1319,c_1372,c_1377]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_706,plain,
% 2.69/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_11,plain,
% 2.69/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.69/1.00      | ~ v1_relat_1(X0)
% 2.69/1.00      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_700,plain,
% 2.69/1.00      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.69/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.69/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2487,plain,
% 2.69/1.00      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 2.69/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_706,c_700]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3902,plain,
% 2.69/1.00      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1384,c_2487]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4,plain,
% 2.69/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_704,plain,
% 2.69/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_7,plain,
% 2.69/1.00      ( ~ v1_relat_1(X0)
% 2.69/1.00      | ~ v1_relat_1(X1)
% 2.69/1.00      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_701,plain,
% 2.69/1.00      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.69/1.00      | v1_relat_1(X0) != iProver_top
% 2.69/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2637,plain,
% 2.69/1.00      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 2.69/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1384,c_701]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2722,plain,
% 2.69/1.00      ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_704,c_2637]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_10,plain,
% 2.69/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2730,plain,
% 2.69/1.00      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
% 2.69/1.00      inference(light_normalisation,[status(thm)],[c_2722,c_10]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4298,plain,
% 2.69/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3902,c_2730]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_695,plain,
% 2.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 2.69/1.00      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1440,plain,
% 2.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) = iProver_top
% 2.69/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_692,c_695]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_12,plain,
% 2.69/1.00      ( v4_relat_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.69/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_8,plain,
% 2.69/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_226,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | ~ v1_relat_1(X0)
% 2.69/1.00      | k7_relat_1(X0,X1) = X0 ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_12,c_8]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_691,plain,
% 2.69/1.00      ( k7_relat_1(X0,X1) = X0
% 2.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.69/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2094,plain,
% 2.69/1.00      ( k7_relat_1(sK2,X0) = sK2
% 2.69/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.69/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1440,c_691]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2918,plain,
% 2.69/1.00      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.69/1.00      | k7_relat_1(sK2,X0) = sK2 ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_2094,c_22,c_1228,c_1319,c_1372,c_1377]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2919,plain,
% 2.69/1.00      ( k7_relat_1(sK2,X0) = sK2
% 2.69/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 2.69/1.00      inference(renaming,[status(thm)],[c_2918]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2926,plain,
% 2.69/1.00      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_706,c_2919]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_6,plain,
% 2.69/1.00      ( ~ v1_relat_1(X0)
% 2.69/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_702,plain,
% 2.69/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.69/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1389,plain,
% 2.69/1.00      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1384,c_702]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3105,plain,
% 2.69/1.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2926,c_1389]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_16,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.69/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_696,plain,
% 2.69/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.69/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1530,plain,
% 2.69/1.00      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_692,c_696]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_13,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_699,plain,
% 2.69/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.69/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1102,plain,
% 2.69/1.00      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_692,c_699]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_14,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_698,plain,
% 2.69/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.69/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1026,plain,
% 2.69/1.00      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_692,c_698]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_20,negated_conjecture,
% 2.69/1.00      ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
% 2.69/1.00      | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1226,plain,
% 2.69/1.00      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.69/1.00      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_1026,c_20]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1346,plain,
% 2.69/1.00      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
% 2.69/1.00      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_1102,c_1226]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1764,plain,
% 2.69/1.00      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 2.69/1.00      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_1530,c_1346]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1765,plain,
% 2.69/1.00      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 2.69/1.00      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_1764,c_1530]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_19,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_693,plain,
% 2.69/1.00      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 2.69/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1625,plain,
% 2.69/1.00      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_692,c_693]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1626,plain,
% 2.69/1.00      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
% 2.69/1.00      inference(light_normalisation,[status(thm)],[c_1625,c_1026]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_18,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_694,plain,
% 2.69/1.00      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.69/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1630,plain,
% 2.69/1.00      ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_692,c_694]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1631,plain,
% 2.69/1.00      ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2) ),
% 2.69/1.00      inference(light_normalisation,[status(thm)],[c_1630,c_1102]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2302,plain,
% 2.69/1.00      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1530,c_1631]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2986,plain,
% 2.69/1.00      ( k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
% 2.69/1.00      | k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2) ),
% 2.69/1.00      inference(light_normalisation,[status(thm)],[c_1765,c_1626,c_2302]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_15,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.69/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_697,plain,
% 2.69/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.69/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1535,plain,
% 2.69/1.00      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_692,c_697]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2987,plain,
% 2.69/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 2.69/1.00      | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_2986,c_1535]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(contradiction,plain,
% 2.69/1.00      ( $false ),
% 2.69/1.00      inference(minisat,[status(thm)],[c_4298,c_3105,c_2987]) ).
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  ------                               Statistics
% 2.69/1.00  
% 2.69/1.00  ------ General
% 2.69/1.00  
% 2.69/1.00  abstr_ref_over_cycles:                  0
% 2.69/1.00  abstr_ref_under_cycles:                 0
% 2.69/1.00  gc_basic_clause_elim:                   0
% 2.69/1.00  forced_gc_time:                         0
% 2.69/1.00  parsing_time:                           0.01
% 2.69/1.00  unif_index_cands_time:                  0.
% 2.69/1.00  unif_index_add_time:                    0.
% 2.69/1.00  orderings_time:                         0.
% 2.69/1.00  out_proof_time:                         0.008
% 2.69/1.00  total_time:                             0.162
% 2.69/1.00  num_of_symbols:                         51
% 2.69/1.00  num_of_terms:                           5101
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing
% 2.69/1.00  
% 2.69/1.00  num_of_splits:                          0
% 2.69/1.00  num_of_split_atoms:                     0
% 2.69/1.00  num_of_reused_defs:                     0
% 2.69/1.00  num_eq_ax_congr_red:                    26
% 2.69/1.00  num_of_sem_filtered_clauses:            1
% 2.69/1.00  num_of_subtypes:                        0
% 2.69/1.00  monotx_restored_types:                  0
% 2.69/1.00  sat_num_of_epr_types:                   0
% 2.69/1.00  sat_num_of_non_cyclic_types:            0
% 2.69/1.00  sat_guarded_non_collapsed_types:        0
% 2.69/1.00  num_pure_diseq_elim:                    0
% 2.69/1.00  simp_replaced_by:                       0
% 2.69/1.00  res_preprocessed:                       112
% 2.69/1.00  prep_upred:                             0
% 2.69/1.00  prep_unflattend:                        0
% 2.69/1.00  smt_new_axioms:                         0
% 2.69/1.00  pred_elim_cands:                        3
% 2.69/1.00  pred_elim:                              1
% 2.69/1.00  pred_elim_cl:                           1
% 2.69/1.00  pred_elim_cycles:                       3
% 2.69/1.00  merged_defs:                            0
% 2.69/1.00  merged_defs_ncl:                        0
% 2.69/1.00  bin_hyper_res:                          0
% 2.69/1.00  prep_cycles:                            4
% 2.69/1.00  pred_elim_time:                         0.001
% 2.69/1.00  splitting_time:                         0.
% 2.69/1.00  sem_filter_time:                        0.
% 2.69/1.00  monotx_time:                            0.
% 2.69/1.00  subtype_inf_time:                       0.
% 2.69/1.00  
% 2.69/1.00  ------ Problem properties
% 2.69/1.00  
% 2.69/1.00  clauses:                                20
% 2.69/1.00  conjectures:                            2
% 2.69/1.00  epr:                                    2
% 2.69/1.00  horn:                                   20
% 2.69/1.00  ground:                                 2
% 2.69/1.00  unary:                                  6
% 2.69/1.00  binary:                                 8
% 2.69/1.00  lits:                                   40
% 2.69/1.00  lits_eq:                                15
% 2.69/1.00  fd_pure:                                0
% 2.69/1.00  fd_pseudo:                              0
% 2.69/1.00  fd_cond:                                0
% 2.69/1.00  fd_pseudo_cond:                         1
% 2.69/1.00  ac_symbols:                             0
% 2.69/1.00  
% 2.69/1.00  ------ Propositional Solver
% 2.69/1.00  
% 2.69/1.00  prop_solver_calls:                      28
% 2.69/1.00  prop_fast_solver_calls:                 627
% 2.69/1.00  smt_solver_calls:                       0
% 2.69/1.00  smt_fast_solver_calls:                  0
% 2.69/1.00  prop_num_of_clauses:                    1970
% 2.69/1.00  prop_preprocess_simplified:             6287
% 2.69/1.00  prop_fo_subsumed:                       4
% 2.69/1.00  prop_solver_time:                       0.
% 2.69/1.00  smt_solver_time:                        0.
% 2.69/1.00  smt_fast_solver_time:                   0.
% 2.69/1.00  prop_fast_solver_time:                  0.
% 2.69/1.00  prop_unsat_core_time:                   0.
% 2.69/1.00  
% 2.69/1.00  ------ QBF
% 2.69/1.00  
% 2.69/1.00  qbf_q_res:                              0
% 2.69/1.00  qbf_num_tautologies:                    0
% 2.69/1.00  qbf_prep_cycles:                        0
% 2.69/1.00  
% 2.69/1.00  ------ BMC1
% 2.69/1.00  
% 2.69/1.00  bmc1_current_bound:                     -1
% 2.69/1.00  bmc1_last_solved_bound:                 -1
% 2.69/1.00  bmc1_unsat_core_size:                   -1
% 2.69/1.00  bmc1_unsat_core_parents_size:           -1
% 2.69/1.00  bmc1_merge_next_fun:                    0
% 2.69/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation
% 2.69/1.00  
% 2.69/1.00  inst_num_of_clauses:                    662
% 2.69/1.00  inst_num_in_passive:                    314
% 2.69/1.00  inst_num_in_active:                     306
% 2.69/1.00  inst_num_in_unprocessed:                43
% 2.69/1.00  inst_num_of_loops:                      330
% 2.69/1.00  inst_num_of_learning_restarts:          0
% 2.69/1.00  inst_num_moves_active_passive:          21
% 2.69/1.00  inst_lit_activity:                      0
% 2.69/1.00  inst_lit_activity_moves:                0
% 2.69/1.00  inst_num_tautologies:                   0
% 2.69/1.00  inst_num_prop_implied:                  0
% 2.69/1.00  inst_num_existing_simplified:           0
% 2.69/1.00  inst_num_eq_res_simplified:             0
% 2.69/1.00  inst_num_child_elim:                    0
% 2.69/1.00  inst_num_of_dismatching_blockings:      111
% 2.69/1.00  inst_num_of_non_proper_insts:           541
% 2.69/1.00  inst_num_of_duplicates:                 0
% 2.69/1.00  inst_inst_num_from_inst_to_res:         0
% 2.69/1.00  inst_dismatching_checking_time:         0.
% 2.69/1.00  
% 2.69/1.00  ------ Resolution
% 2.69/1.00  
% 2.69/1.00  res_num_of_clauses:                     0
% 2.69/1.00  res_num_in_passive:                     0
% 2.69/1.00  res_num_in_active:                      0
% 2.69/1.00  res_num_of_loops:                       116
% 2.69/1.00  res_forward_subset_subsumed:            42
% 2.69/1.00  res_backward_subset_subsumed:           4
% 2.69/1.00  res_forward_subsumed:                   0
% 2.69/1.00  res_backward_subsumed:                  0
% 2.69/1.00  res_forward_subsumption_resolution:     0
% 2.69/1.00  res_backward_subsumption_resolution:    0
% 2.69/1.00  res_clause_to_clause_subsumption:       84
% 2.69/1.00  res_orphan_elimination:                 0
% 2.69/1.00  res_tautology_del:                      51
% 2.69/1.00  res_num_eq_res_simplified:              0
% 2.69/1.00  res_num_sel_changes:                    0
% 2.69/1.00  res_moves_from_active_to_pass:          0
% 2.69/1.00  
% 2.69/1.00  ------ Superposition
% 2.69/1.00  
% 2.69/1.00  sup_time_total:                         0.
% 2.69/1.00  sup_time_generating:                    0.
% 2.69/1.00  sup_time_sim_full:                      0.
% 2.69/1.00  sup_time_sim_immed:                     0.
% 2.69/1.00  
% 2.69/1.00  sup_num_of_clauses:                     70
% 2.69/1.00  sup_num_in_active:                      61
% 2.69/1.00  sup_num_in_passive:                     9
% 2.69/1.00  sup_num_of_loops:                       64
% 2.69/1.00  sup_fw_superposition:                   45
% 2.69/1.00  sup_bw_superposition:                   17
% 2.69/1.00  sup_immediate_simplified:               11
% 2.69/1.00  sup_given_eliminated:                   0
% 2.69/1.00  comparisons_done:                       0
% 2.69/1.00  comparisons_avoided:                    0
% 2.69/1.00  
% 2.69/1.00  ------ Simplifications
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  sim_fw_subset_subsumed:                 1
% 2.69/1.00  sim_bw_subset_subsumed:                 0
% 2.69/1.00  sim_fw_subsumed:                        3
% 2.69/1.00  sim_bw_subsumed:                        0
% 2.69/1.00  sim_fw_subsumption_res:                 0
% 2.69/1.00  sim_bw_subsumption_res:                 0
% 2.69/1.00  sim_tautology_del:                      0
% 2.69/1.00  sim_eq_tautology_del:                   2
% 2.69/1.00  sim_eq_res_simp:                        1
% 2.69/1.00  sim_fw_demodulated:                     3
% 2.69/1.00  sim_bw_demodulated:                     4
% 2.69/1.00  sim_light_normalised:                   9
% 2.69/1.00  sim_joinable_taut:                      0
% 2.69/1.00  sim_joinable_simp:                      0
% 2.69/1.00  sim_ac_normalised:                      0
% 2.69/1.00  sim_smt_subsumption:                    0
% 2.69/1.00  
%------------------------------------------------------------------------------
