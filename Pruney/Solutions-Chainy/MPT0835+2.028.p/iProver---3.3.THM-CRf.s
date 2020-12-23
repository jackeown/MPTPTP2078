%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:12 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 500 expanded)
%              Number of clauses        :   86 ( 223 expanded)
%              Number of leaves         :   20 (  99 expanded)
%              Depth                    :   19
%              Number of atoms          :  335 (1272 expanded)
%              Number of equality atoms :  174 ( 595 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f40])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

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

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_292,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_293,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_803,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_555,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_940,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_935,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_1086,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1087,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1209,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1210,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1209])).

cnf(c_1423,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_940,c_1087,c_1210])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_810,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_400,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_4,c_13])).

cnf(c_801,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_2658,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_810,c_801])).

cnf(c_4955,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1423,c_2658])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_807,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1725,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1423,c_807])).

cnf(c_4965,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4955,c_1725])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_7])).

cnf(c_307,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_273,c_25])).

cnf(c_308,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_802,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_309,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_1513,plain,
    ( r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_802,c_309,c_940,c_1087,c_1210])).

cnf(c_1514,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1513])).

cnf(c_1521,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1514])).

cnf(c_16,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_804,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2784,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_804])).

cnf(c_1522,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1521])).

cnf(c_1528,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1544,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_3155,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2784,c_940,c_1086,c_1209,c_1522,c_1544])).

cnf(c_8,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_809,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_805,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2843,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_805])).

cnf(c_2977,plain,
    ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_809,c_2843])).

cnf(c_15,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2985,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2977,c_15])).

cnf(c_3527,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3155,c_2985])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_340,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_341,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_970,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_341])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_358,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_359,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_934,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_359])).

cnf(c_24,negated_conjecture,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1058,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_934,c_24])).

cnf(c_1284,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_970,c_1058])).

cnf(c_1285,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_1284,c_970])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_322,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_323,plain,
    ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_1027,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_323])).

cnf(c_1369,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1027,c_934])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_331,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_332,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_1030,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_332])).

cnf(c_1420,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_1030,c_970])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_806,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1658,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1423,c_806])).

cnf(c_2120,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1285,c_1369,c_1420,c_1658])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_349,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_350,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_974,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_350])).

cnf(c_2121,plain,
    ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2120,c_974])).

cnf(c_3658,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3527,c_2121])).

cnf(c_3662,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_3658])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4965,c_3662])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.77/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/0.99  
% 2.77/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/0.99  
% 2.77/0.99  ------  iProver source info
% 2.77/0.99  
% 2.77/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.77/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/0.99  git: non_committed_changes: false
% 2.77/0.99  git: last_make_outside_of_git: false
% 2.77/0.99  
% 2.77/0.99  ------ 
% 2.77/0.99  
% 2.77/0.99  ------ Input Options
% 2.77/0.99  
% 2.77/0.99  --out_options                           all
% 2.77/0.99  --tptp_safe_out                         true
% 2.77/0.99  --problem_path                          ""
% 2.77/0.99  --include_path                          ""
% 2.77/0.99  --clausifier                            res/vclausify_rel
% 2.77/0.99  --clausifier_options                    --mode clausify
% 2.77/0.99  --stdin                                 false
% 2.77/0.99  --stats_out                             all
% 2.77/0.99  
% 2.77/0.99  ------ General Options
% 2.77/0.99  
% 2.77/0.99  --fof                                   false
% 2.77/0.99  --time_out_real                         305.
% 2.77/0.99  --time_out_virtual                      -1.
% 2.77/0.99  --symbol_type_check                     false
% 2.77/0.99  --clausify_out                          false
% 2.77/0.99  --sig_cnt_out                           false
% 2.77/0.99  --trig_cnt_out                          false
% 2.77/0.99  --trig_cnt_out_tolerance                1.
% 2.77/0.99  --trig_cnt_out_sk_spl                   false
% 2.77/0.99  --abstr_cl_out                          false
% 2.77/0.99  
% 2.77/0.99  ------ Global Options
% 2.77/0.99  
% 2.77/0.99  --schedule                              default
% 2.77/0.99  --add_important_lit                     false
% 2.77/0.99  --prop_solver_per_cl                    1000
% 2.77/0.99  --min_unsat_core                        false
% 2.77/0.99  --soft_assumptions                      false
% 2.77/0.99  --soft_lemma_size                       3
% 2.77/0.99  --prop_impl_unit_size                   0
% 2.77/0.99  --prop_impl_unit                        []
% 2.77/0.99  --share_sel_clauses                     true
% 2.77/0.99  --reset_solvers                         false
% 2.77/0.99  --bc_imp_inh                            [conj_cone]
% 2.77/0.99  --conj_cone_tolerance                   3.
% 2.77/0.99  --extra_neg_conj                        none
% 2.77/0.99  --large_theory_mode                     true
% 2.77/0.99  --prolific_symb_bound                   200
% 2.77/0.99  --lt_threshold                          2000
% 2.77/0.99  --clause_weak_htbl                      true
% 2.77/0.99  --gc_record_bc_elim                     false
% 2.77/0.99  
% 2.77/0.99  ------ Preprocessing Options
% 2.77/0.99  
% 2.77/0.99  --preprocessing_flag                    true
% 2.77/0.99  --time_out_prep_mult                    0.1
% 2.77/0.99  --splitting_mode                        input
% 2.77/0.99  --splitting_grd                         true
% 2.77/0.99  --splitting_cvd                         false
% 2.77/0.99  --splitting_cvd_svl                     false
% 2.77/0.99  --splitting_nvd                         32
% 2.77/0.99  --sub_typing                            true
% 2.77/0.99  --prep_gs_sim                           true
% 2.77/0.99  --prep_unflatten                        true
% 2.77/0.99  --prep_res_sim                          true
% 2.77/0.99  --prep_upred                            true
% 2.77/0.99  --prep_sem_filter                       exhaustive
% 2.77/0.99  --prep_sem_filter_out                   false
% 2.77/0.99  --pred_elim                             true
% 2.77/0.99  --res_sim_input                         true
% 2.77/0.99  --eq_ax_congr_red                       true
% 2.77/0.99  --pure_diseq_elim                       true
% 2.77/0.99  --brand_transform                       false
% 2.77/0.99  --non_eq_to_eq                          false
% 2.77/0.99  --prep_def_merge                        true
% 2.77/0.99  --prep_def_merge_prop_impl              false
% 2.77/0.99  --prep_def_merge_mbd                    true
% 2.77/0.99  --prep_def_merge_tr_red                 false
% 2.77/0.99  --prep_def_merge_tr_cl                  false
% 2.77/0.99  --smt_preprocessing                     true
% 2.77/0.99  --smt_ac_axioms                         fast
% 2.77/0.99  --preprocessed_out                      false
% 2.77/0.99  --preprocessed_stats                    false
% 2.77/0.99  
% 2.77/0.99  ------ Abstraction refinement Options
% 2.77/0.99  
% 2.77/0.99  --abstr_ref                             []
% 2.77/0.99  --abstr_ref_prep                        false
% 2.77/0.99  --abstr_ref_until_sat                   false
% 2.77/0.99  --abstr_ref_sig_restrict                funpre
% 2.77/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.99  --abstr_ref_under                       []
% 2.77/0.99  
% 2.77/0.99  ------ SAT Options
% 2.77/0.99  
% 2.77/0.99  --sat_mode                              false
% 2.77/0.99  --sat_fm_restart_options                ""
% 2.77/0.99  --sat_gr_def                            false
% 2.77/0.99  --sat_epr_types                         true
% 2.77/0.99  --sat_non_cyclic_types                  false
% 2.77/0.99  --sat_finite_models                     false
% 2.77/0.99  --sat_fm_lemmas                         false
% 2.77/0.99  --sat_fm_prep                           false
% 2.77/0.99  --sat_fm_uc_incr                        true
% 2.77/0.99  --sat_out_model                         small
% 2.77/0.99  --sat_out_clauses                       false
% 2.77/0.99  
% 2.77/0.99  ------ QBF Options
% 2.77/0.99  
% 2.77/0.99  --qbf_mode                              false
% 2.77/0.99  --qbf_elim_univ                         false
% 2.77/0.99  --qbf_dom_inst                          none
% 2.77/0.99  --qbf_dom_pre_inst                      false
% 2.77/0.99  --qbf_sk_in                             false
% 2.77/0.99  --qbf_pred_elim                         true
% 2.77/0.99  --qbf_split                             512
% 2.77/0.99  
% 2.77/0.99  ------ BMC1 Options
% 2.77/0.99  
% 2.77/0.99  --bmc1_incremental                      false
% 2.77/0.99  --bmc1_axioms                           reachable_all
% 2.77/0.99  --bmc1_min_bound                        0
% 2.77/0.99  --bmc1_max_bound                        -1
% 2.77/0.99  --bmc1_max_bound_default                -1
% 2.77/0.99  --bmc1_symbol_reachability              true
% 2.77/0.99  --bmc1_property_lemmas                  false
% 2.77/0.99  --bmc1_k_induction                      false
% 2.77/0.99  --bmc1_non_equiv_states                 false
% 2.77/0.99  --bmc1_deadlock                         false
% 2.77/0.99  --bmc1_ucm                              false
% 2.77/0.99  --bmc1_add_unsat_core                   none
% 2.77/1.00  --bmc1_unsat_core_children              false
% 2.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.00  --bmc1_out_stat                         full
% 2.77/1.00  --bmc1_ground_init                      false
% 2.77/1.00  --bmc1_pre_inst_next_state              false
% 2.77/1.00  --bmc1_pre_inst_state                   false
% 2.77/1.00  --bmc1_pre_inst_reach_state             false
% 2.77/1.00  --bmc1_out_unsat_core                   false
% 2.77/1.00  --bmc1_aig_witness_out                  false
% 2.77/1.00  --bmc1_verbose                          false
% 2.77/1.00  --bmc1_dump_clauses_tptp                false
% 2.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.00  --bmc1_dump_file                        -
% 2.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.00  --bmc1_ucm_extend_mode                  1
% 2.77/1.00  --bmc1_ucm_init_mode                    2
% 2.77/1.00  --bmc1_ucm_cone_mode                    none
% 2.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.00  --bmc1_ucm_relax_model                  4
% 2.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.00  --bmc1_ucm_layered_model                none
% 2.77/1.00  --bmc1_ucm_max_lemma_size               10
% 2.77/1.00  
% 2.77/1.00  ------ AIG Options
% 2.77/1.00  
% 2.77/1.00  --aig_mode                              false
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation Options
% 2.77/1.00  
% 2.77/1.00  --instantiation_flag                    true
% 2.77/1.00  --inst_sos_flag                         false
% 2.77/1.00  --inst_sos_phase                        true
% 2.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel_side                     num_symb
% 2.77/1.00  --inst_solver_per_active                1400
% 2.77/1.00  --inst_solver_calls_frac                1.
% 2.77/1.00  --inst_passive_queue_type               priority_queues
% 2.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.00  --inst_passive_queues_freq              [25;2]
% 2.77/1.00  --inst_dismatching                      true
% 2.77/1.00  --inst_eager_unprocessed_to_passive     true
% 2.77/1.00  --inst_prop_sim_given                   true
% 2.77/1.00  --inst_prop_sim_new                     false
% 2.77/1.00  --inst_subs_new                         false
% 2.77/1.00  --inst_eq_res_simp                      false
% 2.77/1.00  --inst_subs_given                       false
% 2.77/1.00  --inst_orphan_elimination               true
% 2.77/1.00  --inst_learning_loop_flag               true
% 2.77/1.00  --inst_learning_start                   3000
% 2.77/1.00  --inst_learning_factor                  2
% 2.77/1.00  --inst_start_prop_sim_after_learn       3
% 2.77/1.00  --inst_sel_renew                        solver
% 2.77/1.00  --inst_lit_activity_flag                true
% 2.77/1.00  --inst_restr_to_given                   false
% 2.77/1.00  --inst_activity_threshold               500
% 2.77/1.00  --inst_out_proof                        true
% 2.77/1.00  
% 2.77/1.00  ------ Resolution Options
% 2.77/1.00  
% 2.77/1.00  --resolution_flag                       true
% 2.77/1.00  --res_lit_sel                           adaptive
% 2.77/1.00  --res_lit_sel_side                      none
% 2.77/1.00  --res_ordering                          kbo
% 2.77/1.00  --res_to_prop_solver                    active
% 2.77/1.00  --res_prop_simpl_new                    false
% 2.77/1.00  --res_prop_simpl_given                  true
% 2.77/1.00  --res_passive_queue_type                priority_queues
% 2.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.00  --res_passive_queues_freq               [15;5]
% 2.77/1.00  --res_forward_subs                      full
% 2.77/1.00  --res_backward_subs                     full
% 2.77/1.00  --res_forward_subs_resolution           true
% 2.77/1.00  --res_backward_subs_resolution          true
% 2.77/1.00  --res_orphan_elimination                true
% 2.77/1.00  --res_time_limit                        2.
% 2.77/1.00  --res_out_proof                         true
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Options
% 2.77/1.00  
% 2.77/1.00  --superposition_flag                    true
% 2.77/1.00  --sup_passive_queue_type                priority_queues
% 2.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.00  --demod_completeness_check              fast
% 2.77/1.00  --demod_use_ground                      true
% 2.77/1.00  --sup_to_prop_solver                    passive
% 2.77/1.00  --sup_prop_simpl_new                    true
% 2.77/1.00  --sup_prop_simpl_given                  true
% 2.77/1.00  --sup_fun_splitting                     false
% 2.77/1.00  --sup_smt_interval                      50000
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Simplification Setup
% 2.77/1.00  
% 2.77/1.00  --sup_indices_passive                   []
% 2.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_full_bw                           [BwDemod]
% 2.77/1.00  --sup_immed_triv                        [TrivRules]
% 2.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_immed_bw_main                     []
% 2.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  
% 2.77/1.00  ------ Combination Options
% 2.77/1.00  
% 2.77/1.00  --comb_res_mult                         3
% 2.77/1.00  --comb_sup_mult                         2
% 2.77/1.00  --comb_inst_mult                        10
% 2.77/1.00  
% 2.77/1.00  ------ Debug Options
% 2.77/1.00  
% 2.77/1.00  --dbg_backtrace                         false
% 2.77/1.00  --dbg_dump_prop_clauses                 false
% 2.77/1.00  --dbg_dump_prop_clauses_file            -
% 2.77/1.00  --dbg_out_stat                          false
% 2.77/1.00  ------ Parsing...
% 2.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/1.00  ------ Proving...
% 2.77/1.00  ------ Problem Properties 
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  clauses                                 21
% 2.77/1.00  conjectures                             1
% 2.77/1.00  EPR                                     2
% 2.77/1.00  Horn                                    21
% 2.77/1.00  unary                                   5
% 2.77/1.00  binary                                  8
% 2.77/1.00  lits                                    45
% 2.77/1.00  lits eq                                 25
% 2.77/1.00  fd_pure                                 0
% 2.77/1.00  fd_pseudo                               0
% 2.77/1.00  fd_cond                                 0
% 2.77/1.00  fd_pseudo_cond                          1
% 2.77/1.00  AC symbols                              0
% 2.77/1.00  
% 2.77/1.00  ------ Schedule dynamic 5 is on 
% 2.77/1.00  
% 2.77/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  ------ 
% 2.77/1.00  Current options:
% 2.77/1.00  ------ 
% 2.77/1.00  
% 2.77/1.00  ------ Input Options
% 2.77/1.00  
% 2.77/1.00  --out_options                           all
% 2.77/1.00  --tptp_safe_out                         true
% 2.77/1.00  --problem_path                          ""
% 2.77/1.00  --include_path                          ""
% 2.77/1.00  --clausifier                            res/vclausify_rel
% 2.77/1.00  --clausifier_options                    --mode clausify
% 2.77/1.00  --stdin                                 false
% 2.77/1.00  --stats_out                             all
% 2.77/1.00  
% 2.77/1.00  ------ General Options
% 2.77/1.00  
% 2.77/1.00  --fof                                   false
% 2.77/1.00  --time_out_real                         305.
% 2.77/1.00  --time_out_virtual                      -1.
% 2.77/1.00  --symbol_type_check                     false
% 2.77/1.00  --clausify_out                          false
% 2.77/1.00  --sig_cnt_out                           false
% 2.77/1.00  --trig_cnt_out                          false
% 2.77/1.00  --trig_cnt_out_tolerance                1.
% 2.77/1.00  --trig_cnt_out_sk_spl                   false
% 2.77/1.00  --abstr_cl_out                          false
% 2.77/1.00  
% 2.77/1.00  ------ Global Options
% 2.77/1.00  
% 2.77/1.00  --schedule                              default
% 2.77/1.00  --add_important_lit                     false
% 2.77/1.00  --prop_solver_per_cl                    1000
% 2.77/1.00  --min_unsat_core                        false
% 2.77/1.00  --soft_assumptions                      false
% 2.77/1.00  --soft_lemma_size                       3
% 2.77/1.00  --prop_impl_unit_size                   0
% 2.77/1.00  --prop_impl_unit                        []
% 2.77/1.00  --share_sel_clauses                     true
% 2.77/1.00  --reset_solvers                         false
% 2.77/1.00  --bc_imp_inh                            [conj_cone]
% 2.77/1.00  --conj_cone_tolerance                   3.
% 2.77/1.00  --extra_neg_conj                        none
% 2.77/1.00  --large_theory_mode                     true
% 2.77/1.00  --prolific_symb_bound                   200
% 2.77/1.00  --lt_threshold                          2000
% 2.77/1.00  --clause_weak_htbl                      true
% 2.77/1.00  --gc_record_bc_elim                     false
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing Options
% 2.77/1.00  
% 2.77/1.00  --preprocessing_flag                    true
% 2.77/1.00  --time_out_prep_mult                    0.1
% 2.77/1.00  --splitting_mode                        input
% 2.77/1.00  --splitting_grd                         true
% 2.77/1.00  --splitting_cvd                         false
% 2.77/1.00  --splitting_cvd_svl                     false
% 2.77/1.00  --splitting_nvd                         32
% 2.77/1.00  --sub_typing                            true
% 2.77/1.00  --prep_gs_sim                           true
% 2.77/1.00  --prep_unflatten                        true
% 2.77/1.00  --prep_res_sim                          true
% 2.77/1.00  --prep_upred                            true
% 2.77/1.00  --prep_sem_filter                       exhaustive
% 2.77/1.00  --prep_sem_filter_out                   false
% 2.77/1.00  --pred_elim                             true
% 2.77/1.00  --res_sim_input                         true
% 2.77/1.00  --eq_ax_congr_red                       true
% 2.77/1.00  --pure_diseq_elim                       true
% 2.77/1.00  --brand_transform                       false
% 2.77/1.00  --non_eq_to_eq                          false
% 2.77/1.00  --prep_def_merge                        true
% 2.77/1.00  --prep_def_merge_prop_impl              false
% 2.77/1.00  --prep_def_merge_mbd                    true
% 2.77/1.00  --prep_def_merge_tr_red                 false
% 2.77/1.00  --prep_def_merge_tr_cl                  false
% 2.77/1.00  --smt_preprocessing                     true
% 2.77/1.00  --smt_ac_axioms                         fast
% 2.77/1.00  --preprocessed_out                      false
% 2.77/1.00  --preprocessed_stats                    false
% 2.77/1.00  
% 2.77/1.00  ------ Abstraction refinement Options
% 2.77/1.00  
% 2.77/1.00  --abstr_ref                             []
% 2.77/1.00  --abstr_ref_prep                        false
% 2.77/1.00  --abstr_ref_until_sat                   false
% 2.77/1.00  --abstr_ref_sig_restrict                funpre
% 2.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.00  --abstr_ref_under                       []
% 2.77/1.00  
% 2.77/1.00  ------ SAT Options
% 2.77/1.00  
% 2.77/1.00  --sat_mode                              false
% 2.77/1.00  --sat_fm_restart_options                ""
% 2.77/1.00  --sat_gr_def                            false
% 2.77/1.00  --sat_epr_types                         true
% 2.77/1.00  --sat_non_cyclic_types                  false
% 2.77/1.00  --sat_finite_models                     false
% 2.77/1.00  --sat_fm_lemmas                         false
% 2.77/1.00  --sat_fm_prep                           false
% 2.77/1.00  --sat_fm_uc_incr                        true
% 2.77/1.00  --sat_out_model                         small
% 2.77/1.00  --sat_out_clauses                       false
% 2.77/1.00  
% 2.77/1.00  ------ QBF Options
% 2.77/1.00  
% 2.77/1.00  --qbf_mode                              false
% 2.77/1.00  --qbf_elim_univ                         false
% 2.77/1.00  --qbf_dom_inst                          none
% 2.77/1.00  --qbf_dom_pre_inst                      false
% 2.77/1.00  --qbf_sk_in                             false
% 2.77/1.00  --qbf_pred_elim                         true
% 2.77/1.00  --qbf_split                             512
% 2.77/1.00  
% 2.77/1.00  ------ BMC1 Options
% 2.77/1.00  
% 2.77/1.00  --bmc1_incremental                      false
% 2.77/1.00  --bmc1_axioms                           reachable_all
% 2.77/1.00  --bmc1_min_bound                        0
% 2.77/1.00  --bmc1_max_bound                        -1
% 2.77/1.00  --bmc1_max_bound_default                -1
% 2.77/1.00  --bmc1_symbol_reachability              true
% 2.77/1.00  --bmc1_property_lemmas                  false
% 2.77/1.00  --bmc1_k_induction                      false
% 2.77/1.00  --bmc1_non_equiv_states                 false
% 2.77/1.00  --bmc1_deadlock                         false
% 2.77/1.00  --bmc1_ucm                              false
% 2.77/1.00  --bmc1_add_unsat_core                   none
% 2.77/1.00  --bmc1_unsat_core_children              false
% 2.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.00  --bmc1_out_stat                         full
% 2.77/1.00  --bmc1_ground_init                      false
% 2.77/1.00  --bmc1_pre_inst_next_state              false
% 2.77/1.00  --bmc1_pre_inst_state                   false
% 2.77/1.00  --bmc1_pre_inst_reach_state             false
% 2.77/1.00  --bmc1_out_unsat_core                   false
% 2.77/1.00  --bmc1_aig_witness_out                  false
% 2.77/1.00  --bmc1_verbose                          false
% 2.77/1.00  --bmc1_dump_clauses_tptp                false
% 2.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.00  --bmc1_dump_file                        -
% 2.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.00  --bmc1_ucm_extend_mode                  1
% 2.77/1.00  --bmc1_ucm_init_mode                    2
% 2.77/1.00  --bmc1_ucm_cone_mode                    none
% 2.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.00  --bmc1_ucm_relax_model                  4
% 2.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.00  --bmc1_ucm_layered_model                none
% 2.77/1.00  --bmc1_ucm_max_lemma_size               10
% 2.77/1.00  
% 2.77/1.00  ------ AIG Options
% 2.77/1.00  
% 2.77/1.00  --aig_mode                              false
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation Options
% 2.77/1.00  
% 2.77/1.00  --instantiation_flag                    true
% 2.77/1.00  --inst_sos_flag                         false
% 2.77/1.00  --inst_sos_phase                        true
% 2.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel_side                     none
% 2.77/1.00  --inst_solver_per_active                1400
% 2.77/1.00  --inst_solver_calls_frac                1.
% 2.77/1.00  --inst_passive_queue_type               priority_queues
% 2.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.00  --inst_passive_queues_freq              [25;2]
% 2.77/1.00  --inst_dismatching                      true
% 2.77/1.00  --inst_eager_unprocessed_to_passive     true
% 2.77/1.00  --inst_prop_sim_given                   true
% 2.77/1.00  --inst_prop_sim_new                     false
% 2.77/1.00  --inst_subs_new                         false
% 2.77/1.00  --inst_eq_res_simp                      false
% 2.77/1.00  --inst_subs_given                       false
% 2.77/1.00  --inst_orphan_elimination               true
% 2.77/1.00  --inst_learning_loop_flag               true
% 2.77/1.00  --inst_learning_start                   3000
% 2.77/1.00  --inst_learning_factor                  2
% 2.77/1.00  --inst_start_prop_sim_after_learn       3
% 2.77/1.00  --inst_sel_renew                        solver
% 2.77/1.00  --inst_lit_activity_flag                true
% 2.77/1.00  --inst_restr_to_given                   false
% 2.77/1.00  --inst_activity_threshold               500
% 2.77/1.00  --inst_out_proof                        true
% 2.77/1.00  
% 2.77/1.00  ------ Resolution Options
% 2.77/1.00  
% 2.77/1.00  --resolution_flag                       false
% 2.77/1.00  --res_lit_sel                           adaptive
% 2.77/1.00  --res_lit_sel_side                      none
% 2.77/1.00  --res_ordering                          kbo
% 2.77/1.00  --res_to_prop_solver                    active
% 2.77/1.00  --res_prop_simpl_new                    false
% 2.77/1.00  --res_prop_simpl_given                  true
% 2.77/1.00  --res_passive_queue_type                priority_queues
% 2.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.00  --res_passive_queues_freq               [15;5]
% 2.77/1.00  --res_forward_subs                      full
% 2.77/1.00  --res_backward_subs                     full
% 2.77/1.00  --res_forward_subs_resolution           true
% 2.77/1.00  --res_backward_subs_resolution          true
% 2.77/1.00  --res_orphan_elimination                true
% 2.77/1.00  --res_time_limit                        2.
% 2.77/1.00  --res_out_proof                         true
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Options
% 2.77/1.00  
% 2.77/1.00  --superposition_flag                    true
% 2.77/1.00  --sup_passive_queue_type                priority_queues
% 2.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.00  --demod_completeness_check              fast
% 2.77/1.00  --demod_use_ground                      true
% 2.77/1.00  --sup_to_prop_solver                    passive
% 2.77/1.00  --sup_prop_simpl_new                    true
% 2.77/1.00  --sup_prop_simpl_given                  true
% 2.77/1.00  --sup_fun_splitting                     false
% 2.77/1.00  --sup_smt_interval                      50000
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Simplification Setup
% 2.77/1.00  
% 2.77/1.00  --sup_indices_passive                   []
% 2.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_full_bw                           [BwDemod]
% 2.77/1.00  --sup_immed_triv                        [TrivRules]
% 2.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_immed_bw_main                     []
% 2.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  
% 2.77/1.00  ------ Combination Options
% 2.77/1.00  
% 2.77/1.00  --comb_res_mult                         3
% 2.77/1.00  --comb_sup_mult                         2
% 2.77/1.00  --comb_inst_mult                        10
% 2.77/1.00  
% 2.77/1.00  ------ Debug Options
% 2.77/1.00  
% 2.77/1.00  --dbg_backtrace                         false
% 2.77/1.00  --dbg_dump_prop_clauses                 false
% 2.77/1.00  --dbg_dump_prop_clauses_file            -
% 2.77/1.00  --dbg_out_stat                          false
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  ------ Proving...
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  % SZS status Theorem for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  fof(f2,axiom,(
% 2.77/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f20,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f2])).
% 2.77/1.00  
% 2.77/1.00  fof(f45,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f20])).
% 2.77/1.00  
% 2.77/1.00  fof(f18,conjecture,(
% 2.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f19,negated_conjecture,(
% 2.77/1.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.77/1.00    inference(negated_conjecture,[],[f18])).
% 2.77/1.00  
% 2.77/1.00  fof(f35,plain,(
% 2.77/1.00    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.77/1.00    inference(ennf_transformation,[],[f19])).
% 2.77/1.00  
% 2.77/1.00  fof(f40,plain,(
% 2.77/1.00    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f41,plain,(
% 2.77/1.00    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f40])).
% 2.77/1.00  
% 2.77/1.00  fof(f66,plain,(
% 2.77/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.77/1.00    inference(cnf_transformation,[],[f41])).
% 2.77/1.00  
% 2.77/1.00  fof(f6,axiom,(
% 2.77/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f51,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f6])).
% 2.77/1.00  
% 2.77/1.00  fof(f1,axiom,(
% 2.77/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f36,plain,(
% 2.77/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.77/1.00    inference(nnf_transformation,[],[f1])).
% 2.77/1.00  
% 2.77/1.00  fof(f37,plain,(
% 2.77/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.77/1.00    inference(flattening,[],[f36])).
% 2.77/1.00  
% 2.77/1.00  fof(f42,plain,(
% 2.77/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.77/1.00    inference(cnf_transformation,[],[f37])).
% 2.77/1.00  
% 2.77/1.00  fof(f69,plain,(
% 2.77/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.77/1.00    inference(equality_resolution,[],[f42])).
% 2.77/1.00  
% 2.77/1.00  fof(f3,axiom,(
% 2.77/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f21,plain,(
% 2.77/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(ennf_transformation,[],[f3])).
% 2.77/1.00  
% 2.77/1.00  fof(f38,plain,(
% 2.77/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(nnf_transformation,[],[f21])).
% 2.77/1.00  
% 2.77/1.00  fof(f47,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f38])).
% 2.77/1.00  
% 2.77/1.00  fof(f10,axiom,(
% 2.77/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f26,plain,(
% 2.77/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.77/1.00    inference(ennf_transformation,[],[f10])).
% 2.77/1.00  
% 2.77/1.00  fof(f27,plain,(
% 2.77/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(flattening,[],[f26])).
% 2.77/1.00  
% 2.77/1.00  fof(f55,plain,(
% 2.77/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f27])).
% 2.77/1.00  
% 2.77/1.00  fof(f7,axiom,(
% 2.77/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f23,plain,(
% 2.77/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(ennf_transformation,[],[f7])).
% 2.77/1.00  
% 2.77/1.00  fof(f52,plain,(
% 2.77/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f23])).
% 2.77/1.00  
% 2.77/1.00  fof(f13,axiom,(
% 2.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f30,plain,(
% 2.77/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.00    inference(ennf_transformation,[],[f13])).
% 2.77/1.00  
% 2.77/1.00  fof(f60,plain,(
% 2.77/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f30])).
% 2.77/1.00  
% 2.77/1.00  fof(f4,axiom,(
% 2.77/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f22,plain,(
% 2.77/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(ennf_transformation,[],[f4])).
% 2.77/1.00  
% 2.77/1.00  fof(f39,plain,(
% 2.77/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(nnf_transformation,[],[f22])).
% 2.77/1.00  
% 2.77/1.00  fof(f48,plain,(
% 2.77/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f39])).
% 2.77/1.00  
% 2.77/1.00  fof(f12,axiom,(
% 2.77/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f28,plain,(
% 2.77/1.00    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(ennf_transformation,[],[f12])).
% 2.77/1.00  
% 2.77/1.00  fof(f29,plain,(
% 2.77/1.00    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(flattening,[],[f28])).
% 2.77/1.00  
% 2.77/1.00  fof(f58,plain,(
% 2.77/1.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f29])).
% 2.77/1.00  
% 2.77/1.00  fof(f5,axiom,(
% 2.77/1.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f50,plain,(
% 2.77/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f5])).
% 2.77/1.00  
% 2.77/1.00  fof(f9,axiom,(
% 2.77/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f25,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f9])).
% 2.77/1.00  
% 2.77/1.00  fof(f54,plain,(
% 2.77/1.00    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f25])).
% 2.77/1.00  
% 2.77/1.00  fof(f11,axiom,(
% 2.77/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f56,plain,(
% 2.77/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.77/1.00    inference(cnf_transformation,[],[f11])).
% 2.77/1.00  
% 2.77/1.00  fof(f16,axiom,(
% 2.77/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f33,plain,(
% 2.77/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.00    inference(ennf_transformation,[],[f16])).
% 2.77/1.00  
% 2.77/1.00  fof(f63,plain,(
% 2.77/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f33])).
% 2.77/1.00  
% 2.77/1.00  fof(f14,axiom,(
% 2.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f31,plain,(
% 2.77/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.00    inference(ennf_transformation,[],[f14])).
% 2.77/1.00  
% 2.77/1.00  fof(f61,plain,(
% 2.77/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f31])).
% 2.77/1.00  
% 2.77/1.00  fof(f67,plain,(
% 2.77/1.00    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 2.77/1.00    inference(cnf_transformation,[],[f41])).
% 2.77/1.00  
% 2.77/1.00  fof(f17,axiom,(
% 2.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f34,plain,(
% 2.77/1.00    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.00    inference(ennf_transformation,[],[f17])).
% 2.77/1.00  
% 2.77/1.00  fof(f64,plain,(
% 2.77/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f34])).
% 2.77/1.00  
% 2.77/1.00  fof(f65,plain,(
% 2.77/1.00    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f34])).
% 2.77/1.00  
% 2.77/1.00  fof(f8,axiom,(
% 2.77/1.00    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f24,plain,(
% 2.77/1.00    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f8])).
% 2.77/1.00  
% 2.77/1.00  fof(f53,plain,(
% 2.77/1.00    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f24])).
% 2.77/1.00  
% 2.77/1.00  fof(f15,axiom,(
% 2.77/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f32,plain,(
% 2.77/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.00    inference(ennf_transformation,[],[f15])).
% 2.77/1.00  
% 2.77/1.00  fof(f62,plain,(
% 2.77/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f32])).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.77/1.00      | ~ v1_relat_1(X1)
% 2.77/1.00      | v1_relat_1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_25,negated_conjecture,
% 2.77/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.77/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_292,plain,
% 2.77/1.00      ( ~ v1_relat_1(X0)
% 2.77/1.00      | v1_relat_1(X1)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 2.77/1.00      | sK2 != X1 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_293,plain,
% 2.77/1.00      ( ~ v1_relat_1(X0)
% 2.77/1.00      | v1_relat_1(sK2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_292]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_803,plain,
% 2.77/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 2.77/1.00      | v1_relat_1(X0) != iProver_top
% 2.77/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_555,plain,( X0 = X0 ),theory(equality) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_940,plain,
% 2.77/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_555]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_935,plain,
% 2.77/1.00      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.77/1.00      | v1_relat_1(sK2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_293]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1086,plain,
% 2.77/1.00      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | v1_relat_1(sK2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_935]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1087,plain,
% 2.77/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.77/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1086]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_9,plain,
% 2.77/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1209,plain,
% 2.77/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1210,plain,
% 2.77/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1209]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1423,plain,
% 2.77/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_803,c_940,c_1087,c_1210]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2,plain,
% 2.77/1.00      ( r1_tarski(X0,X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_810,plain,
% 2.77/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4,plain,
% 2.77/1.00      ( v4_relat_1(X0,X1)
% 2.77/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.77/1.00      | ~ v1_relat_1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_13,plain,
% 2.77/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.77/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_400,plain,
% 2.77/1.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.77/1.00      | ~ v1_relat_1(X0)
% 2.77/1.00      | k7_relat_1(X0,X1) = X0 ),
% 2.77/1.00      inference(resolution,[status(thm)],[c_4,c_13]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_801,plain,
% 2.77/1.00      ( k7_relat_1(X0,X1) = X0
% 2.77/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2658,plain,
% 2.77/1.00      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_810,c_801]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4955,plain,
% 2.77/1.00      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1423,c_2658]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_10,plain,
% 2.77/1.00      ( ~ v1_relat_1(X0)
% 2.77/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.77/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_807,plain,
% 2.77/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1725,plain,
% 2.77/1.00      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1423,c_807]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4965,plain,
% 2.77/1.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_4955,c_1725]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_17,plain,
% 2.77/1.00      ( v5_relat_1(X0,X1)
% 2.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.77/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7,plain,
% 2.77/1.00      ( ~ v5_relat_1(X0,X1)
% 2.77/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 2.77/1.00      | ~ v1_relat_1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_273,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 2.77/1.00      | ~ v1_relat_1(X0) ),
% 2.77/1.00      inference(resolution,[status(thm)],[c_17,c_7]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_307,plain,
% 2.77/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 2.77/1.00      | ~ v1_relat_1(X0)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | sK2 != X0 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_273,c_25]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_308,plain,
% 2.77/1.00      ( r1_tarski(k2_relat_1(sK2),X0)
% 2.77/1.00      | ~ v1_relat_1(sK2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_307]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_802,plain,
% 2.77/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 2.77/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_309,plain,
% 2.77/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 2.77/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1513,plain,
% 2.77/1.00      ( r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_802,c_309,c_940,c_1087,c_1210]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1514,plain,
% 2.77/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
% 2.77/1.00      inference(renaming,[status(thm)],[c_1513]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1521,plain,
% 2.77/1.00      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 2.77/1.00      inference(equality_resolution,[status(thm)],[c_1514]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_16,plain,
% 2.77/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.77/1.00      | ~ v1_relat_1(X0)
% 2.77/1.00      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.77/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_804,plain,
% 2.77/1.00      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.77/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2784,plain,
% 2.77/1.00      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
% 2.77/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1521,c_804]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1522,plain,
% 2.77/1.00      ( r1_tarski(k2_relat_1(sK2),sK0) ),
% 2.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1521]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1528,plain,
% 2.77/1.00      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 2.77/1.00      | ~ v1_relat_1(sK2)
% 2.77/1.00      | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1544,plain,
% 2.77/1.00      ( ~ r1_tarski(k2_relat_1(sK2),sK0)
% 2.77/1.00      | ~ v1_relat_1(sK2)
% 2.77/1.00      | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1528]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3155,plain,
% 2.77/1.00      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_2784,c_940,c_1086,c_1209,c_1522,c_1544]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_8,plain,
% 2.77/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_809,plain,
% 2.77/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_12,plain,
% 2.77/1.00      ( ~ v1_relat_1(X0)
% 2.77/1.00      | ~ v1_relat_1(X1)
% 2.77/1.00      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_805,plain,
% 2.77/1.00      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.77/1.00      | v1_relat_1(X0) != iProver_top
% 2.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2843,plain,
% 2.77/1.00      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 2.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1423,c_805]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2977,plain,
% 2.77/1.00      ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_809,c_2843]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_15,plain,
% 2.77/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.77/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2985,plain,
% 2.77/1.00      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
% 2.77/1.00      inference(light_normalisation,[status(thm)],[c_2977,c_15]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3527,plain,
% 2.77/1.00      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3155,c_2985]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_21,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.77/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_340,plain,
% 2.77/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | sK2 != X2 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_341,plain,
% 2.77/1.00      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_340]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_970,plain,
% 2.77/1.00      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.77/1.00      inference(equality_resolution,[status(thm)],[c_341]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_19,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_358,plain,
% 2.77/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | sK2 != X2 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_359,plain,
% 2.77/1.00      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_358]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_934,plain,
% 2.77/1.00      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 2.77/1.00      inference(equality_resolution,[status(thm)],[c_359]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_24,negated_conjecture,
% 2.77/1.00      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.77/1.00      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1058,plain,
% 2.77/1.00      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.77/1.00      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.77/1.00      inference(demodulation,[status(thm)],[c_934,c_24]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1284,plain,
% 2.77/1.00      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 2.77/1.00      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
% 2.77/1.00      inference(demodulation,[status(thm)],[c_970,c_1058]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1285,plain,
% 2.77/1.00      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 2.77/1.00      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
% 2.77/1.00      inference(demodulation,[status(thm)],[c_1284,c_970]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_23,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.00      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_322,plain,
% 2.77/1.00      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | sK2 != X2 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_323,plain,
% 2.77/1.00      ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_322]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1027,plain,
% 2.77/1.00      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
% 2.77/1.00      inference(equality_resolution,[status(thm)],[c_323]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1369,plain,
% 2.77/1.00      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
% 2.77/1.00      inference(light_normalisation,[status(thm)],[c_1027,c_934]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_22,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.00      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_331,plain,
% 2.77/1.00      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | sK2 != X2 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_332,plain,
% 2.77/1.00      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_331]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1030,plain,
% 2.77/1.00      ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
% 2.77/1.00      inference(equality_resolution,[status(thm)],[c_332]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1420,plain,
% 2.77/1.00      ( k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0) ),
% 2.77/1.00      inference(demodulation,[status(thm)],[c_1030,c_970]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_11,plain,
% 2.77/1.00      ( ~ v1_relat_1(X0)
% 2.77/1.00      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_806,plain,
% 2.77/1.00      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 2.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1658,plain,
% 2.77/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1423,c_806]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2120,plain,
% 2.77/1.00      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 2.77/1.00      | k10_relat_1(sK2,sK0) != k1_relat_1(sK2) ),
% 2.77/1.00      inference(light_normalisation,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_1285,c_1369,c_1420,c_1658]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_20,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.77/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_349,plain,
% 2.77/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.77/1.00      | sK2 != X2 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_350,plain,
% 2.77/1.00      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_349]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_974,plain,
% 2.77/1.00      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.77/1.00      inference(equality_resolution,[status(thm)],[c_350]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2121,plain,
% 2.77/1.00      ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
% 2.77/1.00      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.77/1.00      inference(demodulation,[status(thm)],[c_2120,c_974]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3658,plain,
% 2.77/1.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
% 2.77/1.00      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 2.77/1.00      inference(demodulation,[status(thm)],[c_3527,c_2121]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3662,plain,
% 2.77/1.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.77/1.00      inference(equality_resolution_simp,[status(thm)],[c_3658]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(contradiction,plain,
% 2.77/1.00      ( $false ),
% 2.77/1.00      inference(minisat,[status(thm)],[c_4965,c_3662]) ).
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  ------                               Statistics
% 2.77/1.00  
% 2.77/1.00  ------ General
% 2.77/1.00  
% 2.77/1.00  abstr_ref_over_cycles:                  0
% 2.77/1.00  abstr_ref_under_cycles:                 0
% 2.77/1.00  gc_basic_clause_elim:                   0
% 2.77/1.00  forced_gc_time:                         0
% 2.77/1.00  parsing_time:                           0.009
% 2.77/1.00  unif_index_cands_time:                  0.
% 2.77/1.00  unif_index_add_time:                    0.
% 2.77/1.00  orderings_time:                         0.
% 2.77/1.00  out_proof_time:                         0.007
% 2.77/1.00  total_time:                             0.169
% 2.77/1.00  num_of_symbols:                         52
% 2.77/1.00  num_of_terms:                           5895
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing
% 2.77/1.00  
% 2.77/1.00  num_of_splits:                          0
% 2.77/1.00  num_of_split_atoms:                     0
% 2.77/1.00  num_of_reused_defs:                     0
% 2.77/1.00  num_eq_ax_congr_red:                    22
% 2.77/1.00  num_of_sem_filtered_clauses:            1
% 2.77/1.00  num_of_subtypes:                        0
% 2.77/1.00  monotx_restored_types:                  0
% 2.77/1.00  sat_num_of_epr_types:                   0
% 2.77/1.00  sat_num_of_non_cyclic_types:            0
% 2.77/1.00  sat_guarded_non_collapsed_types:        0
% 2.77/1.00  num_pure_diseq_elim:                    0
% 2.77/1.00  simp_replaced_by:                       0
% 2.77/1.00  res_preprocessed:                       121
% 2.77/1.00  prep_upred:                             0
% 2.77/1.00  prep_unflattend:                        12
% 2.77/1.00  smt_new_axioms:                         0
% 2.77/1.00  pred_elim_cands:                        2
% 2.77/1.00  pred_elim:                              3
% 2.77/1.00  pred_elim_cl:                           4
% 2.77/1.00  pred_elim_cycles:                       5
% 2.77/1.00  merged_defs:                            0
% 2.77/1.00  merged_defs_ncl:                        0
% 2.77/1.00  bin_hyper_res:                          0
% 2.77/1.00  prep_cycles:                            4
% 2.77/1.00  pred_elim_time:                         0.004
% 2.77/1.00  splitting_time:                         0.
% 2.77/1.00  sem_filter_time:                        0.
% 2.77/1.00  monotx_time:                            0.
% 2.77/1.00  subtype_inf_time:                       0.
% 2.77/1.00  
% 2.77/1.00  ------ Problem properties
% 2.77/1.00  
% 2.77/1.00  clauses:                                21
% 2.77/1.00  conjectures:                            1
% 2.77/1.00  epr:                                    2
% 2.77/1.00  horn:                                   21
% 2.77/1.00  ground:                                 1
% 2.77/1.00  unary:                                  5
% 2.77/1.00  binary:                                 8
% 2.77/1.00  lits:                                   45
% 2.77/1.00  lits_eq:                                25
% 2.77/1.00  fd_pure:                                0
% 2.77/1.00  fd_pseudo:                              0
% 2.77/1.00  fd_cond:                                0
% 2.77/1.00  fd_pseudo_cond:                         1
% 2.77/1.00  ac_symbols:                             0
% 2.77/1.00  
% 2.77/1.00  ------ Propositional Solver
% 2.77/1.00  
% 2.77/1.00  prop_solver_calls:                      28
% 2.77/1.00  prop_fast_solver_calls:                 719
% 2.77/1.00  smt_solver_calls:                       0
% 2.77/1.00  smt_fast_solver_calls:                  0
% 2.77/1.00  prop_num_of_clauses:                    2236
% 2.77/1.00  prop_preprocess_simplified:             6739
% 2.77/1.00  prop_fo_subsumed:                       9
% 2.77/1.00  prop_solver_time:                       0.
% 2.77/1.00  smt_solver_time:                        0.
% 2.77/1.00  smt_fast_solver_time:                   0.
% 2.77/1.00  prop_fast_solver_time:                  0.
% 2.77/1.00  prop_unsat_core_time:                   0.
% 2.77/1.00  
% 2.77/1.00  ------ QBF
% 2.77/1.00  
% 2.77/1.00  qbf_q_res:                              0
% 2.77/1.00  qbf_num_tautologies:                    0
% 2.77/1.00  qbf_prep_cycles:                        0
% 2.77/1.00  
% 2.77/1.00  ------ BMC1
% 2.77/1.00  
% 2.77/1.00  bmc1_current_bound:                     -1
% 2.77/1.00  bmc1_last_solved_bound:                 -1
% 2.77/1.00  bmc1_unsat_core_size:                   -1
% 2.77/1.00  bmc1_unsat_core_parents_size:           -1
% 2.77/1.00  bmc1_merge_next_fun:                    0
% 2.77/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation
% 2.77/1.00  
% 2.77/1.00  inst_num_of_clauses:                    693
% 2.77/1.00  inst_num_in_passive:                    309
% 2.77/1.00  inst_num_in_active:                     322
% 2.77/1.00  inst_num_in_unprocessed:                62
% 2.77/1.00  inst_num_of_loops:                      330
% 2.77/1.00  inst_num_of_learning_restarts:          0
% 2.77/1.00  inst_num_moves_active_passive:          6
% 2.77/1.00  inst_lit_activity:                      0
% 2.77/1.00  inst_lit_activity_moves:                0
% 2.77/1.00  inst_num_tautologies:                   0
% 2.77/1.00  inst_num_prop_implied:                  0
% 2.77/1.00  inst_num_existing_simplified:           0
% 2.77/1.00  inst_num_eq_res_simplified:             0
% 2.77/1.00  inst_num_child_elim:                    0
% 2.77/1.00  inst_num_of_dismatching_blockings:      81
% 2.77/1.00  inst_num_of_non_proper_insts:           533
% 2.77/1.00  inst_num_of_duplicates:                 0
% 2.77/1.00  inst_inst_num_from_inst_to_res:         0
% 2.77/1.00  inst_dismatching_checking_time:         0.
% 2.77/1.00  
% 2.77/1.00  ------ Resolution
% 2.77/1.00  
% 2.77/1.00  res_num_of_clauses:                     0
% 2.77/1.00  res_num_in_passive:                     0
% 2.77/1.00  res_num_in_active:                      0
% 2.77/1.00  res_num_of_loops:                       125
% 2.77/1.00  res_forward_subset_subsumed:            85
% 2.77/1.00  res_backward_subset_subsumed:           0
% 2.77/1.00  res_forward_subsumed:                   0
% 2.77/1.00  res_backward_subsumed:                  0
% 2.77/1.00  res_forward_subsumption_resolution:     0
% 2.77/1.00  res_backward_subsumption_resolution:    0
% 2.77/1.00  res_clause_to_clause_subsumption:       129
% 2.77/1.00  res_orphan_elimination:                 0
% 2.77/1.00  res_tautology_del:                      51
% 2.77/1.00  res_num_eq_res_simplified:              0
% 2.77/1.00  res_num_sel_changes:                    0
% 2.77/1.00  res_moves_from_active_to_pass:          0
% 2.77/1.00  
% 2.77/1.00  ------ Superposition
% 2.77/1.00  
% 2.77/1.00  sup_time_total:                         0.
% 2.77/1.00  sup_time_generating:                    0.
% 2.77/1.00  sup_time_sim_full:                      0.
% 2.77/1.00  sup_time_sim_immed:                     0.
% 2.77/1.00  
% 2.77/1.00  sup_num_of_clauses:                     72
% 2.77/1.00  sup_num_in_active:                      62
% 2.77/1.00  sup_num_in_passive:                     10
% 2.77/1.00  sup_num_of_loops:                       65
% 2.77/1.00  sup_fw_superposition:                   44
% 2.77/1.00  sup_bw_superposition:                   9
% 2.77/1.00  sup_immediate_simplified:               14
% 2.77/1.00  sup_given_eliminated:                   0
% 2.77/1.00  comparisons_done:                       0
% 2.77/1.00  comparisons_avoided:                    0
% 2.77/1.00  
% 2.77/1.00  ------ Simplifications
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  sim_fw_subset_subsumed:                 1
% 2.77/1.00  sim_bw_subset_subsumed:                 0
% 2.77/1.00  sim_fw_subsumed:                        3
% 2.77/1.00  sim_bw_subsumed:                        0
% 2.77/1.00  sim_fw_subsumption_res:                 0
% 2.77/1.00  sim_bw_subsumption_res:                 0
% 2.77/1.00  sim_tautology_del:                      0
% 2.77/1.00  sim_eq_tautology_del:                   3
% 2.77/1.00  sim_eq_res_simp:                        1
% 2.77/1.00  sim_fw_demodulated:                     6
% 2.77/1.00  sim_bw_demodulated:                     4
% 2.77/1.00  sim_light_normalised:                   11
% 2.77/1.00  sim_joinable_taut:                      0
% 2.77/1.00  sim_joinable_simp:                      0
% 2.77/1.00  sim_ac_normalised:                      0
% 2.77/1.00  sim_smt_subsumption:                    0
% 2.77/1.00  
%------------------------------------------------------------------------------
