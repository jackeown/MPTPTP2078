%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:08 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 638 expanded)
%              Number of clauses        :   89 ( 253 expanded)
%              Number of leaves         :   18 ( 118 expanded)
%              Depth                    :   15
%              Number of atoms          :  328 (1540 expanded)
%              Number of equality atoms :  157 ( 654 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f41])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f34])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1050,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1036,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1037,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2815,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_1037])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_14,c_12,c_10])).

cnf(c_1035,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_3217,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2815,c_1035])).

cnf(c_3398,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1050,c_3217])).

cnf(c_1043,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1482,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_1043])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1046,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1600,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1482,c_1046])).

cnf(c_3838,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3398,c_1600])).

cnf(c_11,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1044,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4160,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3838,c_1044])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_7])).

cnf(c_324,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_12])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_1034,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_1358,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_1034])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1049,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1702,plain,
    ( k3_xboole_0(k2_relat_1(sK2),sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1358,c_1049])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1045,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1599,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1482,c_1045])).

cnf(c_1755,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_1702,c_1599])).

cnf(c_4161,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4160,c_1755])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1173,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_1236,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1416,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_1418,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1416])).

cnf(c_6475,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4161,c_23,c_1174,c_1418])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1051,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6480,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2)
    | r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6475,c_1051])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1038,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3213,plain,
    ( k8_relset_1(X0,sK0,sK2,X1) = k10_relat_1(sK2,X1)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2815,c_1038])).

cnf(c_4036,plain,
    ( k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1050,c_3213])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1042,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4310,plain,
    ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4036,c_1042])).

cnf(c_1237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1519,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_1520,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1519])).

cnf(c_6276,plain,
    ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4310,c_23,c_1418,c_1520])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6285,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6276,c_1047])).

cnf(c_6289,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6285])).

cnf(c_3399,plain,
    ( k7_relat_1(sK2,k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(sK2)))) = sK2
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_3217])).

cnf(c_4884,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_3399])).

cnf(c_4885,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4884,c_1755,c_3838])).

cnf(c_5279,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4885,c_23,c_1174])).

cnf(c_5282,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5279,c_1600])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1039,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2836,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1036,c_1039])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1041,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2070,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1036,c_1041])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1040,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2056,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1036,c_1040])).

cnf(c_21,negated_conjecture,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2412,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_2056,c_21])).

cnf(c_2586,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2070,c_2412])).

cnf(c_2303,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1036,c_1038])).

cnf(c_2626,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2586,c_2303])).

cnf(c_3205,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2836,c_2626])).

cnf(c_1928,plain,
    ( k7_relat_1(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1036,c_1035])).

cnf(c_2410,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1928,c_1600])).

cnf(c_3206,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3205,c_1755,c_2410])).

cnf(c_3207,plain,
    ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3206,c_2836])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6480,c_6289,c_5282,c_3207])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:36:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.29/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/0.93  
% 3.29/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.93  
% 3.29/0.93  ------  iProver source info
% 3.29/0.93  
% 3.29/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.93  git: non_committed_changes: false
% 3.29/0.93  git: last_make_outside_of_git: false
% 3.29/0.93  
% 3.29/0.93  ------ 
% 3.29/0.93  
% 3.29/0.93  ------ Input Options
% 3.29/0.93  
% 3.29/0.93  --out_options                           all
% 3.29/0.93  --tptp_safe_out                         true
% 3.29/0.93  --problem_path                          ""
% 3.29/0.93  --include_path                          ""
% 3.29/0.93  --clausifier                            res/vclausify_rel
% 3.29/0.93  --clausifier_options                    --mode clausify
% 3.29/0.93  --stdin                                 false
% 3.29/0.93  --stats_out                             all
% 3.29/0.93  
% 3.29/0.93  ------ General Options
% 3.29/0.93  
% 3.29/0.93  --fof                                   false
% 3.29/0.93  --time_out_real                         305.
% 3.29/0.93  --time_out_virtual                      -1.
% 3.29/0.93  --symbol_type_check                     false
% 3.29/0.93  --clausify_out                          false
% 3.29/0.93  --sig_cnt_out                           false
% 3.29/0.93  --trig_cnt_out                          false
% 3.29/0.93  --trig_cnt_out_tolerance                1.
% 3.29/0.93  --trig_cnt_out_sk_spl                   false
% 3.29/0.93  --abstr_cl_out                          false
% 3.29/0.93  
% 3.29/0.93  ------ Global Options
% 3.29/0.93  
% 3.29/0.93  --schedule                              default
% 3.29/0.93  --add_important_lit                     false
% 3.29/0.93  --prop_solver_per_cl                    1000
% 3.29/0.93  --min_unsat_core                        false
% 3.29/0.93  --soft_assumptions                      false
% 3.29/0.93  --soft_lemma_size                       3
% 3.29/0.93  --prop_impl_unit_size                   0
% 3.29/0.93  --prop_impl_unit                        []
% 3.29/0.93  --share_sel_clauses                     true
% 3.29/0.93  --reset_solvers                         false
% 3.29/0.93  --bc_imp_inh                            [conj_cone]
% 3.29/0.93  --conj_cone_tolerance                   3.
% 3.29/0.93  --extra_neg_conj                        none
% 3.29/0.93  --large_theory_mode                     true
% 3.29/0.93  --prolific_symb_bound                   200
% 3.29/0.93  --lt_threshold                          2000
% 3.29/0.93  --clause_weak_htbl                      true
% 3.29/0.93  --gc_record_bc_elim                     false
% 3.29/0.93  
% 3.29/0.93  ------ Preprocessing Options
% 3.29/0.93  
% 3.29/0.93  --preprocessing_flag                    true
% 3.29/0.93  --time_out_prep_mult                    0.1
% 3.29/0.93  --splitting_mode                        input
% 3.29/0.93  --splitting_grd                         true
% 3.29/0.93  --splitting_cvd                         false
% 3.29/0.93  --splitting_cvd_svl                     false
% 3.29/0.93  --splitting_nvd                         32
% 3.29/0.93  --sub_typing                            true
% 3.29/0.93  --prep_gs_sim                           true
% 3.29/0.93  --prep_unflatten                        true
% 3.29/0.93  --prep_res_sim                          true
% 3.29/0.93  --prep_upred                            true
% 3.29/0.93  --prep_sem_filter                       exhaustive
% 3.29/0.93  --prep_sem_filter_out                   false
% 3.29/0.93  --pred_elim                             true
% 3.29/0.93  --res_sim_input                         true
% 3.29/0.93  --eq_ax_congr_red                       true
% 3.29/0.93  --pure_diseq_elim                       true
% 3.29/0.93  --brand_transform                       false
% 3.29/0.93  --non_eq_to_eq                          false
% 3.29/0.93  --prep_def_merge                        true
% 3.29/0.93  --prep_def_merge_prop_impl              false
% 3.29/0.93  --prep_def_merge_mbd                    true
% 3.29/0.93  --prep_def_merge_tr_red                 false
% 3.29/0.93  --prep_def_merge_tr_cl                  false
% 3.29/0.93  --smt_preprocessing                     true
% 3.29/0.93  --smt_ac_axioms                         fast
% 3.29/0.93  --preprocessed_out                      false
% 3.29/0.93  --preprocessed_stats                    false
% 3.29/0.93  
% 3.29/0.93  ------ Abstraction refinement Options
% 3.29/0.93  
% 3.29/0.93  --abstr_ref                             []
% 3.29/0.93  --abstr_ref_prep                        false
% 3.29/0.93  --abstr_ref_until_sat                   false
% 3.29/0.93  --abstr_ref_sig_restrict                funpre
% 3.29/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.93  --abstr_ref_under                       []
% 3.29/0.93  
% 3.29/0.93  ------ SAT Options
% 3.29/0.93  
% 3.29/0.93  --sat_mode                              false
% 3.29/0.93  --sat_fm_restart_options                ""
% 3.29/0.93  --sat_gr_def                            false
% 3.29/0.93  --sat_epr_types                         true
% 3.29/0.93  --sat_non_cyclic_types                  false
% 3.29/0.93  --sat_finite_models                     false
% 3.29/0.93  --sat_fm_lemmas                         false
% 3.29/0.93  --sat_fm_prep                           false
% 3.29/0.93  --sat_fm_uc_incr                        true
% 3.29/0.93  --sat_out_model                         small
% 3.29/0.93  --sat_out_clauses                       false
% 3.29/0.93  
% 3.29/0.93  ------ QBF Options
% 3.29/0.93  
% 3.29/0.93  --qbf_mode                              false
% 3.29/0.93  --qbf_elim_univ                         false
% 3.29/0.93  --qbf_dom_inst                          none
% 3.29/0.93  --qbf_dom_pre_inst                      false
% 3.29/0.93  --qbf_sk_in                             false
% 3.29/0.93  --qbf_pred_elim                         true
% 3.29/0.93  --qbf_split                             512
% 3.29/0.93  
% 3.29/0.93  ------ BMC1 Options
% 3.29/0.93  
% 3.29/0.93  --bmc1_incremental                      false
% 3.29/0.93  --bmc1_axioms                           reachable_all
% 3.29/0.93  --bmc1_min_bound                        0
% 3.29/0.93  --bmc1_max_bound                        -1
% 3.29/0.93  --bmc1_max_bound_default                -1
% 3.29/0.93  --bmc1_symbol_reachability              true
% 3.29/0.93  --bmc1_property_lemmas                  false
% 3.29/0.93  --bmc1_k_induction                      false
% 3.29/0.93  --bmc1_non_equiv_states                 false
% 3.29/0.93  --bmc1_deadlock                         false
% 3.29/0.93  --bmc1_ucm                              false
% 3.29/0.93  --bmc1_add_unsat_core                   none
% 3.29/0.93  --bmc1_unsat_core_children              false
% 3.29/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.93  --bmc1_out_stat                         full
% 3.29/0.93  --bmc1_ground_init                      false
% 3.29/0.93  --bmc1_pre_inst_next_state              false
% 3.29/0.93  --bmc1_pre_inst_state                   false
% 3.29/0.93  --bmc1_pre_inst_reach_state             false
% 3.29/0.93  --bmc1_out_unsat_core                   false
% 3.29/0.93  --bmc1_aig_witness_out                  false
% 3.29/0.93  --bmc1_verbose                          false
% 3.29/0.93  --bmc1_dump_clauses_tptp                false
% 3.29/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.93  --bmc1_dump_file                        -
% 3.29/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.93  --bmc1_ucm_extend_mode                  1
% 3.29/0.93  --bmc1_ucm_init_mode                    2
% 3.29/0.93  --bmc1_ucm_cone_mode                    none
% 3.29/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.93  --bmc1_ucm_relax_model                  4
% 3.29/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.93  --bmc1_ucm_layered_model                none
% 3.29/0.93  --bmc1_ucm_max_lemma_size               10
% 3.29/0.93  
% 3.29/0.93  ------ AIG Options
% 3.29/0.93  
% 3.29/0.93  --aig_mode                              false
% 3.29/0.93  
% 3.29/0.93  ------ Instantiation Options
% 3.29/0.93  
% 3.29/0.93  --instantiation_flag                    true
% 3.29/0.93  --inst_sos_flag                         false
% 3.29/0.93  --inst_sos_phase                        true
% 3.29/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.93  --inst_lit_sel_side                     num_symb
% 3.29/0.93  --inst_solver_per_active                1400
% 3.29/0.93  --inst_solver_calls_frac                1.
% 3.29/0.93  --inst_passive_queue_type               priority_queues
% 3.29/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.93  --inst_passive_queues_freq              [25;2]
% 3.29/0.93  --inst_dismatching                      true
% 3.29/0.93  --inst_eager_unprocessed_to_passive     true
% 3.29/0.93  --inst_prop_sim_given                   true
% 3.29/0.93  --inst_prop_sim_new                     false
% 3.29/0.93  --inst_subs_new                         false
% 3.29/0.93  --inst_eq_res_simp                      false
% 3.29/0.93  --inst_subs_given                       false
% 3.29/0.93  --inst_orphan_elimination               true
% 3.29/0.93  --inst_learning_loop_flag               true
% 3.29/0.93  --inst_learning_start                   3000
% 3.29/0.93  --inst_learning_factor                  2
% 3.29/0.93  --inst_start_prop_sim_after_learn       3
% 3.29/0.93  --inst_sel_renew                        solver
% 3.29/0.93  --inst_lit_activity_flag                true
% 3.29/0.93  --inst_restr_to_given                   false
% 3.29/0.93  --inst_activity_threshold               500
% 3.29/0.93  --inst_out_proof                        true
% 3.29/0.93  
% 3.29/0.93  ------ Resolution Options
% 3.29/0.93  
% 3.29/0.93  --resolution_flag                       true
% 3.29/0.93  --res_lit_sel                           adaptive
% 3.29/0.93  --res_lit_sel_side                      none
% 3.29/0.93  --res_ordering                          kbo
% 3.29/0.93  --res_to_prop_solver                    active
% 3.29/0.93  --res_prop_simpl_new                    false
% 3.29/0.93  --res_prop_simpl_given                  true
% 3.29/0.93  --res_passive_queue_type                priority_queues
% 3.29/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.93  --res_passive_queues_freq               [15;5]
% 3.29/0.93  --res_forward_subs                      full
% 3.29/0.93  --res_backward_subs                     full
% 3.29/0.93  --res_forward_subs_resolution           true
% 3.29/0.93  --res_backward_subs_resolution          true
% 3.29/0.93  --res_orphan_elimination                true
% 3.29/0.93  --res_time_limit                        2.
% 3.29/0.93  --res_out_proof                         true
% 3.29/0.93  
% 3.29/0.93  ------ Superposition Options
% 3.29/0.93  
% 3.29/0.93  --superposition_flag                    true
% 3.29/0.93  --sup_passive_queue_type                priority_queues
% 3.29/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.93  --demod_completeness_check              fast
% 3.29/0.93  --demod_use_ground                      true
% 3.29/0.93  --sup_to_prop_solver                    passive
% 3.29/0.93  --sup_prop_simpl_new                    true
% 3.29/0.93  --sup_prop_simpl_given                  true
% 3.29/0.93  --sup_fun_splitting                     false
% 3.29/0.93  --sup_smt_interval                      50000
% 3.29/0.93  
% 3.29/0.93  ------ Superposition Simplification Setup
% 3.29/0.93  
% 3.29/0.93  --sup_indices_passive                   []
% 3.29/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.93  --sup_full_bw                           [BwDemod]
% 3.29/0.93  --sup_immed_triv                        [TrivRules]
% 3.29/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.93  --sup_immed_bw_main                     []
% 3.29/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.93  
% 3.29/0.93  ------ Combination Options
% 3.29/0.93  
% 3.29/0.93  --comb_res_mult                         3
% 3.29/0.93  --comb_sup_mult                         2
% 3.29/0.93  --comb_inst_mult                        10
% 3.29/0.93  
% 3.29/0.93  ------ Debug Options
% 3.29/0.93  
% 3.29/0.93  --dbg_backtrace                         false
% 3.29/0.93  --dbg_dump_prop_clauses                 false
% 3.29/0.93  --dbg_dump_prop_clauses_file            -
% 3.29/0.93  --dbg_out_stat                          false
% 3.29/0.93  ------ Parsing...
% 3.29/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.93  
% 3.29/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.29/0.93  
% 3.29/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.93  
% 3.29/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.93  ------ Proving...
% 3.29/0.93  ------ Problem Properties 
% 3.29/0.93  
% 3.29/0.93  
% 3.29/0.93  clauses                                 19
% 3.29/0.93  conjectures                             2
% 3.29/0.93  EPR                                     2
% 3.29/0.93  Horn                                    19
% 3.29/0.93  unary                                   2
% 3.29/0.93  binary                                  14
% 3.29/0.93  lits                                    39
% 3.29/0.93  lits eq                                 11
% 3.29/0.93  fd_pure                                 0
% 3.29/0.93  fd_pseudo                               0
% 3.29/0.93  fd_cond                                 0
% 3.29/0.93  fd_pseudo_cond                          1
% 3.29/0.93  AC symbols                              0
% 3.29/0.93  
% 3.29/0.93  ------ Schedule dynamic 5 is on 
% 3.29/0.93  
% 3.29/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.29/0.93  
% 3.29/0.93  
% 3.29/0.93  ------ 
% 3.29/0.93  Current options:
% 3.29/0.93  ------ 
% 3.29/0.93  
% 3.29/0.93  ------ Input Options
% 3.29/0.93  
% 3.29/0.93  --out_options                           all
% 3.29/0.93  --tptp_safe_out                         true
% 3.29/0.93  --problem_path                          ""
% 3.29/0.93  --include_path                          ""
% 3.29/0.93  --clausifier                            res/vclausify_rel
% 3.29/0.93  --clausifier_options                    --mode clausify
% 3.29/0.93  --stdin                                 false
% 3.29/0.93  --stats_out                             all
% 3.29/0.93  
% 3.29/0.93  ------ General Options
% 3.29/0.93  
% 3.29/0.93  --fof                                   false
% 3.29/0.93  --time_out_real                         305.
% 3.29/0.93  --time_out_virtual                      -1.
% 3.29/0.93  --symbol_type_check                     false
% 3.29/0.93  --clausify_out                          false
% 3.29/0.93  --sig_cnt_out                           false
% 3.29/0.93  --trig_cnt_out                          false
% 3.29/0.93  --trig_cnt_out_tolerance                1.
% 3.29/0.93  --trig_cnt_out_sk_spl                   false
% 3.29/0.93  --abstr_cl_out                          false
% 3.29/0.93  
% 3.29/0.93  ------ Global Options
% 3.29/0.93  
% 3.29/0.93  --schedule                              default
% 3.29/0.93  --add_important_lit                     false
% 3.29/0.93  --prop_solver_per_cl                    1000
% 3.29/0.93  --min_unsat_core                        false
% 3.29/0.93  --soft_assumptions                      false
% 3.29/0.93  --soft_lemma_size                       3
% 3.29/0.93  --prop_impl_unit_size                   0
% 3.29/0.93  --prop_impl_unit                        []
% 3.29/0.93  --share_sel_clauses                     true
% 3.29/0.93  --reset_solvers                         false
% 3.29/0.93  --bc_imp_inh                            [conj_cone]
% 3.29/0.93  --conj_cone_tolerance                   3.
% 3.29/0.93  --extra_neg_conj                        none
% 3.29/0.93  --large_theory_mode                     true
% 3.29/0.93  --prolific_symb_bound                   200
% 3.29/0.93  --lt_threshold                          2000
% 3.29/0.93  --clause_weak_htbl                      true
% 3.29/0.93  --gc_record_bc_elim                     false
% 3.29/0.93  
% 3.29/0.93  ------ Preprocessing Options
% 3.29/0.93  
% 3.29/0.93  --preprocessing_flag                    true
% 3.29/0.93  --time_out_prep_mult                    0.1
% 3.29/0.93  --splitting_mode                        input
% 3.29/0.93  --splitting_grd                         true
% 3.29/0.93  --splitting_cvd                         false
% 3.29/0.93  --splitting_cvd_svl                     false
% 3.29/0.93  --splitting_nvd                         32
% 3.29/0.93  --sub_typing                            true
% 3.29/0.93  --prep_gs_sim                           true
% 3.29/0.93  --prep_unflatten                        true
% 3.29/0.93  --prep_res_sim                          true
% 3.29/0.93  --prep_upred                            true
% 3.29/0.93  --prep_sem_filter                       exhaustive
% 3.29/0.93  --prep_sem_filter_out                   false
% 3.29/0.93  --pred_elim                             true
% 3.29/0.93  --res_sim_input                         true
% 3.29/0.93  --eq_ax_congr_red                       true
% 3.29/0.93  --pure_diseq_elim                       true
% 3.29/0.93  --brand_transform                       false
% 3.29/0.93  --non_eq_to_eq                          false
% 3.29/0.93  --prep_def_merge                        true
% 3.29/0.93  --prep_def_merge_prop_impl              false
% 3.29/0.93  --prep_def_merge_mbd                    true
% 3.29/0.93  --prep_def_merge_tr_red                 false
% 3.29/0.93  --prep_def_merge_tr_cl                  false
% 3.29/0.93  --smt_preprocessing                     true
% 3.29/0.93  --smt_ac_axioms                         fast
% 3.29/0.93  --preprocessed_out                      false
% 3.29/0.93  --preprocessed_stats                    false
% 3.29/0.93  
% 3.29/0.93  ------ Abstraction refinement Options
% 3.29/0.93  
% 3.29/0.93  --abstr_ref                             []
% 3.29/0.93  --abstr_ref_prep                        false
% 3.29/0.93  --abstr_ref_until_sat                   false
% 3.29/0.93  --abstr_ref_sig_restrict                funpre
% 3.29/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.93  --abstr_ref_under                       []
% 3.29/0.93  
% 3.29/0.93  ------ SAT Options
% 3.29/0.93  
% 3.29/0.93  --sat_mode                              false
% 3.29/0.93  --sat_fm_restart_options                ""
% 3.29/0.93  --sat_gr_def                            false
% 3.29/0.93  --sat_epr_types                         true
% 3.29/0.93  --sat_non_cyclic_types                  false
% 3.29/0.93  --sat_finite_models                     false
% 3.29/0.93  --sat_fm_lemmas                         false
% 3.29/0.93  --sat_fm_prep                           false
% 3.29/0.93  --sat_fm_uc_incr                        true
% 3.29/0.93  --sat_out_model                         small
% 3.29/0.93  --sat_out_clauses                       false
% 3.29/0.93  
% 3.29/0.93  ------ QBF Options
% 3.29/0.93  
% 3.29/0.93  --qbf_mode                              false
% 3.29/0.93  --qbf_elim_univ                         false
% 3.29/0.93  --qbf_dom_inst                          none
% 3.29/0.93  --qbf_dom_pre_inst                      false
% 3.29/0.93  --qbf_sk_in                             false
% 3.29/0.93  --qbf_pred_elim                         true
% 3.29/0.93  --qbf_split                             512
% 3.29/0.93  
% 3.29/0.93  ------ BMC1 Options
% 3.29/0.93  
% 3.29/0.93  --bmc1_incremental                      false
% 3.29/0.93  --bmc1_axioms                           reachable_all
% 3.29/0.93  --bmc1_min_bound                        0
% 3.29/0.93  --bmc1_max_bound                        -1
% 3.29/0.93  --bmc1_max_bound_default                -1
% 3.29/0.93  --bmc1_symbol_reachability              true
% 3.29/0.93  --bmc1_property_lemmas                  false
% 3.29/0.93  --bmc1_k_induction                      false
% 3.29/0.93  --bmc1_non_equiv_states                 false
% 3.29/0.93  --bmc1_deadlock                         false
% 3.29/0.93  --bmc1_ucm                              false
% 3.29/0.93  --bmc1_add_unsat_core                   none
% 3.29/0.93  --bmc1_unsat_core_children              false
% 3.29/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.93  --bmc1_out_stat                         full
% 3.29/0.93  --bmc1_ground_init                      false
% 3.29/0.93  --bmc1_pre_inst_next_state              false
% 3.29/0.93  --bmc1_pre_inst_state                   false
% 3.29/0.93  --bmc1_pre_inst_reach_state             false
% 3.29/0.93  --bmc1_out_unsat_core                   false
% 3.29/0.93  --bmc1_aig_witness_out                  false
% 3.29/0.93  --bmc1_verbose                          false
% 3.29/0.93  --bmc1_dump_clauses_tptp                false
% 3.29/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.93  --bmc1_dump_file                        -
% 3.29/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.93  --bmc1_ucm_extend_mode                  1
% 3.29/0.93  --bmc1_ucm_init_mode                    2
% 3.29/0.93  --bmc1_ucm_cone_mode                    none
% 3.29/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.93  --bmc1_ucm_relax_model                  4
% 3.29/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.93  --bmc1_ucm_layered_model                none
% 3.29/0.93  --bmc1_ucm_max_lemma_size               10
% 3.29/0.93  
% 3.29/0.93  ------ AIG Options
% 3.29/0.93  
% 3.29/0.93  --aig_mode                              false
% 3.29/0.93  
% 3.29/0.93  ------ Instantiation Options
% 3.29/0.93  
% 3.29/0.93  --instantiation_flag                    true
% 3.29/0.93  --inst_sos_flag                         false
% 3.29/0.93  --inst_sos_phase                        true
% 3.29/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.93  --inst_lit_sel_side                     none
% 3.29/0.93  --inst_solver_per_active                1400
% 3.29/0.93  --inst_solver_calls_frac                1.
% 3.29/0.93  --inst_passive_queue_type               priority_queues
% 3.29/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.93  --inst_passive_queues_freq              [25;2]
% 3.29/0.93  --inst_dismatching                      true
% 3.29/0.93  --inst_eager_unprocessed_to_passive     true
% 3.29/0.93  --inst_prop_sim_given                   true
% 3.29/0.93  --inst_prop_sim_new                     false
% 3.29/0.93  --inst_subs_new                         false
% 3.29/0.93  --inst_eq_res_simp                      false
% 3.29/0.93  --inst_subs_given                       false
% 3.29/0.93  --inst_orphan_elimination               true
% 3.29/0.93  --inst_learning_loop_flag               true
% 3.29/0.93  --inst_learning_start                   3000
% 3.29/0.93  --inst_learning_factor                  2
% 3.29/0.93  --inst_start_prop_sim_after_learn       3
% 3.29/0.93  --inst_sel_renew                        solver
% 3.29/0.93  --inst_lit_activity_flag                true
% 3.29/0.93  --inst_restr_to_given                   false
% 3.29/0.93  --inst_activity_threshold               500
% 3.29/0.93  --inst_out_proof                        true
% 3.29/0.93  
% 3.29/0.93  ------ Resolution Options
% 3.29/0.93  
% 3.29/0.93  --resolution_flag                       false
% 3.29/0.93  --res_lit_sel                           adaptive
% 3.29/0.93  --res_lit_sel_side                      none
% 3.29/0.93  --res_ordering                          kbo
% 3.29/0.93  --res_to_prop_solver                    active
% 3.29/0.93  --res_prop_simpl_new                    false
% 3.29/0.93  --res_prop_simpl_given                  true
% 3.29/0.93  --res_passive_queue_type                priority_queues
% 3.29/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.93  --res_passive_queues_freq               [15;5]
% 3.29/0.93  --res_forward_subs                      full
% 3.29/0.93  --res_backward_subs                     full
% 3.29/0.93  --res_forward_subs_resolution           true
% 3.29/0.93  --res_backward_subs_resolution          true
% 3.29/0.93  --res_orphan_elimination                true
% 3.29/0.93  --res_time_limit                        2.
% 3.29/0.93  --res_out_proof                         true
% 3.29/0.93  
% 3.29/0.93  ------ Superposition Options
% 3.29/0.93  
% 3.29/0.93  --superposition_flag                    true
% 3.29/0.93  --sup_passive_queue_type                priority_queues
% 3.29/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.93  --demod_completeness_check              fast
% 3.29/0.93  --demod_use_ground                      true
% 3.29/0.93  --sup_to_prop_solver                    passive
% 3.29/0.93  --sup_prop_simpl_new                    true
% 3.29/0.93  --sup_prop_simpl_given                  true
% 3.29/0.93  --sup_fun_splitting                     false
% 3.29/0.93  --sup_smt_interval                      50000
% 3.29/0.93  
% 3.29/0.93  ------ Superposition Simplification Setup
% 3.29/0.93  
% 3.29/0.93  --sup_indices_passive                   []
% 3.29/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.93  --sup_full_bw                           [BwDemod]
% 3.29/0.93  --sup_immed_triv                        [TrivRules]
% 3.29/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.93  --sup_immed_bw_main                     []
% 3.29/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.93  
% 3.29/0.93  ------ Combination Options
% 3.29/0.93  
% 3.29/0.93  --comb_res_mult                         3
% 3.29/0.93  --comb_sup_mult                         2
% 3.29/0.93  --comb_inst_mult                        10
% 3.29/0.93  
% 3.29/0.93  ------ Debug Options
% 3.29/0.93  
% 3.29/0.93  --dbg_backtrace                         false
% 3.29/0.93  --dbg_dump_prop_clauses                 false
% 3.29/0.93  --dbg_dump_prop_clauses_file            -
% 3.29/0.93  --dbg_out_stat                          false
% 3.29/0.93  
% 3.29/0.93  
% 3.29/0.93  
% 3.29/0.93  
% 3.29/0.93  ------ Proving...
% 3.29/0.93  
% 3.29/0.93  
% 3.29/0.93  % SZS status Theorem for theBenchmark.p
% 3.29/0.93  
% 3.29/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.93  
% 3.29/0.93  fof(f1,axiom,(
% 3.29/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f37,plain,(
% 3.29/0.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.29/0.93    inference(nnf_transformation,[],[f1])).
% 3.29/0.93  
% 3.29/0.93  fof(f38,plain,(
% 3.29/0.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.29/0.93    inference(flattening,[],[f37])).
% 3.29/0.93  
% 3.29/0.93  fof(f44,plain,(
% 3.29/0.93    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.29/0.93    inference(cnf_transformation,[],[f38])).
% 3.29/0.93  
% 3.29/0.93  fof(f66,plain,(
% 3.29/0.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.29/0.93    inference(equality_resolution,[],[f44])).
% 3.29/0.93  
% 3.29/0.93  fof(f17,conjecture,(
% 3.29/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f18,negated_conjecture,(
% 3.29/0.93    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.29/0.93    inference(negated_conjecture,[],[f17])).
% 3.29/0.93  
% 3.29/0.93  fof(f36,plain,(
% 3.29/0.93    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.29/0.93    inference(ennf_transformation,[],[f18])).
% 3.29/0.93  
% 3.29/0.93  fof(f41,plain,(
% 3.29/0.93    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 3.29/0.93    introduced(choice_axiom,[])).
% 3.29/0.93  
% 3.29/0.93  fof(f42,plain,(
% 3.29/0.93    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.29/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f41])).
% 3.29/0.93  
% 3.29/0.93  fof(f64,plain,(
% 3.29/0.93    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.29/0.93    inference(cnf_transformation,[],[f42])).
% 3.29/0.93  
% 3.29/0.93  fof(f16,axiom,(
% 3.29/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f34,plain,(
% 3.29/0.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.29/0.93    inference(ennf_transformation,[],[f16])).
% 3.29/0.93  
% 3.29/0.93  fof(f35,plain,(
% 3.29/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.29/0.93    inference(flattening,[],[f34])).
% 3.29/0.93  
% 3.29/0.93  fof(f63,plain,(
% 3.29/0.93    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f35])).
% 3.29/0.93  
% 3.29/0.93  fof(f10,axiom,(
% 3.29/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f28,plain,(
% 3.29/0.93    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.93    inference(ennf_transformation,[],[f10])).
% 3.29/0.93  
% 3.29/0.93  fof(f56,plain,(
% 3.29/0.93    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f28])).
% 3.29/0.93  
% 3.29/0.93  fof(f7,axiom,(
% 3.29/0.93    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f23,plain,(
% 3.29/0.93    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.29/0.93    inference(ennf_transformation,[],[f7])).
% 3.29/0.93  
% 3.29/0.93  fof(f24,plain,(
% 3.29/0.93    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.29/0.93    inference(flattening,[],[f23])).
% 3.29/0.93  
% 3.29/0.93  fof(f53,plain,(
% 3.29/0.93    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.29/0.93    inference(cnf_transformation,[],[f24])).
% 3.29/0.93  
% 3.29/0.93  fof(f9,axiom,(
% 3.29/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f27,plain,(
% 3.29/0.93    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.93    inference(ennf_transformation,[],[f9])).
% 3.29/0.93  
% 3.29/0.93  fof(f55,plain,(
% 3.29/0.93    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f27])).
% 3.29/0.93  
% 3.29/0.93  fof(f5,axiom,(
% 3.29/0.93    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f21,plain,(
% 3.29/0.93    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.29/0.93    inference(ennf_transformation,[],[f5])).
% 3.29/0.93  
% 3.29/0.93  fof(f51,plain,(
% 3.29/0.93    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.29/0.93    inference(cnf_transformation,[],[f21])).
% 3.29/0.93  
% 3.29/0.93  fof(f8,axiom,(
% 3.29/0.93    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f25,plain,(
% 3.29/0.93    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.29/0.93    inference(ennf_transformation,[],[f8])).
% 3.29/0.93  
% 3.29/0.93  fof(f26,plain,(
% 3.29/0.93    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.29/0.93    inference(flattening,[],[f25])).
% 3.29/0.93  
% 3.29/0.93  fof(f54,plain,(
% 3.29/0.93    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.29/0.93    inference(cnf_transformation,[],[f26])).
% 3.29/0.93  
% 3.29/0.93  fof(f57,plain,(
% 3.29/0.93    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f28])).
% 3.29/0.93  
% 3.29/0.93  fof(f4,axiom,(
% 3.29/0.93    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f20,plain,(
% 3.29/0.93    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.29/0.93    inference(ennf_transformation,[],[f4])).
% 3.29/0.93  
% 3.29/0.93  fof(f40,plain,(
% 3.29/0.93    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.29/0.93    inference(nnf_transformation,[],[f20])).
% 3.29/0.93  
% 3.29/0.93  fof(f49,plain,(
% 3.29/0.93    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.29/0.93    inference(cnf_transformation,[],[f40])).
% 3.29/0.93  
% 3.29/0.93  fof(f2,axiom,(
% 3.29/0.93    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f19,plain,(
% 3.29/0.93    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.29/0.93    inference(ennf_transformation,[],[f2])).
% 3.29/0.93  
% 3.29/0.93  fof(f46,plain,(
% 3.29/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.29/0.93    inference(cnf_transformation,[],[f19])).
% 3.29/0.93  
% 3.29/0.93  fof(f6,axiom,(
% 3.29/0.93    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f22,plain,(
% 3.29/0.93    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.29/0.93    inference(ennf_transformation,[],[f6])).
% 3.29/0.93  
% 3.29/0.93  fof(f52,plain,(
% 3.29/0.93    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.29/0.93    inference(cnf_transformation,[],[f22])).
% 3.29/0.93  
% 3.29/0.93  fof(f45,plain,(
% 3.29/0.93    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.29/0.93    inference(cnf_transformation,[],[f38])).
% 3.29/0.93  
% 3.29/0.93  fof(f15,axiom,(
% 3.29/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f33,plain,(
% 3.29/0.93    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.93    inference(ennf_transformation,[],[f15])).
% 3.29/0.93  
% 3.29/0.93  fof(f62,plain,(
% 3.29/0.93    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f33])).
% 3.29/0.93  
% 3.29/0.93  fof(f11,axiom,(
% 3.29/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f29,plain,(
% 3.29/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.93    inference(ennf_transformation,[],[f11])).
% 3.29/0.93  
% 3.29/0.93  fof(f58,plain,(
% 3.29/0.93    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f29])).
% 3.29/0.93  
% 3.29/0.93  fof(f3,axiom,(
% 3.29/0.93    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f39,plain,(
% 3.29/0.93    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.29/0.93    inference(nnf_transformation,[],[f3])).
% 3.29/0.93  
% 3.29/0.93  fof(f47,plain,(
% 3.29/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f39])).
% 3.29/0.93  
% 3.29/0.93  fof(f14,axiom,(
% 3.29/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f32,plain,(
% 3.29/0.93    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.93    inference(ennf_transformation,[],[f14])).
% 3.29/0.93  
% 3.29/0.93  fof(f61,plain,(
% 3.29/0.93    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f32])).
% 3.29/0.93  
% 3.29/0.93  fof(f12,axiom,(
% 3.29/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f30,plain,(
% 3.29/0.93    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.93    inference(ennf_transformation,[],[f12])).
% 3.29/0.93  
% 3.29/0.93  fof(f59,plain,(
% 3.29/0.93    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f30])).
% 3.29/0.93  
% 3.29/0.93  fof(f13,axiom,(
% 3.29/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.29/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.93  
% 3.29/0.93  fof(f31,plain,(
% 3.29/0.93    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.93    inference(ennf_transformation,[],[f13])).
% 3.29/0.93  
% 3.29/0.93  fof(f60,plain,(
% 3.29/0.93    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.93    inference(cnf_transformation,[],[f31])).
% 3.29/0.93  
% 3.29/0.93  fof(f65,plain,(
% 3.29/0.93    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 3.29/0.93    inference(cnf_transformation,[],[f42])).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1,plain,
% 3.29/0.93      ( r1_tarski(X0,X0) ),
% 3.29/0.93      inference(cnf_transformation,[],[f66]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1050,plain,
% 3.29/0.93      ( r1_tarski(X0,X0) = iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_22,negated_conjecture,
% 3.29/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.29/0.93      inference(cnf_transformation,[],[f64]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1036,plain,
% 3.29/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_20,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.29/0.93      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.29/0.93      inference(cnf_transformation,[],[f63]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1037,plain,
% 3.29/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.29/0.93      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.29/0.93      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_2815,plain,
% 3.29/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) = iProver_top
% 3.29/0.93      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1036,c_1037]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_14,plain,
% 3.29/0.93      ( v4_relat_1(X0,X1)
% 3.29/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.29/0.93      inference(cnf_transformation,[],[f56]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_10,plain,
% 3.29/0.93      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.29/0.93      inference(cnf_transformation,[],[f53]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_300,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | ~ v1_relat_1(X0)
% 3.29/0.93      | k7_relat_1(X0,X1) = X0 ),
% 3.29/0.93      inference(resolution,[status(thm)],[c_14,c_10]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_12,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | v1_relat_1(X0) ),
% 3.29/0.93      inference(cnf_transformation,[],[f55]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_304,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | k7_relat_1(X0,X1) = X0 ),
% 3.29/0.93      inference(global_propositional_subsumption,
% 3.29/0.93                [status(thm)],
% 3.29/0.93                [c_300,c_14,c_12,c_10]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1035,plain,
% 3.29/0.93      ( k7_relat_1(X0,X1) = X0
% 3.29/0.93      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_3217,plain,
% 3.29/0.93      ( k7_relat_1(sK2,X0) = sK2
% 3.29/0.93      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_2815,c_1035]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_3398,plain,
% 3.29/0.93      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1050,c_3217]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1043,plain,
% 3.29/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.29/0.93      | v1_relat_1(X0) = iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1482,plain,
% 3.29/0.93      ( v1_relat_1(sK2) = iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1036,c_1043]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_8,plain,
% 3.29/0.93      ( ~ v1_relat_1(X0)
% 3.29/0.93      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.29/0.93      inference(cnf_transformation,[],[f51]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1046,plain,
% 3.29/0.93      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.29/0.93      | v1_relat_1(X0) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1600,plain,
% 3.29/0.93      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1482,c_1046]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_3838,plain,
% 3.29/0.93      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_3398,c_1600]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_11,plain,
% 3.29/0.93      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 3.29/0.93      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.29/0.93      | ~ v1_relat_1(X1) ),
% 3.29/0.93      inference(cnf_transformation,[],[f54]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1044,plain,
% 3.29/0.93      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 3.29/0.93      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 3.29/0.93      | v1_relat_1(X1) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_4160,plain,
% 3.29/0.93      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
% 3.29/0.93      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.29/0.93      | v1_relat_1(sK2) != iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_3838,c_1044]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_13,plain,
% 3.29/0.93      ( v5_relat_1(X0,X1)
% 3.29/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.29/0.93      inference(cnf_transformation,[],[f57]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_7,plain,
% 3.29/0.93      ( ~ v5_relat_1(X0,X1)
% 3.29/0.93      | r1_tarski(k2_relat_1(X0),X1)
% 3.29/0.93      | ~ v1_relat_1(X0) ),
% 3.29/0.93      inference(cnf_transformation,[],[f49]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_320,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | r1_tarski(k2_relat_1(X0),X2)
% 3.29/0.93      | ~ v1_relat_1(X0) ),
% 3.29/0.93      inference(resolution,[status(thm)],[c_13,c_7]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_324,plain,
% 3.29/0.93      ( r1_tarski(k2_relat_1(X0),X2)
% 3.29/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.29/0.93      inference(global_propositional_subsumption,
% 3.29/0.93                [status(thm)],
% 3.29/0.93                [c_320,c_12]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_325,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.29/0.93      inference(renaming,[status(thm)],[c_324]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1034,plain,
% 3.29/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.29/0.93      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1358,plain,
% 3.29/0.93      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1036,c_1034]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_3,plain,
% 3.29/0.93      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.29/0.93      inference(cnf_transformation,[],[f46]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1049,plain,
% 3.29/0.93      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1702,plain,
% 3.29/0.93      ( k3_xboole_0(k2_relat_1(sK2),sK0) = k2_relat_1(sK2) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1358,c_1049]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_9,plain,
% 3.29/0.93      ( ~ v1_relat_1(X0)
% 3.29/0.93      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 3.29/0.93      inference(cnf_transformation,[],[f52]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1045,plain,
% 3.29/0.93      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 3.29/0.93      | v1_relat_1(X0) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1599,plain,
% 3.29/0.93      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1482,c_1045]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1755,plain,
% 3.29/0.93      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK0) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1702,c_1599]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_4161,plain,
% 3.29/0.93      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) = iProver_top
% 3.29/0.93      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.29/0.93      | v1_relat_1(sK2) != iProver_top ),
% 3.29/0.93      inference(light_normalisation,[status(thm)],[c_4160,c_1755]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_23,plain,
% 3.29/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1173,plain,
% 3.29/0.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.29/0.93      | v1_relat_1(sK2) ),
% 3.29/0.93      inference(instantiation,[status(thm)],[c_12]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1174,plain,
% 3.29/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.29/0.93      | v1_relat_1(sK2) = iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1236,plain,
% 3.29/0.93      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 3.29/0.93      inference(instantiation,[status(thm)],[c_1]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1416,plain,
% 3.29/0.93      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 3.29/0.93      inference(instantiation,[status(thm)],[c_1236]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1418,plain,
% 3.29/0.93      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_1416]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_6475,plain,
% 3.29/0.93      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) = iProver_top ),
% 3.29/0.93      inference(global_propositional_subsumption,
% 3.29/0.93                [status(thm)],
% 3.29/0.93                [c_4161,c_23,c_1174,c_1418]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_0,plain,
% 3.29/0.93      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.29/0.93      inference(cnf_transformation,[],[f45]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1051,plain,
% 3.29/0.93      ( X0 = X1
% 3.29/0.93      | r1_tarski(X0,X1) != iProver_top
% 3.29/0.93      | r1_tarski(X1,X0) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_6480,plain,
% 3.29/0.93      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2)
% 3.29/0.93      | r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) != iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_6475,c_1051]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_19,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.29/0.93      inference(cnf_transformation,[],[f62]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1038,plain,
% 3.29/0.93      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.29/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_3213,plain,
% 3.29/0.93      ( k8_relset_1(X0,sK0,sK2,X1) = k10_relat_1(sK2,X1)
% 3.29/0.93      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_2815,c_1038]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_4036,plain,
% 3.29/0.93      ( k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1050,c_3213]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_15,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 3.29/0.93      inference(cnf_transformation,[],[f58]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1042,plain,
% 3.29/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.29/0.93      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_4310,plain,
% 3.29/0.93      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top
% 3.29/0.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) != iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_4036,c_1042]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1237,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 3.29/0.93      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 3.29/0.93      inference(instantiation,[status(thm)],[c_20]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1519,plain,
% 3.29/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
% 3.29/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.29/0.93      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 3.29/0.93      inference(instantiation,[status(thm)],[c_1237]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1520,plain,
% 3.29/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) = iProver_top
% 3.29/0.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.29/0.93      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_1519]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_6276,plain,
% 3.29/0.93      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
% 3.29/0.93      inference(global_propositional_subsumption,
% 3.29/0.93                [status(thm)],
% 3.29/0.93                [c_4310,c_23,c_1418,c_1520]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_5,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.29/0.93      inference(cnf_transformation,[],[f47]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1047,plain,
% 3.29/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.29/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_6285,plain,
% 3.29/0.93      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_6276,c_1047]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_6289,plain,
% 3.29/0.93      ( r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) = iProver_top ),
% 3.29/0.93      inference(instantiation,[status(thm)],[c_6285]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_3399,plain,
% 3.29/0.93      ( k7_relat_1(sK2,k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(sK2)))) = sK2
% 3.29/0.93      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
% 3.29/0.93      | v1_relat_1(X0) != iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1044,c_3217]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_4884,plain,
% 3.29/0.93      ( k7_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))) = sK2
% 3.29/0.93      | v1_relat_1(sK2) != iProver_top ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1050,c_3399]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_4885,plain,
% 3.29/0.93      ( k7_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK2
% 3.29/0.93      | v1_relat_1(sK2) != iProver_top ),
% 3.29/0.93      inference(light_normalisation,[status(thm)],[c_4884,c_1755,c_3838]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_5279,plain,
% 3.29/0.93      ( k7_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK2 ),
% 3.29/0.93      inference(global_propositional_subsumption,
% 3.29/0.93                [status(thm)],
% 3.29/0.93                [c_4885,c_23,c_1174]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_5282,plain,
% 3.29/0.93      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k2_relat_1(sK2) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_5279,c_1600]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_18,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.29/0.93      inference(cnf_transformation,[],[f61]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1039,plain,
% 3.29/0.93      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.29/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_2836,plain,
% 3.29/0.93      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1036,c_1039]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_16,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.29/0.93      inference(cnf_transformation,[],[f59]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1041,plain,
% 3.29/0.93      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.29/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_2070,plain,
% 3.29/0.93      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1036,c_1041]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_17,plain,
% 3.29/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.93      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.29/0.93      inference(cnf_transformation,[],[f60]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1040,plain,
% 3.29/0.93      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.29/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.29/0.93      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_2056,plain,
% 3.29/0.93      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1036,c_1040]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_21,negated_conjecture,
% 3.29/0.93      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 3.29/0.93      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
% 3.29/0.93      inference(cnf_transformation,[],[f65]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_2412,plain,
% 3.29/0.93      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 3.29/0.93      | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
% 3.29/0.93      inference(demodulation,[status(thm)],[c_2056,c_21]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_2586,plain,
% 3.29/0.93      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 3.29/0.93      | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
% 3.29/0.93      inference(demodulation,[status(thm)],[c_2070,c_2412]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_2303,plain,
% 3.29/0.93      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1036,c_1038]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_2626,plain,
% 3.29/0.93      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 3.29/0.93      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
% 3.29/0.93      inference(demodulation,[status(thm)],[c_2586,c_2303]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_3205,plain,
% 3.29/0.93      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 3.29/0.93      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2) ),
% 3.29/0.93      inference(demodulation,[status(thm)],[c_2836,c_2626]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_1928,plain,
% 3.29/0.93      ( k7_relat_1(sK2,sK1) = sK2 ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1036,c_1035]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_2410,plain,
% 3.29/0.93      ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 3.29/0.93      inference(superposition,[status(thm)],[c_1928,c_1600]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_3206,plain,
% 3.29/0.93      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 3.29/0.93      | k10_relat_1(sK2,sK0) != k1_relat_1(sK2) ),
% 3.29/0.93      inference(light_normalisation,[status(thm)],[c_3205,c_1755,c_2410]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(c_3207,plain,
% 3.29/0.93      ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
% 3.29/0.93      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 3.29/0.93      inference(demodulation,[status(thm)],[c_3206,c_2836]) ).
% 3.29/0.93  
% 3.29/0.93  cnf(contradiction,plain,
% 3.29/0.93      ( $false ),
% 3.29/0.93      inference(minisat,[status(thm)],[c_6480,c_6289,c_5282,c_3207]) ).
% 3.29/0.93  
% 3.29/0.93  
% 3.29/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.93  
% 3.29/0.93  ------                               Statistics
% 3.29/0.93  
% 3.29/0.93  ------ General
% 3.29/0.93  
% 3.29/0.93  abstr_ref_over_cycles:                  0
% 3.29/0.93  abstr_ref_under_cycles:                 0
% 3.29/0.93  gc_basic_clause_elim:                   0
% 3.29/0.93  forced_gc_time:                         0
% 3.29/0.93  parsing_time:                           0.009
% 3.29/0.93  unif_index_cands_time:                  0.
% 3.29/0.93  unif_index_add_time:                    0.
% 3.29/0.93  orderings_time:                         0.
% 3.29/0.93  out_proof_time:                         0.035
% 3.29/0.93  total_time:                             0.291
% 3.29/0.93  num_of_symbols:                         51
% 3.29/0.93  num_of_terms:                           6101
% 3.29/0.93  
% 3.29/0.93  ------ Preprocessing
% 3.29/0.93  
% 3.29/0.93  num_of_splits:                          0
% 3.29/0.93  num_of_split_atoms:                     0
% 3.29/0.93  num_of_reused_defs:                     0
% 3.29/0.93  num_eq_ax_congr_red:                    28
% 3.29/0.93  num_of_sem_filtered_clauses:            1
% 3.29/0.93  num_of_subtypes:                        0
% 3.29/0.93  monotx_restored_types:                  0
% 3.29/0.93  sat_num_of_epr_types:                   0
% 3.29/0.93  sat_num_of_non_cyclic_types:            0
% 3.29/0.93  sat_guarded_non_collapsed_types:        0
% 3.29/0.93  num_pure_diseq_elim:                    0
% 3.29/0.93  simp_replaced_by:                       0
% 3.29/0.93  res_preprocessed:                       106
% 3.29/0.93  prep_upred:                             0
% 3.29/0.93  prep_unflattend:                        2
% 3.29/0.93  smt_new_axioms:                         0
% 3.29/0.93  pred_elim_cands:                        3
% 3.29/0.93  pred_elim:                              2
% 3.29/0.93  pred_elim_cl:                           3
% 3.29/0.93  pred_elim_cycles:                       4
% 3.29/0.93  merged_defs:                            8
% 3.29/0.93  merged_defs_ncl:                        0
% 3.29/0.93  bin_hyper_res:                          8
% 3.29/0.93  prep_cycles:                            4
% 3.29/0.93  pred_elim_time:                         0.003
% 3.29/0.93  splitting_time:                         0.
% 3.29/0.93  sem_filter_time:                        0.
% 3.29/0.93  monotx_time:                            0.001
% 3.29/0.93  subtype_inf_time:                       0.
% 3.29/0.93  
% 3.29/0.93  ------ Problem properties
% 3.29/0.93  
% 3.29/0.93  clauses:                                19
% 3.29/0.93  conjectures:                            2
% 3.29/0.93  epr:                                    2
% 3.29/0.93  horn:                                   19
% 3.29/0.93  ground:                                 2
% 3.29/0.93  unary:                                  2
% 3.29/0.93  binary:                                 14
% 3.29/0.93  lits:                                   39
% 3.29/0.93  lits_eq:                                11
% 3.29/0.93  fd_pure:                                0
% 3.29/0.93  fd_pseudo:                              0
% 3.29/0.93  fd_cond:                                0
% 3.29/0.93  fd_pseudo_cond:                         1
% 3.29/0.93  ac_symbols:                             0
% 3.29/0.93  
% 3.29/0.93  ------ Propositional Solver
% 3.29/0.93  
% 3.29/0.93  prop_solver_calls:                      30
% 3.29/0.93  prop_fast_solver_calls:                 686
% 3.29/0.93  smt_solver_calls:                       0
% 3.29/0.93  smt_fast_solver_calls:                  0
% 3.29/0.93  prop_num_of_clauses:                    2824
% 3.29/0.93  prop_preprocess_simplified:             6281
% 3.29/0.93  prop_fo_subsumed:                       13
% 3.29/0.93  prop_solver_time:                       0.
% 3.29/0.93  smt_solver_time:                        0.
% 3.29/0.93  smt_fast_solver_time:                   0.
% 3.29/0.93  prop_fast_solver_time:                  0.
% 3.29/0.93  prop_unsat_core_time:                   0.
% 3.29/0.93  
% 3.29/0.93  ------ QBF
% 3.29/0.93  
% 3.29/0.93  qbf_q_res:                              0
% 3.29/0.93  qbf_num_tautologies:                    0
% 3.29/0.93  qbf_prep_cycles:                        0
% 3.29/0.93  
% 3.29/0.93  ------ BMC1
% 3.29/0.93  
% 3.29/0.93  bmc1_current_bound:                     -1
% 3.29/0.93  bmc1_last_solved_bound:                 -1
% 3.29/0.93  bmc1_unsat_core_size:                   -1
% 3.29/0.93  bmc1_unsat_core_parents_size:           -1
% 3.29/0.93  bmc1_merge_next_fun:                    0
% 3.29/0.93  bmc1_unsat_core_clauses_time:           0.
% 3.29/0.93  
% 3.29/0.93  ------ Instantiation
% 3.29/0.93  
% 3.29/0.93  inst_num_of_clauses:                    934
% 3.29/0.93  inst_num_in_passive:                    140
% 3.29/0.93  inst_num_in_active:                     416
% 3.29/0.93  inst_num_in_unprocessed:                379
% 3.29/0.93  inst_num_of_loops:                      430
% 3.29/0.93  inst_num_of_learning_restarts:          0
% 3.29/0.93  inst_num_moves_active_passive:          10
% 3.29/0.93  inst_lit_activity:                      0
% 3.29/0.93  inst_lit_activity_moves:                0
% 3.29/0.93  inst_num_tautologies:                   0
% 3.29/0.93  inst_num_prop_implied:                  0
% 3.29/0.93  inst_num_existing_simplified:           0
% 3.29/0.93  inst_num_eq_res_simplified:             0
% 3.29/0.93  inst_num_child_elim:                    0
% 3.29/0.93  inst_num_of_dismatching_blockings:      315
% 3.29/0.93  inst_num_of_non_proper_insts:           1156
% 3.29/0.93  inst_num_of_duplicates:                 0
% 3.29/0.93  inst_inst_num_from_inst_to_res:         0
% 3.29/0.93  inst_dismatching_checking_time:         0.
% 3.29/0.93  
% 3.29/0.93  ------ Resolution
% 3.29/0.93  
% 3.29/0.93  res_num_of_clauses:                     0
% 3.29/0.93  res_num_in_passive:                     0
% 3.29/0.94  res_num_in_active:                      0
% 3.29/0.94  res_num_of_loops:                       110
% 3.29/0.94  res_forward_subset_subsumed:            81
% 3.29/0.94  res_backward_subset_subsumed:           6
% 3.29/0.94  res_forward_subsumed:                   0
% 3.29/0.94  res_backward_subsumed:                  0
% 3.29/0.94  res_forward_subsumption_resolution:     0
% 3.29/0.94  res_backward_subsumption_resolution:    0
% 3.29/0.94  res_clause_to_clause_subsumption:       315
% 3.29/0.94  res_orphan_elimination:                 0
% 3.29/0.94  res_tautology_del:                      111
% 3.29/0.94  res_num_eq_res_simplified:              0
% 3.29/0.94  res_num_sel_changes:                    0
% 3.29/0.94  res_moves_from_active_to_pass:          0
% 3.29/0.94  
% 3.29/0.94  ------ Superposition
% 3.29/0.94  
% 3.29/0.94  sup_time_total:                         0.
% 3.29/0.94  sup_time_generating:                    0.
% 3.29/0.94  sup_time_sim_full:                      0.
% 3.29/0.94  sup_time_sim_immed:                     0.
% 3.29/0.94  
% 3.29/0.94  sup_num_of_clauses:                     111
% 3.29/0.94  sup_num_in_active:                      82
% 3.29/0.94  sup_num_in_passive:                     29
% 3.29/0.94  sup_num_of_loops:                       85
% 3.29/0.94  sup_fw_superposition:                   70
% 3.29/0.94  sup_bw_superposition:                   57
% 3.29/0.94  sup_immediate_simplified:               23
% 3.29/0.94  sup_given_eliminated:                   0
% 3.29/0.94  comparisons_done:                       0
% 3.29/0.94  comparisons_avoided:                    0
% 3.29/0.94  
% 3.29/0.94  ------ Simplifications
% 3.29/0.94  
% 3.29/0.94  
% 3.29/0.94  sim_fw_subset_subsumed:                 2
% 3.29/0.94  sim_bw_subset_subsumed:                 0
% 3.29/0.94  sim_fw_subsumed:                        9
% 3.29/0.94  sim_bw_subsumed:                        0
% 3.29/0.94  sim_fw_subsumption_res:                 0
% 3.29/0.94  sim_bw_subsumption_res:                 0
% 3.29/0.94  sim_tautology_del:                      1
% 3.29/0.94  sim_eq_tautology_del:                   1
% 3.29/0.94  sim_eq_res_simp:                        1
% 3.29/0.94  sim_fw_demodulated:                     5
% 3.29/0.94  sim_bw_demodulated:                     4
% 3.29/0.94  sim_light_normalised:                   11
% 3.29/0.94  sim_joinable_taut:                      0
% 3.29/0.94  sim_joinable_simp:                      0
% 3.29/0.94  sim_ac_normalised:                      0
% 3.29/0.94  sim_smt_subsumption:                    0
% 3.29/0.94  
%------------------------------------------------------------------------------
