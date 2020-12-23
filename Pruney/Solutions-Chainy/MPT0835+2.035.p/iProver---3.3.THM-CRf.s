%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:14 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 844 expanded)
%              Number of clauses        :   91 ( 368 expanded)
%              Number of leaves         :   18 ( 157 expanded)
%              Depth                    :   16
%              Number of atoms          :  338 (2058 expanded)
%              Number of equality atoms :  166 ( 884 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_744,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_731,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_732,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2209,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_732])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_11])).

cnf(c_730,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_2275,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2209,c_730])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_861,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1009,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1010,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1044,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1045,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_2752,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2275,c_22,c_1010,c_1045])).

cnf(c_2753,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2752])).

cnf(c_2760,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_744,c_2753])).

cnf(c_742,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1715,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_742])).

cnf(c_1968,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1715,c_22,c_1010,c_1045])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_740,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1974,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1968,c_740])).

cnf(c_2875,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2760,c_1974])).

cnf(c_12,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_737,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2877,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2875,c_737])).

cnf(c_925,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1486,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_1487,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_4466,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2877,c_22,c_1010,c_1045,c_1487])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_6])).

cnf(c_729,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_1105,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_729])).

cnf(c_1468,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1105,c_22,c_1010,c_1045])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_743,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1474,plain,
    ( k3_xboole_0(k2_relat_1(sK2),sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1468,c_743])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_738,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1973,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1968,c_738])).

cnf(c_2125,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_1474,c_1973])).

cnf(c_4470,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4466,c_2125])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2101,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X0)
    | X0 = k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3548,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0))
    | k10_relat_1(sK2,X0) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_3549,plain,
    ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
    | r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3548])).

cnf(c_3551,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2)
    | r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3549])).

cnf(c_2761,plain,
    ( k7_relat_1(sK2,k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(sK2)))) = sK2
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_2753])).

cnf(c_3286,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_2761])).

cnf(c_3287,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3286,c_2125,c_2875])).

cnf(c_3497,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3287,c_22,c_1010,c_1045])).

cnf(c_3500,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3497,c_1974])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_733,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1720,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_731,c_733])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_736,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1174,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_731,c_736])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_735,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1170,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_731,c_735])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1247,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1170,c_20])).

cnf(c_1383,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1174,c_1247])).

cnf(c_1896,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1720,c_1383])).

cnf(c_1897,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1896,c_1720])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_734,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1798,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_731,c_734])).

cnf(c_2131,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1897,c_1798])).

cnf(c_1617,plain,
    ( k7_relat_1(sK2,sK1) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_730])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_1504,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK1) = sK2 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1964,plain,
    ( k7_relat_1(sK2,sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1617,c_21,c_1009,c_1044,c_1504])).

cnf(c_2046,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1964,c_1974])).

cnf(c_2132,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2131,c_2046])).

cnf(c_2964,plain,
    ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2125,c_2132])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1304,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1323,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(c_1325,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4470,c_3551,c_3500,c_2964,c_1325,c_1045,c_1010,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.21/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.01  
% 2.21/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/1.01  
% 2.21/1.01  ------  iProver source info
% 2.21/1.01  
% 2.21/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.21/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/1.01  git: non_committed_changes: false
% 2.21/1.01  git: last_make_outside_of_git: false
% 2.21/1.01  
% 2.21/1.01  ------ 
% 2.21/1.01  
% 2.21/1.01  ------ Input Options
% 2.21/1.01  
% 2.21/1.01  --out_options                           all
% 2.21/1.01  --tptp_safe_out                         true
% 2.21/1.01  --problem_path                          ""
% 2.21/1.01  --include_path                          ""
% 2.21/1.01  --clausifier                            res/vclausify_rel
% 2.21/1.01  --clausifier_options                    --mode clausify
% 2.21/1.01  --stdin                                 false
% 2.21/1.01  --stats_out                             all
% 2.21/1.01  
% 2.21/1.01  ------ General Options
% 2.21/1.01  
% 2.21/1.01  --fof                                   false
% 2.21/1.01  --time_out_real                         305.
% 2.21/1.01  --time_out_virtual                      -1.
% 2.21/1.01  --symbol_type_check                     false
% 2.21/1.01  --clausify_out                          false
% 2.21/1.01  --sig_cnt_out                           false
% 2.21/1.01  --trig_cnt_out                          false
% 2.21/1.01  --trig_cnt_out_tolerance                1.
% 2.21/1.01  --trig_cnt_out_sk_spl                   false
% 2.21/1.01  --abstr_cl_out                          false
% 2.21/1.01  
% 2.21/1.01  ------ Global Options
% 2.21/1.01  
% 2.21/1.01  --schedule                              default
% 2.21/1.01  --add_important_lit                     false
% 2.21/1.01  --prop_solver_per_cl                    1000
% 2.21/1.01  --min_unsat_core                        false
% 2.21/1.01  --soft_assumptions                      false
% 2.21/1.01  --soft_lemma_size                       3
% 2.21/1.01  --prop_impl_unit_size                   0
% 2.21/1.01  --prop_impl_unit                        []
% 2.21/1.01  --share_sel_clauses                     true
% 2.21/1.01  --reset_solvers                         false
% 2.21/1.01  --bc_imp_inh                            [conj_cone]
% 2.21/1.01  --conj_cone_tolerance                   3.
% 2.21/1.01  --extra_neg_conj                        none
% 2.21/1.01  --large_theory_mode                     true
% 2.21/1.01  --prolific_symb_bound                   200
% 2.21/1.01  --lt_threshold                          2000
% 2.21/1.01  --clause_weak_htbl                      true
% 2.21/1.01  --gc_record_bc_elim                     false
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing Options
% 2.21/1.01  
% 2.21/1.01  --preprocessing_flag                    true
% 2.21/1.01  --time_out_prep_mult                    0.1
% 2.21/1.01  --splitting_mode                        input
% 2.21/1.01  --splitting_grd                         true
% 2.21/1.01  --splitting_cvd                         false
% 2.21/1.01  --splitting_cvd_svl                     false
% 2.21/1.01  --splitting_nvd                         32
% 2.21/1.01  --sub_typing                            true
% 2.21/1.01  --prep_gs_sim                           true
% 2.21/1.01  --prep_unflatten                        true
% 2.21/1.01  --prep_res_sim                          true
% 2.21/1.01  --prep_upred                            true
% 2.21/1.01  --prep_sem_filter                       exhaustive
% 2.21/1.01  --prep_sem_filter_out                   false
% 2.21/1.01  --pred_elim                             true
% 2.21/1.01  --res_sim_input                         true
% 2.21/1.01  --eq_ax_congr_red                       true
% 2.21/1.01  --pure_diseq_elim                       true
% 2.21/1.01  --brand_transform                       false
% 2.21/1.01  --non_eq_to_eq                          false
% 2.21/1.01  --prep_def_merge                        true
% 2.21/1.01  --prep_def_merge_prop_impl              false
% 2.21/1.01  --prep_def_merge_mbd                    true
% 2.21/1.01  --prep_def_merge_tr_red                 false
% 2.21/1.01  --prep_def_merge_tr_cl                  false
% 2.21/1.01  --smt_preprocessing                     true
% 2.21/1.01  --smt_ac_axioms                         fast
% 2.21/1.01  --preprocessed_out                      false
% 2.21/1.01  --preprocessed_stats                    false
% 2.21/1.01  
% 2.21/1.01  ------ Abstraction refinement Options
% 2.21/1.01  
% 2.21/1.01  --abstr_ref                             []
% 2.21/1.01  --abstr_ref_prep                        false
% 2.21/1.01  --abstr_ref_until_sat                   false
% 2.21/1.01  --abstr_ref_sig_restrict                funpre
% 2.21/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.01  --abstr_ref_under                       []
% 2.21/1.01  
% 2.21/1.01  ------ SAT Options
% 2.21/1.01  
% 2.21/1.01  --sat_mode                              false
% 2.21/1.01  --sat_fm_restart_options                ""
% 2.21/1.01  --sat_gr_def                            false
% 2.21/1.01  --sat_epr_types                         true
% 2.21/1.01  --sat_non_cyclic_types                  false
% 2.21/1.01  --sat_finite_models                     false
% 2.21/1.01  --sat_fm_lemmas                         false
% 2.21/1.01  --sat_fm_prep                           false
% 2.21/1.01  --sat_fm_uc_incr                        true
% 2.21/1.01  --sat_out_model                         small
% 2.21/1.01  --sat_out_clauses                       false
% 2.21/1.01  
% 2.21/1.01  ------ QBF Options
% 2.21/1.01  
% 2.21/1.01  --qbf_mode                              false
% 2.21/1.01  --qbf_elim_univ                         false
% 2.21/1.01  --qbf_dom_inst                          none
% 2.21/1.01  --qbf_dom_pre_inst                      false
% 2.21/1.01  --qbf_sk_in                             false
% 2.21/1.01  --qbf_pred_elim                         true
% 2.21/1.01  --qbf_split                             512
% 2.21/1.01  
% 2.21/1.01  ------ BMC1 Options
% 2.21/1.01  
% 2.21/1.01  --bmc1_incremental                      false
% 2.21/1.01  --bmc1_axioms                           reachable_all
% 2.21/1.01  --bmc1_min_bound                        0
% 2.21/1.01  --bmc1_max_bound                        -1
% 2.21/1.01  --bmc1_max_bound_default                -1
% 2.21/1.01  --bmc1_symbol_reachability              true
% 2.21/1.01  --bmc1_property_lemmas                  false
% 2.21/1.01  --bmc1_k_induction                      false
% 2.21/1.01  --bmc1_non_equiv_states                 false
% 2.21/1.01  --bmc1_deadlock                         false
% 2.21/1.01  --bmc1_ucm                              false
% 2.21/1.01  --bmc1_add_unsat_core                   none
% 2.21/1.01  --bmc1_unsat_core_children              false
% 2.21/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.01  --bmc1_out_stat                         full
% 2.21/1.01  --bmc1_ground_init                      false
% 2.21/1.01  --bmc1_pre_inst_next_state              false
% 2.21/1.01  --bmc1_pre_inst_state                   false
% 2.21/1.01  --bmc1_pre_inst_reach_state             false
% 2.21/1.01  --bmc1_out_unsat_core                   false
% 2.21/1.01  --bmc1_aig_witness_out                  false
% 2.21/1.01  --bmc1_verbose                          false
% 2.21/1.01  --bmc1_dump_clauses_tptp                false
% 2.21/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.01  --bmc1_dump_file                        -
% 2.21/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.01  --bmc1_ucm_extend_mode                  1
% 2.21/1.01  --bmc1_ucm_init_mode                    2
% 2.21/1.01  --bmc1_ucm_cone_mode                    none
% 2.21/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.01  --bmc1_ucm_relax_model                  4
% 2.21/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.01  --bmc1_ucm_layered_model                none
% 2.21/1.01  --bmc1_ucm_max_lemma_size               10
% 2.21/1.01  
% 2.21/1.01  ------ AIG Options
% 2.21/1.01  
% 2.21/1.01  --aig_mode                              false
% 2.21/1.01  
% 2.21/1.01  ------ Instantiation Options
% 2.21/1.01  
% 2.21/1.01  --instantiation_flag                    true
% 2.21/1.01  --inst_sos_flag                         false
% 2.21/1.01  --inst_sos_phase                        true
% 2.21/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.01  --inst_lit_sel_side                     num_symb
% 2.21/1.01  --inst_solver_per_active                1400
% 2.21/1.01  --inst_solver_calls_frac                1.
% 2.21/1.01  --inst_passive_queue_type               priority_queues
% 2.21/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.01  --inst_passive_queues_freq              [25;2]
% 2.21/1.01  --inst_dismatching                      true
% 2.21/1.01  --inst_eager_unprocessed_to_passive     true
% 2.21/1.01  --inst_prop_sim_given                   true
% 2.21/1.01  --inst_prop_sim_new                     false
% 2.21/1.01  --inst_subs_new                         false
% 2.21/1.01  --inst_eq_res_simp                      false
% 2.21/1.01  --inst_subs_given                       false
% 2.21/1.01  --inst_orphan_elimination               true
% 2.21/1.01  --inst_learning_loop_flag               true
% 2.21/1.01  --inst_learning_start                   3000
% 2.21/1.01  --inst_learning_factor                  2
% 2.21/1.01  --inst_start_prop_sim_after_learn       3
% 2.21/1.01  --inst_sel_renew                        solver
% 2.21/1.01  --inst_lit_activity_flag                true
% 2.21/1.01  --inst_restr_to_given                   false
% 2.21/1.01  --inst_activity_threshold               500
% 2.21/1.01  --inst_out_proof                        true
% 2.21/1.01  
% 2.21/1.01  ------ Resolution Options
% 2.21/1.01  
% 2.21/1.01  --resolution_flag                       true
% 2.21/1.01  --res_lit_sel                           adaptive
% 2.21/1.01  --res_lit_sel_side                      none
% 2.21/1.01  --res_ordering                          kbo
% 2.21/1.01  --res_to_prop_solver                    active
% 2.21/1.01  --res_prop_simpl_new                    false
% 2.21/1.01  --res_prop_simpl_given                  true
% 2.21/1.01  --res_passive_queue_type                priority_queues
% 2.21/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.01  --res_passive_queues_freq               [15;5]
% 2.21/1.01  --res_forward_subs                      full
% 2.21/1.01  --res_backward_subs                     full
% 2.21/1.01  --res_forward_subs_resolution           true
% 2.21/1.01  --res_backward_subs_resolution          true
% 2.21/1.01  --res_orphan_elimination                true
% 2.21/1.01  --res_time_limit                        2.
% 2.21/1.01  --res_out_proof                         true
% 2.21/1.01  
% 2.21/1.01  ------ Superposition Options
% 2.21/1.01  
% 2.21/1.01  --superposition_flag                    true
% 2.21/1.01  --sup_passive_queue_type                priority_queues
% 2.21/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.01  --demod_completeness_check              fast
% 2.21/1.01  --demod_use_ground                      true
% 2.21/1.01  --sup_to_prop_solver                    passive
% 2.21/1.01  --sup_prop_simpl_new                    true
% 2.21/1.01  --sup_prop_simpl_given                  true
% 2.21/1.01  --sup_fun_splitting                     false
% 2.21/1.01  --sup_smt_interval                      50000
% 2.21/1.01  
% 2.21/1.01  ------ Superposition Simplification Setup
% 2.21/1.01  
% 2.21/1.01  --sup_indices_passive                   []
% 2.21/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_full_bw                           [BwDemod]
% 2.21/1.01  --sup_immed_triv                        [TrivRules]
% 2.21/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_immed_bw_main                     []
% 2.21/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.01  
% 2.21/1.01  ------ Combination Options
% 2.21/1.01  
% 2.21/1.01  --comb_res_mult                         3
% 2.21/1.01  --comb_sup_mult                         2
% 2.21/1.01  --comb_inst_mult                        10
% 2.21/1.01  
% 2.21/1.01  ------ Debug Options
% 2.21/1.01  
% 2.21/1.01  --dbg_backtrace                         false
% 2.21/1.01  --dbg_dump_prop_clauses                 false
% 2.21/1.01  --dbg_dump_prop_clauses_file            -
% 2.21/1.01  --dbg_out_stat                          false
% 2.21/1.01  ------ Parsing...
% 2.21/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/1.01  ------ Proving...
% 2.21/1.01  ------ Problem Properties 
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  clauses                                 18
% 2.21/1.01  conjectures                             2
% 2.21/1.01  EPR                                     2
% 2.21/1.01  Horn                                    18
% 2.21/1.01  unary                                   3
% 2.21/1.01  binary                                  9
% 2.21/1.01  lits                                    39
% 2.21/1.01  lits eq                                 11
% 2.21/1.01  fd_pure                                 0
% 2.21/1.01  fd_pseudo                               0
% 2.21/1.01  fd_cond                                 0
% 2.21/1.01  fd_pseudo_cond                          1
% 2.21/1.01  AC symbols                              0
% 2.21/1.01  
% 2.21/1.01  ------ Schedule dynamic 5 is on 
% 2.21/1.01  
% 2.21/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  ------ 
% 2.21/1.01  Current options:
% 2.21/1.01  ------ 
% 2.21/1.01  
% 2.21/1.01  ------ Input Options
% 2.21/1.01  
% 2.21/1.01  --out_options                           all
% 2.21/1.01  --tptp_safe_out                         true
% 2.21/1.01  --problem_path                          ""
% 2.21/1.01  --include_path                          ""
% 2.21/1.01  --clausifier                            res/vclausify_rel
% 2.21/1.01  --clausifier_options                    --mode clausify
% 2.21/1.01  --stdin                                 false
% 2.21/1.01  --stats_out                             all
% 2.21/1.01  
% 2.21/1.01  ------ General Options
% 2.21/1.01  
% 2.21/1.01  --fof                                   false
% 2.21/1.01  --time_out_real                         305.
% 2.21/1.01  --time_out_virtual                      -1.
% 2.21/1.01  --symbol_type_check                     false
% 2.21/1.01  --clausify_out                          false
% 2.21/1.01  --sig_cnt_out                           false
% 2.21/1.01  --trig_cnt_out                          false
% 2.21/1.01  --trig_cnt_out_tolerance                1.
% 2.21/1.01  --trig_cnt_out_sk_spl                   false
% 2.21/1.01  --abstr_cl_out                          false
% 2.21/1.01  
% 2.21/1.01  ------ Global Options
% 2.21/1.01  
% 2.21/1.01  --schedule                              default
% 2.21/1.01  --add_important_lit                     false
% 2.21/1.01  --prop_solver_per_cl                    1000
% 2.21/1.01  --min_unsat_core                        false
% 2.21/1.01  --soft_assumptions                      false
% 2.21/1.01  --soft_lemma_size                       3
% 2.21/1.01  --prop_impl_unit_size                   0
% 2.21/1.01  --prop_impl_unit                        []
% 2.21/1.01  --share_sel_clauses                     true
% 2.21/1.01  --reset_solvers                         false
% 2.21/1.01  --bc_imp_inh                            [conj_cone]
% 2.21/1.01  --conj_cone_tolerance                   3.
% 2.21/1.01  --extra_neg_conj                        none
% 2.21/1.01  --large_theory_mode                     true
% 2.21/1.01  --prolific_symb_bound                   200
% 2.21/1.01  --lt_threshold                          2000
% 2.21/1.01  --clause_weak_htbl                      true
% 2.21/1.01  --gc_record_bc_elim                     false
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing Options
% 2.21/1.01  
% 2.21/1.01  --preprocessing_flag                    true
% 2.21/1.01  --time_out_prep_mult                    0.1
% 2.21/1.01  --splitting_mode                        input
% 2.21/1.01  --splitting_grd                         true
% 2.21/1.01  --splitting_cvd                         false
% 2.21/1.01  --splitting_cvd_svl                     false
% 2.21/1.01  --splitting_nvd                         32
% 2.21/1.01  --sub_typing                            true
% 2.21/1.01  --prep_gs_sim                           true
% 2.21/1.01  --prep_unflatten                        true
% 2.21/1.01  --prep_res_sim                          true
% 2.21/1.01  --prep_upred                            true
% 2.21/1.01  --prep_sem_filter                       exhaustive
% 2.21/1.01  --prep_sem_filter_out                   false
% 2.21/1.01  --pred_elim                             true
% 2.21/1.01  --res_sim_input                         true
% 2.21/1.01  --eq_ax_congr_red                       true
% 2.21/1.01  --pure_diseq_elim                       true
% 2.21/1.01  --brand_transform                       false
% 2.21/1.01  --non_eq_to_eq                          false
% 2.21/1.01  --prep_def_merge                        true
% 2.21/1.01  --prep_def_merge_prop_impl              false
% 2.21/1.01  --prep_def_merge_mbd                    true
% 2.21/1.01  --prep_def_merge_tr_red                 false
% 2.21/1.01  --prep_def_merge_tr_cl                  false
% 2.21/1.01  --smt_preprocessing                     true
% 2.21/1.01  --smt_ac_axioms                         fast
% 2.21/1.01  --preprocessed_out                      false
% 2.21/1.01  --preprocessed_stats                    false
% 2.21/1.01  
% 2.21/1.01  ------ Abstraction refinement Options
% 2.21/1.01  
% 2.21/1.01  --abstr_ref                             []
% 2.21/1.01  --abstr_ref_prep                        false
% 2.21/1.01  --abstr_ref_until_sat                   false
% 2.21/1.01  --abstr_ref_sig_restrict                funpre
% 2.21/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.01  --abstr_ref_under                       []
% 2.21/1.01  
% 2.21/1.01  ------ SAT Options
% 2.21/1.01  
% 2.21/1.01  --sat_mode                              false
% 2.21/1.01  --sat_fm_restart_options                ""
% 2.21/1.01  --sat_gr_def                            false
% 2.21/1.01  --sat_epr_types                         true
% 2.21/1.01  --sat_non_cyclic_types                  false
% 2.21/1.01  --sat_finite_models                     false
% 2.21/1.01  --sat_fm_lemmas                         false
% 2.21/1.01  --sat_fm_prep                           false
% 2.21/1.01  --sat_fm_uc_incr                        true
% 2.21/1.01  --sat_out_model                         small
% 2.21/1.01  --sat_out_clauses                       false
% 2.21/1.01  
% 2.21/1.01  ------ QBF Options
% 2.21/1.01  
% 2.21/1.01  --qbf_mode                              false
% 2.21/1.01  --qbf_elim_univ                         false
% 2.21/1.01  --qbf_dom_inst                          none
% 2.21/1.01  --qbf_dom_pre_inst                      false
% 2.21/1.01  --qbf_sk_in                             false
% 2.21/1.01  --qbf_pred_elim                         true
% 2.21/1.01  --qbf_split                             512
% 2.21/1.01  
% 2.21/1.01  ------ BMC1 Options
% 2.21/1.01  
% 2.21/1.01  --bmc1_incremental                      false
% 2.21/1.01  --bmc1_axioms                           reachable_all
% 2.21/1.01  --bmc1_min_bound                        0
% 2.21/1.01  --bmc1_max_bound                        -1
% 2.21/1.01  --bmc1_max_bound_default                -1
% 2.21/1.01  --bmc1_symbol_reachability              true
% 2.21/1.01  --bmc1_property_lemmas                  false
% 2.21/1.01  --bmc1_k_induction                      false
% 2.21/1.01  --bmc1_non_equiv_states                 false
% 2.21/1.01  --bmc1_deadlock                         false
% 2.21/1.01  --bmc1_ucm                              false
% 2.21/1.01  --bmc1_add_unsat_core                   none
% 2.21/1.01  --bmc1_unsat_core_children              false
% 2.21/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.01  --bmc1_out_stat                         full
% 2.21/1.01  --bmc1_ground_init                      false
% 2.21/1.01  --bmc1_pre_inst_next_state              false
% 2.21/1.01  --bmc1_pre_inst_state                   false
% 2.21/1.01  --bmc1_pre_inst_reach_state             false
% 2.21/1.01  --bmc1_out_unsat_core                   false
% 2.21/1.01  --bmc1_aig_witness_out                  false
% 2.21/1.01  --bmc1_verbose                          false
% 2.21/1.01  --bmc1_dump_clauses_tptp                false
% 2.21/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.01  --bmc1_dump_file                        -
% 2.21/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.01  --bmc1_ucm_extend_mode                  1
% 2.21/1.01  --bmc1_ucm_init_mode                    2
% 2.21/1.01  --bmc1_ucm_cone_mode                    none
% 2.21/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.01  --bmc1_ucm_relax_model                  4
% 2.21/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.01  --bmc1_ucm_layered_model                none
% 2.21/1.01  --bmc1_ucm_max_lemma_size               10
% 2.21/1.01  
% 2.21/1.01  ------ AIG Options
% 2.21/1.01  
% 2.21/1.01  --aig_mode                              false
% 2.21/1.01  
% 2.21/1.01  ------ Instantiation Options
% 2.21/1.01  
% 2.21/1.01  --instantiation_flag                    true
% 2.21/1.01  --inst_sos_flag                         false
% 2.21/1.01  --inst_sos_phase                        true
% 2.21/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.01  --inst_lit_sel_side                     none
% 2.21/1.01  --inst_solver_per_active                1400
% 2.21/1.01  --inst_solver_calls_frac                1.
% 2.21/1.01  --inst_passive_queue_type               priority_queues
% 2.21/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.01  --inst_passive_queues_freq              [25;2]
% 2.21/1.01  --inst_dismatching                      true
% 2.21/1.01  --inst_eager_unprocessed_to_passive     true
% 2.21/1.01  --inst_prop_sim_given                   true
% 2.21/1.01  --inst_prop_sim_new                     false
% 2.21/1.01  --inst_subs_new                         false
% 2.21/1.01  --inst_eq_res_simp                      false
% 2.21/1.01  --inst_subs_given                       false
% 2.21/1.01  --inst_orphan_elimination               true
% 2.21/1.01  --inst_learning_loop_flag               true
% 2.21/1.01  --inst_learning_start                   3000
% 2.21/1.01  --inst_learning_factor                  2
% 2.21/1.01  --inst_start_prop_sim_after_learn       3
% 2.21/1.01  --inst_sel_renew                        solver
% 2.21/1.01  --inst_lit_activity_flag                true
% 2.21/1.01  --inst_restr_to_given                   false
% 2.21/1.01  --inst_activity_threshold               500
% 2.21/1.01  --inst_out_proof                        true
% 2.21/1.01  
% 2.21/1.01  ------ Resolution Options
% 2.21/1.01  
% 2.21/1.01  --resolution_flag                       false
% 2.21/1.01  --res_lit_sel                           adaptive
% 2.21/1.01  --res_lit_sel_side                      none
% 2.21/1.01  --res_ordering                          kbo
% 2.21/1.01  --res_to_prop_solver                    active
% 2.21/1.01  --res_prop_simpl_new                    false
% 2.21/1.01  --res_prop_simpl_given                  true
% 2.21/1.01  --res_passive_queue_type                priority_queues
% 2.21/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.01  --res_passive_queues_freq               [15;5]
% 2.21/1.01  --res_forward_subs                      full
% 2.21/1.01  --res_backward_subs                     full
% 2.21/1.01  --res_forward_subs_resolution           true
% 2.21/1.01  --res_backward_subs_resolution          true
% 2.21/1.01  --res_orphan_elimination                true
% 2.21/1.01  --res_time_limit                        2.
% 2.21/1.01  --res_out_proof                         true
% 2.21/1.01  
% 2.21/1.01  ------ Superposition Options
% 2.21/1.01  
% 2.21/1.01  --superposition_flag                    true
% 2.21/1.01  --sup_passive_queue_type                priority_queues
% 2.21/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.01  --demod_completeness_check              fast
% 2.21/1.01  --demod_use_ground                      true
% 2.21/1.01  --sup_to_prop_solver                    passive
% 2.21/1.01  --sup_prop_simpl_new                    true
% 2.21/1.01  --sup_prop_simpl_given                  true
% 2.21/1.01  --sup_fun_splitting                     false
% 2.21/1.01  --sup_smt_interval                      50000
% 2.21/1.01  
% 2.21/1.01  ------ Superposition Simplification Setup
% 2.21/1.01  
% 2.21/1.01  --sup_indices_passive                   []
% 2.21/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_full_bw                           [BwDemod]
% 2.21/1.01  --sup_immed_triv                        [TrivRules]
% 2.21/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_immed_bw_main                     []
% 2.21/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.01  
% 2.21/1.01  ------ Combination Options
% 2.21/1.01  
% 2.21/1.01  --comb_res_mult                         3
% 2.21/1.01  --comb_sup_mult                         2
% 2.21/1.01  --comb_inst_mult                        10
% 2.21/1.01  
% 2.21/1.01  ------ Debug Options
% 2.21/1.01  
% 2.21/1.01  --dbg_backtrace                         false
% 2.21/1.01  --dbg_dump_prop_clauses                 false
% 2.21/1.01  --dbg_dump_prop_clauses_file            -
% 2.21/1.01  --dbg_out_stat                          false
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  ------ Proving...
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  % SZS status Theorem for theBenchmark.p
% 2.21/1.01  
% 2.21/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/1.01  
% 2.21/1.01  fof(f1,axiom,(
% 2.21/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f37,plain,(
% 2.21/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/1.01    inference(nnf_transformation,[],[f1])).
% 2.21/1.01  
% 2.21/1.01  fof(f38,plain,(
% 2.21/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/1.01    inference(flattening,[],[f37])).
% 2.21/1.01  
% 2.21/1.01  fof(f43,plain,(
% 2.21/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.21/1.01    inference(cnf_transformation,[],[f38])).
% 2.21/1.01  
% 2.21/1.01  fof(f64,plain,(
% 2.21/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.21/1.01    inference(equality_resolution,[],[f43])).
% 2.21/1.01  
% 2.21/1.01  fof(f17,conjecture,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f18,negated_conjecture,(
% 2.21/1.01    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.21/1.01    inference(negated_conjecture,[],[f17])).
% 2.21/1.01  
% 2.21/1.01  fof(f36,plain,(
% 2.21/1.01    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.21/1.01    inference(ennf_transformation,[],[f18])).
% 2.21/1.01  
% 2.21/1.01  fof(f40,plain,(
% 2.21/1.01    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 2.21/1.01    introduced(choice_axiom,[])).
% 2.21/1.01  
% 2.21/1.01  fof(f41,plain,(
% 2.21/1.01    (k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40])).
% 2.21/1.01  
% 2.21/1.01  fof(f62,plain,(
% 2.21/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.21/1.01    inference(cnf_transformation,[],[f41])).
% 2.21/1.01  
% 2.21/1.01  fof(f16,axiom,(
% 2.21/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f34,plain,(
% 2.21/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.21/1.01    inference(ennf_transformation,[],[f16])).
% 2.21/1.01  
% 2.21/1.01  fof(f35,plain,(
% 2.21/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.21/1.01    inference(flattening,[],[f34])).
% 2.21/1.01  
% 2.21/1.01  fof(f61,plain,(
% 2.21/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f35])).
% 2.21/1.01  
% 2.21/1.01  fof(f11,axiom,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f29,plain,(
% 2.21/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(ennf_transformation,[],[f11])).
% 2.21/1.01  
% 2.21/1.01  fof(f55,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f29])).
% 2.21/1.01  
% 2.21/1.01  fof(f9,axiom,(
% 2.21/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f25,plain,(
% 2.21/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.21/1.01    inference(ennf_transformation,[],[f9])).
% 2.21/1.01  
% 2.21/1.01  fof(f26,plain,(
% 2.21/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.21/1.01    inference(flattening,[],[f25])).
% 2.21/1.01  
% 2.21/1.01  fof(f53,plain,(
% 2.21/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f26])).
% 2.21/1.01  
% 2.21/1.01  fof(f3,axiom,(
% 2.21/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f20,plain,(
% 2.21/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.21/1.01    inference(ennf_transformation,[],[f3])).
% 2.21/1.01  
% 2.21/1.01  fof(f46,plain,(
% 2.21/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f20])).
% 2.21/1.01  
% 2.21/1.01  fof(f5,axiom,(
% 2.21/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f49,plain,(
% 2.21/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f5])).
% 2.21/1.01  
% 2.21/1.01  fof(f6,axiom,(
% 2.21/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f22,plain,(
% 2.21/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.21/1.01    inference(ennf_transformation,[],[f6])).
% 2.21/1.01  
% 2.21/1.01  fof(f50,plain,(
% 2.21/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f22])).
% 2.21/1.01  
% 2.21/1.01  fof(f10,axiom,(
% 2.21/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f27,plain,(
% 2.21/1.01    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.21/1.01    inference(ennf_transformation,[],[f10])).
% 2.21/1.01  
% 2.21/1.01  fof(f28,plain,(
% 2.21/1.01    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.21/1.01    inference(flattening,[],[f27])).
% 2.21/1.01  
% 2.21/1.01  fof(f54,plain,(
% 2.21/1.01    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f28])).
% 2.21/1.01  
% 2.21/1.01  fof(f56,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f29])).
% 2.21/1.01  
% 2.21/1.01  fof(f4,axiom,(
% 2.21/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f21,plain,(
% 2.21/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.21/1.01    inference(ennf_transformation,[],[f4])).
% 2.21/1.01  
% 2.21/1.01  fof(f39,plain,(
% 2.21/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.21/1.01    inference(nnf_transformation,[],[f21])).
% 2.21/1.01  
% 2.21/1.01  fof(f47,plain,(
% 2.21/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f39])).
% 2.21/1.01  
% 2.21/1.01  fof(f2,axiom,(
% 2.21/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f19,plain,(
% 2.21/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.21/1.01    inference(ennf_transformation,[],[f2])).
% 2.21/1.01  
% 2.21/1.01  fof(f45,plain,(
% 2.21/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f19])).
% 2.21/1.01  
% 2.21/1.01  fof(f8,axiom,(
% 2.21/1.01    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f24,plain,(
% 2.21/1.01    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.21/1.01    inference(ennf_transformation,[],[f8])).
% 2.21/1.01  
% 2.21/1.01  fof(f52,plain,(
% 2.21/1.01    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f24])).
% 2.21/1.01  
% 2.21/1.01  fof(f44,plain,(
% 2.21/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f38])).
% 2.21/1.01  
% 2.21/1.01  fof(f15,axiom,(
% 2.21/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f33,plain,(
% 2.21/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(ennf_transformation,[],[f15])).
% 2.21/1.01  
% 2.21/1.01  fof(f60,plain,(
% 2.21/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f33])).
% 2.21/1.01  
% 2.21/1.01  fof(f12,axiom,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f30,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(ennf_transformation,[],[f12])).
% 2.21/1.01  
% 2.21/1.01  fof(f57,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f30])).
% 2.21/1.01  
% 2.21/1.01  fof(f13,axiom,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f31,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(ennf_transformation,[],[f13])).
% 2.21/1.01  
% 2.21/1.01  fof(f58,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f31])).
% 2.21/1.01  
% 2.21/1.01  fof(f63,plain,(
% 2.21/1.01    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 2.21/1.01    inference(cnf_transformation,[],[f41])).
% 2.21/1.01  
% 2.21/1.01  fof(f14,axiom,(
% 2.21/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f32,plain,(
% 2.21/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(ennf_transformation,[],[f14])).
% 2.21/1.01  
% 2.21/1.01  fof(f59,plain,(
% 2.21/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f32])).
% 2.21/1.01  
% 2.21/1.01  fof(f7,axiom,(
% 2.21/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f23,plain,(
% 2.21/1.01    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.21/1.01    inference(ennf_transformation,[],[f7])).
% 2.21/1.01  
% 2.21/1.01  fof(f51,plain,(
% 2.21/1.01    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f23])).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1,plain,
% 2.21/1.01      ( r1_tarski(X0,X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_744,plain,
% 2.21/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_21,negated_conjecture,
% 2.21/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.21/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_731,plain,
% 2.21/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_19,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.21/1.01      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 2.21/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_732,plain,
% 2.21/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.21/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 2.21/1.01      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2209,plain,
% 2.21/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) = iProver_top
% 2.21/1.01      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_731,c_732]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_14,plain,
% 2.21/1.01      ( v4_relat_1(X0,X1)
% 2.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.21/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_11,plain,
% 2.21/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.21/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_245,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | ~ v1_relat_1(X0)
% 2.21/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.21/1.01      inference(resolution,[status(thm)],[c_14,c_11]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_730,plain,
% 2.21/1.01      ( k7_relat_1(X0,X1) = X0
% 2.21/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2275,plain,
% 2.21/1.01      ( k7_relat_1(sK2,X0) = sK2
% 2.21/1.01      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.21/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_2209,c_730]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_22,plain,
% 2.21/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_4,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.21/1.01      | ~ v1_relat_1(X1)
% 2.21/1.01      | v1_relat_1(X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_861,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | v1_relat_1(X0)
% 2.21/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1009,plain,
% 2.21/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.21/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 2.21/1.01      | v1_relat_1(sK2) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_861]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1010,plain,
% 2.21/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.21/1.01      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.21/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1009]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_7,plain,
% 2.21/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.21/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1044,plain,
% 2.21/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1045,plain,
% 2.21/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2752,plain,
% 2.21/1.01      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.21/1.01      | k7_relat_1(sK2,X0) = sK2 ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_2275,c_22,c_1010,c_1045]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2753,plain,
% 2.21/1.01      ( k7_relat_1(sK2,X0) = sK2
% 2.21/1.01      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 2.21/1.01      inference(renaming,[status(thm)],[c_2752]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2760,plain,
% 2.21/1.01      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_744,c_2753]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_742,plain,
% 2.21/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.21/1.01      | v1_relat_1(X1) != iProver_top
% 2.21/1.01      | v1_relat_1(X0) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1715,plain,
% 2.21/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.21/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_731,c_742]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1968,plain,
% 2.21/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_1715,c_22,c_1010,c_1045]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_8,plain,
% 2.21/1.01      ( ~ v1_relat_1(X0)
% 2.21/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.21/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_740,plain,
% 2.21/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1974,plain,
% 2.21/1.01      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1968,c_740]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2875,plain,
% 2.21/1.01      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_2760,c_1974]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_12,plain,
% 2.21/1.01      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 2.21/1.01      | ~ r1_tarski(X0,k1_relat_1(X1))
% 2.21/1.01      | ~ v1_relat_1(X1) ),
% 2.21/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_737,plain,
% 2.21/1.01      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 2.21/1.01      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 2.21/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2877,plain,
% 2.21/1.01      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
% 2.21/1.01      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.21/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_2875,c_737]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_925,plain,
% 2.21/1.01      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1486,plain,
% 2.21/1.01      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_925]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1487,plain,
% 2.21/1.01      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_4466,plain,
% 2.21/1.01      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_2877,c_22,c_1010,c_1045,c_1487]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_13,plain,
% 2.21/1.01      ( v5_relat_1(X0,X1)
% 2.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.21/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_6,plain,
% 2.21/1.01      ( ~ v5_relat_1(X0,X1)
% 2.21/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 2.21/1.01      | ~ v1_relat_1(X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_263,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 2.21/1.01      | ~ v1_relat_1(X0) ),
% 2.21/1.01      inference(resolution,[status(thm)],[c_13,c_6]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_729,plain,
% 2.21/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.21/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 2.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1105,plain,
% 2.21/1.01      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
% 2.21/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_731,c_729]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1468,plain,
% 2.21/1.01      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_1105,c_22,c_1010,c_1045]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3,plain,
% 2.21/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.21/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_743,plain,
% 2.21/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1474,plain,
% 2.21/1.01      ( k3_xboole_0(k2_relat_1(sK2),sK0) = k2_relat_1(sK2) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1468,c_743]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_10,plain,
% 2.21/1.01      ( ~ v1_relat_1(X0)
% 2.21/1.01      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 2.21/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_738,plain,
% 2.21/1.01      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 2.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1973,plain,
% 2.21/1.01      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1968,c_738]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2125,plain,
% 2.21/1.01      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK0) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1474,c_1973]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_4470,plain,
% 2.21/1.01      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) = iProver_top ),
% 2.21/1.01      inference(light_normalisation,[status(thm)],[c_4466,c_2125]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_0,plain,
% 2.21/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.21/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2101,plain,
% 2.21/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.21/1.01      | ~ r1_tarski(k1_relat_1(X1),X0)
% 2.21/1.01      | X0 = k1_relat_1(X1) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3548,plain,
% 2.21/1.01      ( ~ r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
% 2.21/1.01      | ~ r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0))
% 2.21/1.01      | k10_relat_1(sK2,X0) = k1_relat_1(sK2) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_2101]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3549,plain,
% 2.21/1.01      ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
% 2.21/1.01      | r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) != iProver_top
% 2.21/1.01      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_3548]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3551,plain,
% 2.21/1.01      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2)
% 2.21/1.01      | r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) != iProver_top
% 2.21/1.01      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) != iProver_top ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_3549]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2761,plain,
% 2.21/1.01      ( k7_relat_1(sK2,k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(sK2)))) = sK2
% 2.21/1.01      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
% 2.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_737,c_2753]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3286,plain,
% 2.21/1.01      ( k7_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))) = sK2
% 2.21/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_744,c_2761]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3287,plain,
% 2.21/1.01      ( k7_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK2
% 2.21/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.21/1.01      inference(light_normalisation,[status(thm)],[c_3286,c_2125,c_2875]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3497,plain,
% 2.21/1.01      ( k7_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK2 ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_3287,c_22,c_1010,c_1045]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3500,plain,
% 2.21/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k2_relat_1(sK2) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_3497,c_1974]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_18,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.21/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_733,plain,
% 2.21/1.01      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.21/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1720,plain,
% 2.21/1.01      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_731,c_733]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_15,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_736,plain,
% 2.21/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.21/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1174,plain,
% 2.21/1.01      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_731,c_736]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_16,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_735,plain,
% 2.21/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.21/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1170,plain,
% 2.21/1.01      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_731,c_735]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_20,negated_conjecture,
% 2.21/1.01      ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
% 2.21/1.01      | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
% 2.21/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1247,plain,
% 2.21/1.01      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.21/1.01      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.21/1.01      inference(demodulation,[status(thm)],[c_1170,c_20]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1383,plain,
% 2.21/1.01      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
% 2.21/1.01      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.21/1.01      inference(demodulation,[status(thm)],[c_1174,c_1247]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1896,plain,
% 2.21/1.01      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 2.21/1.01      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
% 2.21/1.01      inference(demodulation,[status(thm)],[c_1720,c_1383]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1897,plain,
% 2.21/1.01      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 2.21/1.01      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
% 2.21/1.01      inference(demodulation,[status(thm)],[c_1896,c_1720]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_17,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.21/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_734,plain,
% 2.21/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.21/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1798,plain,
% 2.21/1.01      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_731,c_734]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2131,plain,
% 2.21/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
% 2.21/1.01      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.21/1.01      inference(demodulation,[status(thm)],[c_1897,c_1798]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1617,plain,
% 2.21/1.01      ( k7_relat_1(sK2,sK1) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_731,c_730]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1305,plain,
% 2.21/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.21/1.01      | ~ v1_relat_1(sK2)
% 2.21/1.01      | k7_relat_1(sK2,X0) = sK2 ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_245]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1504,plain,
% 2.21/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.21/1.01      | ~ v1_relat_1(sK2)
% 2.21/1.01      | k7_relat_1(sK2,sK1) = sK2 ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_1305]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1964,plain,
% 2.21/1.01      ( k7_relat_1(sK2,sK1) = sK2 ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_1617,c_21,c_1009,c_1044,c_1504]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2046,plain,
% 2.21/1.01      ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1964,c_1974]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2132,plain,
% 2.21/1.01      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 2.21/1.01      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.21/1.01      inference(light_normalisation,[status(thm)],[c_2131,c_2046]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2964,plain,
% 2.21/1.01      ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
% 2.21/1.01      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.21/1.01      inference(demodulation,[status(thm)],[c_2125,c_2132]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_9,plain,
% 2.21/1.01      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1304,plain,
% 2.21/1.01      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
% 2.21/1.01      | ~ v1_relat_1(sK2) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1323,plain,
% 2.21/1.01      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top
% 2.21/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1304]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1325,plain,
% 2.21/1.01      ( r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) = iProver_top
% 2.21/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_1323]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(contradiction,plain,
% 2.21/1.01      ( $false ),
% 2.21/1.01      inference(minisat,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_4470,c_3551,c_3500,c_2964,c_1325,c_1045,c_1010,c_22]) ).
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/1.01  
% 2.21/1.01  ------                               Statistics
% 2.21/1.01  
% 2.21/1.01  ------ General
% 2.21/1.01  
% 2.21/1.01  abstr_ref_over_cycles:                  0
% 2.21/1.01  abstr_ref_under_cycles:                 0
% 2.21/1.01  gc_basic_clause_elim:                   0
% 2.21/1.01  forced_gc_time:                         0
% 2.21/1.01  parsing_time:                           0.016
% 2.21/1.01  unif_index_cands_time:                  0.
% 2.21/1.01  unif_index_add_time:                    0.
% 2.21/1.01  orderings_time:                         0.
% 2.21/1.01  out_proof_time:                         0.016
% 2.21/1.01  total_time:                             0.179
% 2.21/1.01  num_of_symbols:                         51
% 2.21/1.01  num_of_terms:                           4280
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing
% 2.21/1.01  
% 2.21/1.01  num_of_splits:                          0
% 2.21/1.01  num_of_split_atoms:                     0
% 2.21/1.01  num_of_reused_defs:                     0
% 2.21/1.01  num_eq_ax_congr_red:                    25
% 2.21/1.01  num_of_sem_filtered_clauses:            1
% 2.21/1.01  num_of_subtypes:                        0
% 2.21/1.01  monotx_restored_types:                  0
% 2.21/1.01  sat_num_of_epr_types:                   0
% 2.21/1.01  sat_num_of_non_cyclic_types:            0
% 2.21/1.01  sat_guarded_non_collapsed_types:        0
% 2.21/1.01  num_pure_diseq_elim:                    0
% 2.21/1.01  simp_replaced_by:                       0
% 2.21/1.01  res_preprocessed:                       104
% 2.21/1.01  prep_upred:                             0
% 2.21/1.01  prep_unflattend:                        0
% 2.21/1.01  smt_new_axioms:                         0
% 2.21/1.01  pred_elim_cands:                        3
% 2.21/1.01  pred_elim:                              2
% 2.21/1.01  pred_elim_cl:                           3
% 2.21/1.01  pred_elim_cycles:                       4
% 2.21/1.01  merged_defs:                            0
% 2.21/1.01  merged_defs_ncl:                        0
% 2.21/1.01  bin_hyper_res:                          0
% 2.21/1.01  prep_cycles:                            4
% 2.21/1.01  pred_elim_time:                         0.001
% 2.21/1.01  splitting_time:                         0.
% 2.21/1.01  sem_filter_time:                        0.
% 2.21/1.01  monotx_time:                            0.
% 2.21/1.01  subtype_inf_time:                       0.
% 2.21/1.01  
% 2.21/1.01  ------ Problem properties
% 2.21/1.01  
% 2.21/1.01  clauses:                                18
% 2.21/1.01  conjectures:                            2
% 2.21/1.01  epr:                                    2
% 2.21/1.01  horn:                                   18
% 2.21/1.01  ground:                                 2
% 2.21/1.01  unary:                                  3
% 2.21/1.01  binary:                                 9
% 2.21/1.01  lits:                                   39
% 2.21/1.01  lits_eq:                                11
% 2.21/1.01  fd_pure:                                0
% 2.21/1.01  fd_pseudo:                              0
% 2.21/1.01  fd_cond:                                0
% 2.21/1.01  fd_pseudo_cond:                         1
% 2.21/1.01  ac_symbols:                             0
% 2.21/1.01  
% 2.21/1.01  ------ Propositional Solver
% 2.21/1.01  
% 2.21/1.01  prop_solver_calls:                      30
% 2.21/1.01  prop_fast_solver_calls:                 662
% 2.21/1.01  smt_solver_calls:                       0
% 2.21/1.01  smt_fast_solver_calls:                  0
% 2.21/1.01  prop_num_of_clauses:                    1970
% 2.21/1.01  prop_preprocess_simplified:             5365
% 2.21/1.01  prop_fo_subsumed:                       13
% 2.21/1.01  prop_solver_time:                       0.
% 2.21/1.01  smt_solver_time:                        0.
% 2.21/1.01  smt_fast_solver_time:                   0.
% 2.21/1.01  prop_fast_solver_time:                  0.
% 2.21/1.01  prop_unsat_core_time:                   0.
% 2.21/1.01  
% 2.21/1.01  ------ QBF
% 2.21/1.01  
% 2.21/1.01  qbf_q_res:                              0
% 2.21/1.01  qbf_num_tautologies:                    0
% 2.21/1.01  qbf_prep_cycles:                        0
% 2.21/1.01  
% 2.21/1.01  ------ BMC1
% 2.21/1.01  
% 2.21/1.01  bmc1_current_bound:                     -1
% 2.21/1.01  bmc1_last_solved_bound:                 -1
% 2.21/1.01  bmc1_unsat_core_size:                   -1
% 2.21/1.01  bmc1_unsat_core_parents_size:           -1
% 2.21/1.01  bmc1_merge_next_fun:                    0
% 2.21/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.21/1.01  
% 2.21/1.01  ------ Instantiation
% 2.21/1.01  
% 2.21/1.01  inst_num_of_clauses:                    653
% 2.21/1.01  inst_num_in_passive:                    255
% 2.21/1.01  inst_num_in_active:                     334
% 2.21/1.01  inst_num_in_unprocessed:                64
% 2.21/1.01  inst_num_of_loops:                      350
% 2.21/1.01  inst_num_of_learning_restarts:          0
% 2.21/1.01  inst_num_moves_active_passive:          12
% 2.21/1.01  inst_lit_activity:                      0
% 2.21/1.01  inst_lit_activity_moves:                0
% 2.21/1.01  inst_num_tautologies:                   0
% 2.21/1.01  inst_num_prop_implied:                  0
% 2.21/1.01  inst_num_existing_simplified:           0
% 2.21/1.01  inst_num_eq_res_simplified:             0
% 2.21/1.01  inst_num_child_elim:                    0
% 2.21/1.01  inst_num_of_dismatching_blockings:      138
% 2.21/1.01  inst_num_of_non_proper_insts:           686
% 2.21/1.01  inst_num_of_duplicates:                 0
% 2.21/1.01  inst_inst_num_from_inst_to_res:         0
% 2.21/1.01  inst_dismatching_checking_time:         0.
% 2.21/1.01  
% 2.21/1.01  ------ Resolution
% 2.21/1.01  
% 2.21/1.01  res_num_of_clauses:                     0
% 2.21/1.01  res_num_in_passive:                     0
% 2.21/1.01  res_num_in_active:                      0
% 2.21/1.01  res_num_of_loops:                       108
% 2.21/1.01  res_forward_subset_subsumed:            81
% 2.21/1.01  res_backward_subset_subsumed:           2
% 2.21/1.01  res_forward_subsumed:                   0
% 2.21/1.01  res_backward_subsumed:                  0
% 2.21/1.01  res_forward_subsumption_resolution:     0
% 2.21/1.01  res_backward_subsumption_resolution:    0
% 2.21/1.01  res_clause_to_clause_subsumption:       191
% 2.21/1.01  res_orphan_elimination:                 0
% 2.21/1.01  res_tautology_del:                      51
% 2.21/1.01  res_num_eq_res_simplified:              0
% 2.21/1.01  res_num_sel_changes:                    0
% 2.21/1.01  res_moves_from_active_to_pass:          0
% 2.21/1.01  
% 2.21/1.01  ------ Superposition
% 2.21/1.01  
% 2.21/1.01  sup_time_total:                         0.
% 2.21/1.01  sup_time_generating:                    0.
% 2.21/1.01  sup_time_sim_full:                      0.
% 2.21/1.01  sup_time_sim_immed:                     0.
% 2.21/1.01  
% 2.21/1.01  sup_num_of_clauses:                     69
% 2.21/1.01  sup_num_in_active:                      65
% 2.21/1.01  sup_num_in_passive:                     4
% 2.21/1.01  sup_num_of_loops:                       69
% 2.21/1.01  sup_fw_superposition:                   40
% 2.21/1.01  sup_bw_superposition:                   26
% 2.21/1.01  sup_immediate_simplified:               20
% 2.21/1.01  sup_given_eliminated:                   0
% 2.21/1.01  comparisons_done:                       0
% 2.21/1.01  comparisons_avoided:                    0
% 2.21/1.01  
% 2.21/1.01  ------ Simplifications
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  sim_fw_subset_subsumed:                 2
% 2.21/1.01  sim_bw_subset_subsumed:                 0
% 2.21/1.01  sim_fw_subsumed:                        9
% 2.21/1.01  sim_bw_subsumed:                        0
% 2.21/1.01  sim_fw_subsumption_res:                 0
% 2.21/1.01  sim_bw_subsumption_res:                 0
% 2.21/1.01  sim_tautology_del:                      0
% 2.21/1.01  sim_eq_tautology_del:                   3
% 2.21/1.01  sim_eq_res_simp:                        0
% 2.21/1.01  sim_fw_demodulated:                     5
% 2.21/1.01  sim_bw_demodulated:                     4
% 2.21/1.01  sim_light_normalised:                   12
% 2.21/1.01  sim_joinable_taut:                      0
% 2.21/1.01  sim_joinable_simp:                      0
% 2.21/1.01  sim_ac_normalised:                      0
% 2.21/1.01  sim_smt_subsumption:                    0
% 2.21/1.01  
%------------------------------------------------------------------------------
