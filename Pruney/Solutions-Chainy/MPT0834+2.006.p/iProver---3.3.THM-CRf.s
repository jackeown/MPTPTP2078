%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:00 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 315 expanded)
%              Number of clauses        :   92 ( 133 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  339 ( 727 expanded)
%              Number of equality atoms :  170 ( 356 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f53])).

fof(f87,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1808,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_25,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_25,c_8])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_409,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_24])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_409])).

cnf(c_1807,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_2129,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1808,c_1807])).

cnf(c_17,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1827,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6026,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1827])).

cnf(c_21,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_61,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7690,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6026,c_61])).

cnf(c_7691,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7690])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1820,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7696,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7691,c_1820])).

cnf(c_1825,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1818,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3202,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_1825,c_1818])).

cnf(c_23,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3210,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_3202,c_23])).

cnf(c_7701,plain,
    ( k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7696,c_3210])).

cnf(c_21389,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7701,c_61])).

cnf(c_21390,plain,
    ( k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_21389])).

cnf(c_21402,plain,
    ( k6_relat_1(k3_xboole_0(k2_relat_1(sK2),sK1)) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2129,c_21390])).

cnf(c_16,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_21782,plain,
    ( k3_xboole_0(k2_relat_1(sK2),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_21402,c_16])).

cnf(c_21807,plain,
    ( k3_xboole_0(k2_relat_1(sK2),sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_21782,c_16])).

cnf(c_1815,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2404,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1808,c_1815])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1821,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4278,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2404,c_1821])).

cnf(c_23098,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_21807,c_4278])).

cnf(c_12,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1822,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1824,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2566,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2404,c_1824])).

cnf(c_22,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1816,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7715,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2566,c_1816])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2011,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2012,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2011])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2066,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2363,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2066])).

cnf(c_2366,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2363])).

cnf(c_9798,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7715,c_34,c_2012,c_2366])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1831,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9803,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9798,c_1831])).

cnf(c_12335,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1822,c_9803])).

cnf(c_12657,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12335,c_34,c_2012])).

cnf(c_23100,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_23098,c_12657])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1811,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5770,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1808,c_1811])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1813,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4817,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1808,c_1813])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1812,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4350,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1808,c_1812])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4434,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4350,c_32])).

cnf(c_5131,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4817,c_4434])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1810,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4956,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1808,c_1810])).

cnf(c_5285,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5131,c_4956])).

cnf(c_6357,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5770,c_5285])).

cnf(c_26,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1814,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3844,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1808,c_1814])).

cnf(c_4937,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3844,c_1820])).

cnf(c_2019,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2147,plain,
    ( ~ v4_relat_1(sK2,X0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2167,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK0) = sK2 ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_5289,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4937,c_33,c_2011,c_2019,c_2167])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1823,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3328,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2404,c_1823])).

cnf(c_5292,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5289,c_3328])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23100,c_6357,c_5292])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:07:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.16/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.16/1.49  
% 7.16/1.49  ------  iProver source info
% 7.16/1.49  
% 7.16/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.16/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.16/1.49  git: non_committed_changes: false
% 7.16/1.49  git: last_make_outside_of_git: false
% 7.16/1.49  
% 7.16/1.49  ------ 
% 7.16/1.49  
% 7.16/1.49  ------ Input Options
% 7.16/1.49  
% 7.16/1.49  --out_options                           all
% 7.16/1.49  --tptp_safe_out                         true
% 7.16/1.49  --problem_path                          ""
% 7.16/1.49  --include_path                          ""
% 7.16/1.49  --clausifier                            res/vclausify_rel
% 7.16/1.49  --clausifier_options                    --mode clausify
% 7.16/1.49  --stdin                                 false
% 7.16/1.49  --stats_out                             all
% 7.16/1.49  
% 7.16/1.49  ------ General Options
% 7.16/1.49  
% 7.16/1.49  --fof                                   false
% 7.16/1.49  --time_out_real                         305.
% 7.16/1.49  --time_out_virtual                      -1.
% 7.16/1.49  --symbol_type_check                     false
% 7.16/1.49  --clausify_out                          false
% 7.16/1.49  --sig_cnt_out                           false
% 7.16/1.49  --trig_cnt_out                          false
% 7.16/1.49  --trig_cnt_out_tolerance                1.
% 7.16/1.49  --trig_cnt_out_sk_spl                   false
% 7.16/1.49  --abstr_cl_out                          false
% 7.16/1.49  
% 7.16/1.49  ------ Global Options
% 7.16/1.49  
% 7.16/1.49  --schedule                              default
% 7.16/1.49  --add_important_lit                     false
% 7.16/1.49  --prop_solver_per_cl                    1000
% 7.16/1.49  --min_unsat_core                        false
% 7.16/1.49  --soft_assumptions                      false
% 7.16/1.49  --soft_lemma_size                       3
% 7.16/1.49  --prop_impl_unit_size                   0
% 7.16/1.49  --prop_impl_unit                        []
% 7.16/1.49  --share_sel_clauses                     true
% 7.16/1.49  --reset_solvers                         false
% 7.16/1.49  --bc_imp_inh                            [conj_cone]
% 7.16/1.49  --conj_cone_tolerance                   3.
% 7.16/1.49  --extra_neg_conj                        none
% 7.16/1.49  --large_theory_mode                     true
% 7.16/1.49  --prolific_symb_bound                   200
% 7.16/1.49  --lt_threshold                          2000
% 7.16/1.49  --clause_weak_htbl                      true
% 7.16/1.49  --gc_record_bc_elim                     false
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing Options
% 7.16/1.49  
% 7.16/1.49  --preprocessing_flag                    true
% 7.16/1.49  --time_out_prep_mult                    0.1
% 7.16/1.49  --splitting_mode                        input
% 7.16/1.49  --splitting_grd                         true
% 7.16/1.49  --splitting_cvd                         false
% 7.16/1.49  --splitting_cvd_svl                     false
% 7.16/1.49  --splitting_nvd                         32
% 7.16/1.49  --sub_typing                            true
% 7.16/1.49  --prep_gs_sim                           true
% 7.16/1.49  --prep_unflatten                        true
% 7.16/1.49  --prep_res_sim                          true
% 7.16/1.49  --prep_upred                            true
% 7.16/1.49  --prep_sem_filter                       exhaustive
% 7.16/1.49  --prep_sem_filter_out                   false
% 7.16/1.49  --pred_elim                             true
% 7.16/1.49  --res_sim_input                         true
% 7.16/1.49  --eq_ax_congr_red                       true
% 7.16/1.49  --pure_diseq_elim                       true
% 7.16/1.49  --brand_transform                       false
% 7.16/1.49  --non_eq_to_eq                          false
% 7.16/1.49  --prep_def_merge                        true
% 7.16/1.49  --prep_def_merge_prop_impl              false
% 7.16/1.49  --prep_def_merge_mbd                    true
% 7.16/1.49  --prep_def_merge_tr_red                 false
% 7.16/1.49  --prep_def_merge_tr_cl                  false
% 7.16/1.49  --smt_preprocessing                     true
% 7.16/1.49  --smt_ac_axioms                         fast
% 7.16/1.49  --preprocessed_out                      false
% 7.16/1.49  --preprocessed_stats                    false
% 7.16/1.49  
% 7.16/1.49  ------ Abstraction refinement Options
% 7.16/1.49  
% 7.16/1.49  --abstr_ref                             []
% 7.16/1.49  --abstr_ref_prep                        false
% 7.16/1.49  --abstr_ref_until_sat                   false
% 7.16/1.49  --abstr_ref_sig_restrict                funpre
% 7.16/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.16/1.49  --abstr_ref_under                       []
% 7.16/1.49  
% 7.16/1.49  ------ SAT Options
% 7.16/1.49  
% 7.16/1.49  --sat_mode                              false
% 7.16/1.49  --sat_fm_restart_options                ""
% 7.16/1.49  --sat_gr_def                            false
% 7.16/1.49  --sat_epr_types                         true
% 7.16/1.49  --sat_non_cyclic_types                  false
% 7.16/1.49  --sat_finite_models                     false
% 7.16/1.49  --sat_fm_lemmas                         false
% 7.16/1.49  --sat_fm_prep                           false
% 7.16/1.49  --sat_fm_uc_incr                        true
% 7.16/1.49  --sat_out_model                         small
% 7.16/1.49  --sat_out_clauses                       false
% 7.16/1.49  
% 7.16/1.49  ------ QBF Options
% 7.16/1.49  
% 7.16/1.49  --qbf_mode                              false
% 7.16/1.49  --qbf_elim_univ                         false
% 7.16/1.49  --qbf_dom_inst                          none
% 7.16/1.49  --qbf_dom_pre_inst                      false
% 7.16/1.49  --qbf_sk_in                             false
% 7.16/1.49  --qbf_pred_elim                         true
% 7.16/1.49  --qbf_split                             512
% 7.16/1.49  
% 7.16/1.49  ------ BMC1 Options
% 7.16/1.49  
% 7.16/1.49  --bmc1_incremental                      false
% 7.16/1.49  --bmc1_axioms                           reachable_all
% 7.16/1.49  --bmc1_min_bound                        0
% 7.16/1.49  --bmc1_max_bound                        -1
% 7.16/1.49  --bmc1_max_bound_default                -1
% 7.16/1.49  --bmc1_symbol_reachability              true
% 7.16/1.49  --bmc1_property_lemmas                  false
% 7.16/1.49  --bmc1_k_induction                      false
% 7.16/1.49  --bmc1_non_equiv_states                 false
% 7.16/1.49  --bmc1_deadlock                         false
% 7.16/1.49  --bmc1_ucm                              false
% 7.16/1.49  --bmc1_add_unsat_core                   none
% 7.16/1.49  --bmc1_unsat_core_children              false
% 7.16/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.16/1.49  --bmc1_out_stat                         full
% 7.16/1.49  --bmc1_ground_init                      false
% 7.16/1.49  --bmc1_pre_inst_next_state              false
% 7.16/1.49  --bmc1_pre_inst_state                   false
% 7.16/1.49  --bmc1_pre_inst_reach_state             false
% 7.16/1.49  --bmc1_out_unsat_core                   false
% 7.16/1.49  --bmc1_aig_witness_out                  false
% 7.16/1.49  --bmc1_verbose                          false
% 7.16/1.49  --bmc1_dump_clauses_tptp                false
% 7.16/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.16/1.49  --bmc1_dump_file                        -
% 7.16/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.16/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.16/1.49  --bmc1_ucm_extend_mode                  1
% 7.16/1.49  --bmc1_ucm_init_mode                    2
% 7.16/1.49  --bmc1_ucm_cone_mode                    none
% 7.16/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.16/1.49  --bmc1_ucm_relax_model                  4
% 7.16/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.16/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.16/1.49  --bmc1_ucm_layered_model                none
% 7.16/1.49  --bmc1_ucm_max_lemma_size               10
% 7.16/1.49  
% 7.16/1.49  ------ AIG Options
% 7.16/1.49  
% 7.16/1.49  --aig_mode                              false
% 7.16/1.49  
% 7.16/1.49  ------ Instantiation Options
% 7.16/1.49  
% 7.16/1.49  --instantiation_flag                    true
% 7.16/1.49  --inst_sos_flag                         false
% 7.16/1.49  --inst_sos_phase                        true
% 7.16/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel_side                     num_symb
% 7.16/1.49  --inst_solver_per_active                1400
% 7.16/1.49  --inst_solver_calls_frac                1.
% 7.16/1.49  --inst_passive_queue_type               priority_queues
% 7.16/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.16/1.49  --inst_passive_queues_freq              [25;2]
% 7.16/1.49  --inst_dismatching                      true
% 7.16/1.49  --inst_eager_unprocessed_to_passive     true
% 7.16/1.49  --inst_prop_sim_given                   true
% 7.16/1.49  --inst_prop_sim_new                     false
% 7.16/1.49  --inst_subs_new                         false
% 7.16/1.49  --inst_eq_res_simp                      false
% 7.16/1.49  --inst_subs_given                       false
% 7.16/1.49  --inst_orphan_elimination               true
% 7.16/1.49  --inst_learning_loop_flag               true
% 7.16/1.49  --inst_learning_start                   3000
% 7.16/1.49  --inst_learning_factor                  2
% 7.16/1.49  --inst_start_prop_sim_after_learn       3
% 7.16/1.49  --inst_sel_renew                        solver
% 7.16/1.49  --inst_lit_activity_flag                true
% 7.16/1.49  --inst_restr_to_given                   false
% 7.16/1.49  --inst_activity_threshold               500
% 7.16/1.49  --inst_out_proof                        true
% 7.16/1.49  
% 7.16/1.49  ------ Resolution Options
% 7.16/1.49  
% 7.16/1.49  --resolution_flag                       true
% 7.16/1.49  --res_lit_sel                           adaptive
% 7.16/1.49  --res_lit_sel_side                      none
% 7.16/1.49  --res_ordering                          kbo
% 7.16/1.49  --res_to_prop_solver                    active
% 7.16/1.49  --res_prop_simpl_new                    false
% 7.16/1.49  --res_prop_simpl_given                  true
% 7.16/1.49  --res_passive_queue_type                priority_queues
% 7.16/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.16/1.49  --res_passive_queues_freq               [15;5]
% 7.16/1.49  --res_forward_subs                      full
% 7.16/1.49  --res_backward_subs                     full
% 7.16/1.49  --res_forward_subs_resolution           true
% 7.16/1.49  --res_backward_subs_resolution          true
% 7.16/1.49  --res_orphan_elimination                true
% 7.16/1.49  --res_time_limit                        2.
% 7.16/1.49  --res_out_proof                         true
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Options
% 7.16/1.49  
% 7.16/1.49  --superposition_flag                    true
% 7.16/1.49  --sup_passive_queue_type                priority_queues
% 7.16/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.16/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.16/1.49  --demod_completeness_check              fast
% 7.16/1.49  --demod_use_ground                      true
% 7.16/1.49  --sup_to_prop_solver                    passive
% 7.16/1.49  --sup_prop_simpl_new                    true
% 7.16/1.49  --sup_prop_simpl_given                  true
% 7.16/1.49  --sup_fun_splitting                     false
% 7.16/1.49  --sup_smt_interval                      50000
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Simplification Setup
% 7.16/1.49  
% 7.16/1.49  --sup_indices_passive                   []
% 7.16/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.16/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.16/1.49  --sup_full_bw                           [BwDemod]
% 7.16/1.49  --sup_immed_triv                        [TrivRules]
% 7.16/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.16/1.49  --sup_immed_bw_main                     []
% 7.16/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.16/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.16/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.16/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.16/1.49  
% 7.16/1.49  ------ Combination Options
% 7.16/1.49  
% 7.16/1.49  --comb_res_mult                         3
% 7.16/1.49  --comb_sup_mult                         2
% 7.16/1.49  --comb_inst_mult                        10
% 7.16/1.49  
% 7.16/1.49  ------ Debug Options
% 7.16/1.49  
% 7.16/1.49  --dbg_backtrace                         false
% 7.16/1.49  --dbg_dump_prop_clauses                 false
% 7.16/1.49  --dbg_dump_prop_clauses_file            -
% 7.16/1.49  --dbg_out_stat                          false
% 7.16/1.49  ------ Parsing...
% 7.16/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.16/1.49  ------ Proving...
% 7.16/1.49  ------ Problem Properties 
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  clauses                                 30
% 7.16/1.49  conjectures                             2
% 7.16/1.49  EPR                                     3
% 7.16/1.49  Horn                                    30
% 7.16/1.49  unary                                   8
% 7.16/1.49  binary                                  15
% 7.16/1.49  lits                                    60
% 7.16/1.49  lits eq                                 15
% 7.16/1.49  fd_pure                                 0
% 7.16/1.49  fd_pseudo                               0
% 7.16/1.49  fd_cond                                 0
% 7.16/1.49  fd_pseudo_cond                          1
% 7.16/1.49  AC symbols                              0
% 7.16/1.49  
% 7.16/1.49  ------ Schedule dynamic 5 is on 
% 7.16/1.49  
% 7.16/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  ------ 
% 7.16/1.49  Current options:
% 7.16/1.49  ------ 
% 7.16/1.49  
% 7.16/1.49  ------ Input Options
% 7.16/1.49  
% 7.16/1.49  --out_options                           all
% 7.16/1.49  --tptp_safe_out                         true
% 7.16/1.49  --problem_path                          ""
% 7.16/1.49  --include_path                          ""
% 7.16/1.49  --clausifier                            res/vclausify_rel
% 7.16/1.49  --clausifier_options                    --mode clausify
% 7.16/1.49  --stdin                                 false
% 7.16/1.49  --stats_out                             all
% 7.16/1.49  
% 7.16/1.49  ------ General Options
% 7.16/1.49  
% 7.16/1.49  --fof                                   false
% 7.16/1.49  --time_out_real                         305.
% 7.16/1.49  --time_out_virtual                      -1.
% 7.16/1.49  --symbol_type_check                     false
% 7.16/1.49  --clausify_out                          false
% 7.16/1.49  --sig_cnt_out                           false
% 7.16/1.49  --trig_cnt_out                          false
% 7.16/1.49  --trig_cnt_out_tolerance                1.
% 7.16/1.49  --trig_cnt_out_sk_spl                   false
% 7.16/1.49  --abstr_cl_out                          false
% 7.16/1.49  
% 7.16/1.49  ------ Global Options
% 7.16/1.49  
% 7.16/1.49  --schedule                              default
% 7.16/1.49  --add_important_lit                     false
% 7.16/1.49  --prop_solver_per_cl                    1000
% 7.16/1.49  --min_unsat_core                        false
% 7.16/1.49  --soft_assumptions                      false
% 7.16/1.49  --soft_lemma_size                       3
% 7.16/1.49  --prop_impl_unit_size                   0
% 7.16/1.49  --prop_impl_unit                        []
% 7.16/1.49  --share_sel_clauses                     true
% 7.16/1.49  --reset_solvers                         false
% 7.16/1.49  --bc_imp_inh                            [conj_cone]
% 7.16/1.49  --conj_cone_tolerance                   3.
% 7.16/1.49  --extra_neg_conj                        none
% 7.16/1.49  --large_theory_mode                     true
% 7.16/1.49  --prolific_symb_bound                   200
% 7.16/1.49  --lt_threshold                          2000
% 7.16/1.49  --clause_weak_htbl                      true
% 7.16/1.49  --gc_record_bc_elim                     false
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing Options
% 7.16/1.49  
% 7.16/1.49  --preprocessing_flag                    true
% 7.16/1.49  --time_out_prep_mult                    0.1
% 7.16/1.49  --splitting_mode                        input
% 7.16/1.49  --splitting_grd                         true
% 7.16/1.49  --splitting_cvd                         false
% 7.16/1.49  --splitting_cvd_svl                     false
% 7.16/1.49  --splitting_nvd                         32
% 7.16/1.49  --sub_typing                            true
% 7.16/1.49  --prep_gs_sim                           true
% 7.16/1.49  --prep_unflatten                        true
% 7.16/1.49  --prep_res_sim                          true
% 7.16/1.49  --prep_upred                            true
% 7.16/1.49  --prep_sem_filter                       exhaustive
% 7.16/1.49  --prep_sem_filter_out                   false
% 7.16/1.49  --pred_elim                             true
% 7.16/1.49  --res_sim_input                         true
% 7.16/1.49  --eq_ax_congr_red                       true
% 7.16/1.49  --pure_diseq_elim                       true
% 7.16/1.49  --brand_transform                       false
% 7.16/1.49  --non_eq_to_eq                          false
% 7.16/1.49  --prep_def_merge                        true
% 7.16/1.49  --prep_def_merge_prop_impl              false
% 7.16/1.49  --prep_def_merge_mbd                    true
% 7.16/1.49  --prep_def_merge_tr_red                 false
% 7.16/1.49  --prep_def_merge_tr_cl                  false
% 7.16/1.49  --smt_preprocessing                     true
% 7.16/1.49  --smt_ac_axioms                         fast
% 7.16/1.49  --preprocessed_out                      false
% 7.16/1.49  --preprocessed_stats                    false
% 7.16/1.49  
% 7.16/1.49  ------ Abstraction refinement Options
% 7.16/1.49  
% 7.16/1.49  --abstr_ref                             []
% 7.16/1.49  --abstr_ref_prep                        false
% 7.16/1.49  --abstr_ref_until_sat                   false
% 7.16/1.49  --abstr_ref_sig_restrict                funpre
% 7.16/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.16/1.49  --abstr_ref_under                       []
% 7.16/1.49  
% 7.16/1.49  ------ SAT Options
% 7.16/1.49  
% 7.16/1.49  --sat_mode                              false
% 7.16/1.49  --sat_fm_restart_options                ""
% 7.16/1.49  --sat_gr_def                            false
% 7.16/1.49  --sat_epr_types                         true
% 7.16/1.49  --sat_non_cyclic_types                  false
% 7.16/1.49  --sat_finite_models                     false
% 7.16/1.49  --sat_fm_lemmas                         false
% 7.16/1.49  --sat_fm_prep                           false
% 7.16/1.49  --sat_fm_uc_incr                        true
% 7.16/1.49  --sat_out_model                         small
% 7.16/1.49  --sat_out_clauses                       false
% 7.16/1.49  
% 7.16/1.49  ------ QBF Options
% 7.16/1.49  
% 7.16/1.49  --qbf_mode                              false
% 7.16/1.49  --qbf_elim_univ                         false
% 7.16/1.49  --qbf_dom_inst                          none
% 7.16/1.49  --qbf_dom_pre_inst                      false
% 7.16/1.49  --qbf_sk_in                             false
% 7.16/1.49  --qbf_pred_elim                         true
% 7.16/1.49  --qbf_split                             512
% 7.16/1.49  
% 7.16/1.49  ------ BMC1 Options
% 7.16/1.49  
% 7.16/1.49  --bmc1_incremental                      false
% 7.16/1.49  --bmc1_axioms                           reachable_all
% 7.16/1.49  --bmc1_min_bound                        0
% 7.16/1.49  --bmc1_max_bound                        -1
% 7.16/1.49  --bmc1_max_bound_default                -1
% 7.16/1.49  --bmc1_symbol_reachability              true
% 7.16/1.49  --bmc1_property_lemmas                  false
% 7.16/1.49  --bmc1_k_induction                      false
% 7.16/1.49  --bmc1_non_equiv_states                 false
% 7.16/1.49  --bmc1_deadlock                         false
% 7.16/1.49  --bmc1_ucm                              false
% 7.16/1.49  --bmc1_add_unsat_core                   none
% 7.16/1.49  --bmc1_unsat_core_children              false
% 7.16/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.16/1.49  --bmc1_out_stat                         full
% 7.16/1.49  --bmc1_ground_init                      false
% 7.16/1.49  --bmc1_pre_inst_next_state              false
% 7.16/1.49  --bmc1_pre_inst_state                   false
% 7.16/1.49  --bmc1_pre_inst_reach_state             false
% 7.16/1.49  --bmc1_out_unsat_core                   false
% 7.16/1.49  --bmc1_aig_witness_out                  false
% 7.16/1.49  --bmc1_verbose                          false
% 7.16/1.49  --bmc1_dump_clauses_tptp                false
% 7.16/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.16/1.49  --bmc1_dump_file                        -
% 7.16/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.16/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.16/1.49  --bmc1_ucm_extend_mode                  1
% 7.16/1.49  --bmc1_ucm_init_mode                    2
% 7.16/1.49  --bmc1_ucm_cone_mode                    none
% 7.16/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.16/1.49  --bmc1_ucm_relax_model                  4
% 7.16/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.16/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.16/1.49  --bmc1_ucm_layered_model                none
% 7.16/1.49  --bmc1_ucm_max_lemma_size               10
% 7.16/1.49  
% 7.16/1.49  ------ AIG Options
% 7.16/1.49  
% 7.16/1.49  --aig_mode                              false
% 7.16/1.49  
% 7.16/1.49  ------ Instantiation Options
% 7.16/1.49  
% 7.16/1.49  --instantiation_flag                    true
% 7.16/1.49  --inst_sos_flag                         false
% 7.16/1.49  --inst_sos_phase                        true
% 7.16/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel_side                     none
% 7.16/1.49  --inst_solver_per_active                1400
% 7.16/1.49  --inst_solver_calls_frac                1.
% 7.16/1.49  --inst_passive_queue_type               priority_queues
% 7.16/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.16/1.49  --inst_passive_queues_freq              [25;2]
% 7.16/1.49  --inst_dismatching                      true
% 7.16/1.49  --inst_eager_unprocessed_to_passive     true
% 7.16/1.49  --inst_prop_sim_given                   true
% 7.16/1.49  --inst_prop_sim_new                     false
% 7.16/1.49  --inst_subs_new                         false
% 7.16/1.49  --inst_eq_res_simp                      false
% 7.16/1.49  --inst_subs_given                       false
% 7.16/1.49  --inst_orphan_elimination               true
% 7.16/1.49  --inst_learning_loop_flag               true
% 7.16/1.49  --inst_learning_start                   3000
% 7.16/1.49  --inst_learning_factor                  2
% 7.16/1.49  --inst_start_prop_sim_after_learn       3
% 7.16/1.49  --inst_sel_renew                        solver
% 7.16/1.49  --inst_lit_activity_flag                true
% 7.16/1.49  --inst_restr_to_given                   false
% 7.16/1.49  --inst_activity_threshold               500
% 7.16/1.49  --inst_out_proof                        true
% 7.16/1.49  
% 7.16/1.49  ------ Resolution Options
% 7.16/1.49  
% 7.16/1.49  --resolution_flag                       false
% 7.16/1.49  --res_lit_sel                           adaptive
% 7.16/1.49  --res_lit_sel_side                      none
% 7.16/1.49  --res_ordering                          kbo
% 7.16/1.49  --res_to_prop_solver                    active
% 7.16/1.49  --res_prop_simpl_new                    false
% 7.16/1.49  --res_prop_simpl_given                  true
% 7.16/1.49  --res_passive_queue_type                priority_queues
% 7.16/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.16/1.49  --res_passive_queues_freq               [15;5]
% 7.16/1.49  --res_forward_subs                      full
% 7.16/1.49  --res_backward_subs                     full
% 7.16/1.49  --res_forward_subs_resolution           true
% 7.16/1.49  --res_backward_subs_resolution          true
% 7.16/1.49  --res_orphan_elimination                true
% 7.16/1.49  --res_time_limit                        2.
% 7.16/1.49  --res_out_proof                         true
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Options
% 7.16/1.49  
% 7.16/1.49  --superposition_flag                    true
% 7.16/1.49  --sup_passive_queue_type                priority_queues
% 7.16/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.16/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.16/1.49  --demod_completeness_check              fast
% 7.16/1.49  --demod_use_ground                      true
% 7.16/1.49  --sup_to_prop_solver                    passive
% 7.16/1.49  --sup_prop_simpl_new                    true
% 7.16/1.49  --sup_prop_simpl_given                  true
% 7.16/1.49  --sup_fun_splitting                     false
% 7.16/1.49  --sup_smt_interval                      50000
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Simplification Setup
% 7.16/1.49  
% 7.16/1.49  --sup_indices_passive                   []
% 7.16/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.16/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.16/1.49  --sup_full_bw                           [BwDemod]
% 7.16/1.49  --sup_immed_triv                        [TrivRules]
% 7.16/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.16/1.49  --sup_immed_bw_main                     []
% 7.16/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.16/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.16/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.16/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.16/1.49  
% 7.16/1.49  ------ Combination Options
% 7.16/1.49  
% 7.16/1.49  --comb_res_mult                         3
% 7.16/1.49  --comb_sup_mult                         2
% 7.16/1.49  --comb_inst_mult                        10
% 7.16/1.49  
% 7.16/1.49  ------ Debug Options
% 7.16/1.49  
% 7.16/1.49  --dbg_backtrace                         false
% 7.16/1.49  --dbg_dump_prop_clauses                 false
% 7.16/1.49  --dbg_dump_prop_clauses_file            -
% 7.16/1.49  --dbg_out_stat                          false
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  ------ Proving...
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  % SZS status Theorem for theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  fof(f24,conjecture,(
% 7.16/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f25,negated_conjecture,(
% 7.16/1.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 7.16/1.49    inference(negated_conjecture,[],[f24])).
% 7.16/1.49  
% 7.16/1.49  fof(f47,plain,(
% 7.16/1.49    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.16/1.49    inference(ennf_transformation,[],[f25])).
% 7.16/1.49  
% 7.16/1.49  fof(f53,plain,(
% 7.16/1.49    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 7.16/1.49    introduced(choice_axiom,[])).
% 7.16/1.49  
% 7.16/1.49  fof(f54,plain,(
% 7.16/1.49    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.16/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f53])).
% 7.16/1.49  
% 7.16/1.49  fof(f87,plain,(
% 7.16/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.16/1.49    inference(cnf_transformation,[],[f54])).
% 7.16/1.49  
% 7.16/1.49  fof(f18,axiom,(
% 7.16/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f40,plain,(
% 7.16/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.16/1.49    inference(ennf_transformation,[],[f18])).
% 7.16/1.49  
% 7.16/1.49  fof(f81,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f40])).
% 7.16/1.49  
% 7.16/1.49  fof(f4,axiom,(
% 7.16/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f27,plain,(
% 7.16/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(ennf_transformation,[],[f4])).
% 7.16/1.49  
% 7.16/1.49  fof(f52,plain,(
% 7.16/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(nnf_transformation,[],[f27])).
% 7.16/1.49  
% 7.16/1.49  fof(f62,plain,(
% 7.16/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f52])).
% 7.16/1.49  
% 7.16/1.49  fof(f17,axiom,(
% 7.16/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f39,plain,(
% 7.16/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.16/1.49    inference(ennf_transformation,[],[f17])).
% 7.16/1.49  
% 7.16/1.49  fof(f79,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f39])).
% 7.16/1.49  
% 7.16/1.49  fof(f12,axiom,(
% 7.16/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f71,plain,(
% 7.16/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f12])).
% 7.16/1.49  
% 7.16/1.49  fof(f3,axiom,(
% 7.16/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f26,plain,(
% 7.16/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(ennf_transformation,[],[f3])).
% 7.16/1.49  
% 7.16/1.49  fof(f51,plain,(
% 7.16/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(nnf_transformation,[],[f26])).
% 7.16/1.49  
% 7.16/1.49  fof(f61,plain,(
% 7.16/1.49    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f51])).
% 7.16/1.49  
% 7.16/1.49  fof(f14,axiom,(
% 7.16/1.49    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f74,plain,(
% 7.16/1.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f14])).
% 7.16/1.49  
% 7.16/1.49  fof(f10,axiom,(
% 7.16/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f32,plain,(
% 7.16/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.16/1.49    inference(ennf_transformation,[],[f10])).
% 7.16/1.49  
% 7.16/1.49  fof(f33,plain,(
% 7.16/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(flattening,[],[f32])).
% 7.16/1.49  
% 7.16/1.49  fof(f69,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f33])).
% 7.16/1.49  
% 7.16/1.49  fof(f13,axiom,(
% 7.16/1.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f36,plain,(
% 7.16/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(ennf_transformation,[],[f13])).
% 7.16/1.49  
% 7.16/1.49  fof(f73,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f36])).
% 7.16/1.49  
% 7.16/1.49  fof(f16,axiom,(
% 7.16/1.49    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f78,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f16])).
% 7.16/1.49  
% 7.16/1.49  fof(f72,plain,(
% 7.16/1.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f12])).
% 7.16/1.49  
% 7.16/1.49  fof(f9,axiom,(
% 7.16/1.49    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f31,plain,(
% 7.16/1.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(ennf_transformation,[],[f9])).
% 7.16/1.49  
% 7.16/1.49  fof(f68,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f31])).
% 7.16/1.49  
% 7.16/1.49  fof(f8,axiom,(
% 7.16/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f30,plain,(
% 7.16/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(ennf_transformation,[],[f8])).
% 7.16/1.49  
% 7.16/1.49  fof(f67,plain,(
% 7.16/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f30])).
% 7.16/1.49  
% 7.16/1.49  fof(f6,axiom,(
% 7.16/1.49    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f28,plain,(
% 7.16/1.49    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.16/1.49    inference(ennf_transformation,[],[f6])).
% 7.16/1.49  
% 7.16/1.49  fof(f65,plain,(
% 7.16/1.49    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f28])).
% 7.16/1.49  
% 7.16/1.49  fof(f15,axiom,(
% 7.16/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f37,plain,(
% 7.16/1.49    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(ennf_transformation,[],[f15])).
% 7.16/1.49  
% 7.16/1.49  fof(f38,plain,(
% 7.16/1.49    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(flattening,[],[f37])).
% 7.16/1.49  
% 7.16/1.49  fof(f77,plain,(
% 7.16/1.49    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f38])).
% 7.16/1.49  
% 7.16/1.49  fof(f1,axiom,(
% 7.16/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f48,plain,(
% 7.16/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.16/1.49    inference(nnf_transformation,[],[f1])).
% 7.16/1.49  
% 7.16/1.49  fof(f49,plain,(
% 7.16/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.16/1.49    inference(flattening,[],[f48])).
% 7.16/1.49  
% 7.16/1.49  fof(f56,plain,(
% 7.16/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.16/1.49    inference(cnf_transformation,[],[f49])).
% 7.16/1.49  
% 7.16/1.49  fof(f89,plain,(
% 7.16/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.16/1.49    inference(equality_resolution,[],[f56])).
% 7.16/1.49  
% 7.16/1.49  fof(f57,plain,(
% 7.16/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f49])).
% 7.16/1.49  
% 7.16/1.49  fof(f21,axiom,(
% 7.16/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f43,plain,(
% 7.16/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.16/1.49    inference(ennf_transformation,[],[f21])).
% 7.16/1.49  
% 7.16/1.49  fof(f84,plain,(
% 7.16/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f43])).
% 7.16/1.49  
% 7.16/1.49  fof(f19,axiom,(
% 7.16/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f41,plain,(
% 7.16/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.16/1.49    inference(ennf_transformation,[],[f19])).
% 7.16/1.49  
% 7.16/1.49  fof(f82,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f41])).
% 7.16/1.49  
% 7.16/1.49  fof(f20,axiom,(
% 7.16/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f42,plain,(
% 7.16/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.16/1.49    inference(ennf_transformation,[],[f20])).
% 7.16/1.49  
% 7.16/1.49  fof(f83,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f42])).
% 7.16/1.49  
% 7.16/1.49  fof(f88,plain,(
% 7.16/1.49    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 7.16/1.49    inference(cnf_transformation,[],[f54])).
% 7.16/1.49  
% 7.16/1.49  fof(f22,axiom,(
% 7.16/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f44,plain,(
% 7.16/1.49    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.16/1.49    inference(ennf_transformation,[],[f22])).
% 7.16/1.49  
% 7.16/1.49  fof(f85,plain,(
% 7.16/1.49    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f44])).
% 7.16/1.49  
% 7.16/1.49  fof(f80,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f40])).
% 7.16/1.49  
% 7.16/1.49  fof(f7,axiom,(
% 7.16/1.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.16/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f29,plain,(
% 7.16/1.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.16/1.49    inference(ennf_transformation,[],[f7])).
% 7.16/1.49  
% 7.16/1.49  fof(f66,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f29])).
% 7.16/1.49  
% 7.16/1.49  cnf(c_33,negated_conjecture,
% 7.16/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.16/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1808,plain,
% 7.16/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_25,plain,
% 7.16/1.49      ( v5_relat_1(X0,X1)
% 7.16/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.16/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_8,plain,
% 7.16/1.49      ( ~ v5_relat_1(X0,X1)
% 7.16/1.49      | r1_tarski(k2_relat_1(X0),X1)
% 7.16/1.49      | ~ v1_relat_1(X0) ),
% 7.16/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_405,plain,
% 7.16/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.16/1.49      | r1_tarski(k2_relat_1(X0),X2)
% 7.16/1.49      | ~ v1_relat_1(X0) ),
% 7.16/1.49      inference(resolution,[status(thm)],[c_25,c_8]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_24,plain,
% 7.16/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.16/1.49      | v1_relat_1(X0) ),
% 7.16/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_409,plain,
% 7.16/1.49      ( r1_tarski(k2_relat_1(X0),X2)
% 7.16/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_405,c_24]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_410,plain,
% 7.16/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.16/1.49      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.16/1.49      inference(renaming,[status(thm)],[c_409]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1807,plain,
% 7.16/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.16/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2129,plain,
% 7.16/1.49      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1808,c_1807]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_17,plain,
% 7.16/1.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5,plain,
% 7.16/1.49      ( v4_relat_1(X0,X1)
% 7.16/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.16/1.49      | ~ v1_relat_1(X0) ),
% 7.16/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1827,plain,
% 7.16/1.49      ( v4_relat_1(X0,X1) = iProver_top
% 7.16/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.16/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6026,plain,
% 7.16/1.49      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 7.16/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.16/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_17,c_1827]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_21,plain,
% 7.16/1.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.16/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_61,plain,
% 7.16/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7690,plain,
% 7.16/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.16/1.49      | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_6026,c_61]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7691,plain,
% 7.16/1.49      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 7.16/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.16/1.49      inference(renaming,[status(thm)],[c_7690]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_14,plain,
% 7.16/1.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1820,plain,
% 7.16/1.49      ( k7_relat_1(X0,X1) = X0
% 7.16/1.49      | v4_relat_1(X0,X1) != iProver_top
% 7.16/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7696,plain,
% 7.16/1.49      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 7.16/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.16/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_7691,c_1820]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1825,plain,
% 7.16/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_18,plain,
% 7.16/1.49      ( ~ v1_relat_1(X0)
% 7.16/1.49      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.16/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1818,plain,
% 7.16/1.49      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.16/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_3202,plain,
% 7.16/1.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1825,c_1818]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_23,plain,
% 7.16/1.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
% 7.16/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_3210,plain,
% 7.16/1.49      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k3_xboole_0(X0,X1)) ),
% 7.16/1.49      inference(light_normalisation,[status(thm)],[c_3202,c_23]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7701,plain,
% 7.16/1.49      ( k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0)
% 7.16/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.16/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_7696,c_3210]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_21389,plain,
% 7.16/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.16/1.49      | k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0) ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_7701,c_61]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_21390,plain,
% 7.16/1.49      ( k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0)
% 7.16/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.16/1.49      inference(renaming,[status(thm)],[c_21389]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_21402,plain,
% 7.16/1.49      ( k6_relat_1(k3_xboole_0(k2_relat_1(sK2),sK1)) = k6_relat_1(k2_relat_1(sK2)) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_2129,c_21390]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_16,plain,
% 7.16/1.49      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_21782,plain,
% 7.16/1.49      ( k3_xboole_0(k2_relat_1(sK2),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_21402,c_16]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_21807,plain,
% 7.16/1.49      ( k3_xboole_0(k2_relat_1(sK2),sK1) = k2_relat_1(sK2) ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_21782,c_16]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1815,plain,
% 7.16/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.16/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2404,plain,
% 7.16/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1808,c_1815]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_13,plain,
% 7.16/1.49      ( ~ v1_relat_1(X0)
% 7.16/1.49      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 7.16/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1821,plain,
% 7.16/1.49      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 7.16/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4278,plain,
% 7.16/1.49      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_2404,c_1821]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_23098,plain,
% 7.16/1.49      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_21807,c_4278]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_12,plain,
% 7.16/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.16/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1822,plain,
% 7.16/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.16/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_10,plain,
% 7.16/1.49      ( ~ v1_relat_1(X0)
% 7.16/1.49      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.16/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1824,plain,
% 7.16/1.49      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 7.16/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2566,plain,
% 7.16/1.49      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_2404,c_1824]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_22,plain,
% 7.16/1.49      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 7.16/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.16/1.49      | ~ v1_relat_1(X1) ),
% 7.16/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1816,plain,
% 7.16/1.49      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 7.16/1.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.16/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7715,plain,
% 7.16/1.49      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
% 7.16/1.49      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 7.16/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_2566,c_1816]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_34,plain,
% 7.16/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2011,plain,
% 7.16/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.16/1.49      | v1_relat_1(sK2) ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_24]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2012,plain,
% 7.16/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.16/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_2011]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1,plain,
% 7.16/1.49      ( r1_tarski(X0,X0) ),
% 7.16/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2066,plain,
% 7.16/1.49      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2363,plain,
% 7.16/1.49      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_2066]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2366,plain,
% 7.16/1.49      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_2363]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_9798,plain,
% 7.16/1.49      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_7715,c_34,c_2012,c_2366]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_0,plain,
% 7.16/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.16/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1831,plain,
% 7.16/1.49      ( X0 = X1
% 7.16/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.16/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_9803,plain,
% 7.16/1.49      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
% 7.16/1.49      | r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2)) != iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_9798,c_1831]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_12335,plain,
% 7.16/1.49      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
% 7.16/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1822,c_9803]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_12657,plain,
% 7.16/1.49      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_12335,c_34,c_2012]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_23100,plain,
% 7.16/1.49      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 7.16/1.49      inference(light_normalisation,[status(thm)],[c_23098,c_12657]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_29,plain,
% 7.16/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.16/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.16/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1811,plain,
% 7.16/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.16/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5770,plain,
% 7.16/1.49      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1808,c_1811]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_27,plain,
% 7.16/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.16/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.16/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1813,plain,
% 7.16/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.16/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4817,plain,
% 7.16/1.49      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1808,c_1813]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_28,plain,
% 7.16/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.16/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.16/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1812,plain,
% 7.16/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.16/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4350,plain,
% 7.16/1.49      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1808,c_1812]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_32,negated_conjecture,
% 7.16/1.49      ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
% 7.16/1.49      | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
% 7.16/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4434,plain,
% 7.16/1.49      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
% 7.16/1.49      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_4350,c_32]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5131,plain,
% 7.16/1.49      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
% 7.16/1.49      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_4817,c_4434]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_30,plain,
% 7.16/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.16/1.49      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 7.16/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1810,plain,
% 7.16/1.49      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 7.16/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4956,plain,
% 7.16/1.49      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1808,c_1810]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5285,plain,
% 7.16/1.49      ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
% 7.16/1.49      | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_5131,c_4956]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6357,plain,
% 7.16/1.49      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
% 7.16/1.49      | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_5770,c_5285]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_26,plain,
% 7.16/1.49      ( v4_relat_1(X0,X1)
% 7.16/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.16/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1814,plain,
% 7.16/1.49      ( v4_relat_1(X0,X1) = iProver_top
% 7.16/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_3844,plain,
% 7.16/1.49      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1808,c_1814]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4937,plain,
% 7.16/1.49      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_3844,c_1820]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2019,plain,
% 7.16/1.49      ( v4_relat_1(sK2,sK0)
% 7.16/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_26]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2147,plain,
% 7.16/1.49      ( ~ v4_relat_1(sK2,X0)
% 7.16/1.49      | ~ v1_relat_1(sK2)
% 7.16/1.49      | k7_relat_1(sK2,X0) = sK2 ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2167,plain,
% 7.16/1.49      ( ~ v4_relat_1(sK2,sK0)
% 7.16/1.49      | ~ v1_relat_1(sK2)
% 7.16/1.49      | k7_relat_1(sK2,sK0) = sK2 ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_2147]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5289,plain,
% 7.16/1.49      ( k7_relat_1(sK2,sK0) = sK2 ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_4937,c_33,c_2011,c_2019,c_2167]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_11,plain,
% 7.16/1.49      ( ~ v1_relat_1(X0)
% 7.16/1.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.16/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1823,plain,
% 7.16/1.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.16/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_3328,plain,
% 7.16/1.49      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_2404,c_1823]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5292,plain,
% 7.16/1.49      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_5289,c_3328]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(contradiction,plain,
% 7.16/1.49      ( $false ),
% 7.16/1.49      inference(minisat,[status(thm)],[c_23100,c_6357,c_5292]) ).
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  ------                               Statistics
% 7.16/1.49  
% 7.16/1.49  ------ General
% 7.16/1.49  
% 7.16/1.49  abstr_ref_over_cycles:                  0
% 7.16/1.49  abstr_ref_under_cycles:                 0
% 7.16/1.49  gc_basic_clause_elim:                   0
% 7.16/1.49  forced_gc_time:                         0
% 7.16/1.49  parsing_time:                           0.01
% 7.16/1.49  unif_index_cands_time:                  0.
% 7.16/1.49  unif_index_add_time:                    0.
% 7.16/1.49  orderings_time:                         0.
% 7.16/1.49  out_proof_time:                         0.013
% 7.16/1.49  total_time:                             0.564
% 7.16/1.49  num_of_symbols:                         53
% 7.16/1.49  num_of_terms:                           19894
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing
% 7.16/1.49  
% 7.16/1.49  num_of_splits:                          0
% 7.16/1.49  num_of_split_atoms:                     0
% 7.16/1.49  num_of_reused_defs:                     0
% 7.16/1.49  num_eq_ax_congr_red:                    19
% 7.16/1.49  num_of_sem_filtered_clauses:            1
% 7.16/1.49  num_of_subtypes:                        0
% 7.16/1.49  monotx_restored_types:                  0
% 7.16/1.49  sat_num_of_epr_types:                   0
% 7.16/1.49  sat_num_of_non_cyclic_types:            0
% 7.16/1.49  sat_guarded_non_collapsed_types:        0
% 7.16/1.49  num_pure_diseq_elim:                    0
% 7.16/1.49  simp_replaced_by:                       0
% 7.16/1.49  res_preprocessed:                       161
% 7.16/1.49  prep_upred:                             0
% 7.16/1.49  prep_unflattend:                        24
% 7.16/1.49  smt_new_axioms:                         0
% 7.16/1.49  pred_elim_cands:                        4
% 7.16/1.49  pred_elim:                              1
% 7.16/1.49  pred_elim_cl:                           2
% 7.16/1.49  pred_elim_cycles:                       3
% 7.16/1.49  merged_defs:                            8
% 7.16/1.49  merged_defs_ncl:                        0
% 7.16/1.49  bin_hyper_res:                          8
% 7.16/1.49  prep_cycles:                            4
% 7.16/1.49  pred_elim_time:                         0.008
% 7.16/1.49  splitting_time:                         0.
% 7.16/1.49  sem_filter_time:                        0.
% 7.16/1.49  monotx_time:                            0.001
% 7.16/1.49  subtype_inf_time:                       0.
% 7.16/1.49  
% 7.16/1.49  ------ Problem properties
% 7.16/1.49  
% 7.16/1.49  clauses:                                30
% 7.16/1.49  conjectures:                            2
% 7.16/1.49  epr:                                    3
% 7.16/1.49  horn:                                   30
% 7.16/1.49  ground:                                 2
% 7.16/1.49  unary:                                  8
% 7.16/1.49  binary:                                 15
% 7.16/1.49  lits:                                   60
% 7.16/1.49  lits_eq:                                15
% 7.16/1.49  fd_pure:                                0
% 7.16/1.49  fd_pseudo:                              0
% 7.16/1.49  fd_cond:                                0
% 7.16/1.49  fd_pseudo_cond:                         1
% 7.16/1.49  ac_symbols:                             0
% 7.16/1.49  
% 7.16/1.49  ------ Propositional Solver
% 7.16/1.49  
% 7.16/1.49  prop_solver_calls:                      28
% 7.16/1.49  prop_fast_solver_calls:                 1307
% 7.16/1.49  smt_solver_calls:                       0
% 7.16/1.49  smt_fast_solver_calls:                  0
% 7.16/1.49  prop_num_of_clauses:                    9937
% 7.16/1.49  prop_preprocess_simplified:             20717
% 7.16/1.49  prop_fo_subsumed:                       37
% 7.16/1.49  prop_solver_time:                       0.
% 7.16/1.49  smt_solver_time:                        0.
% 7.16/1.49  smt_fast_solver_time:                   0.
% 7.16/1.49  prop_fast_solver_time:                  0.
% 7.16/1.49  prop_unsat_core_time:                   0.001
% 7.16/1.49  
% 7.16/1.49  ------ QBF
% 7.16/1.49  
% 7.16/1.49  qbf_q_res:                              0
% 7.16/1.49  qbf_num_tautologies:                    0
% 7.16/1.49  qbf_prep_cycles:                        0
% 7.16/1.49  
% 7.16/1.49  ------ BMC1
% 7.16/1.49  
% 7.16/1.49  bmc1_current_bound:                     -1
% 7.16/1.49  bmc1_last_solved_bound:                 -1
% 7.16/1.49  bmc1_unsat_core_size:                   -1
% 7.16/1.49  bmc1_unsat_core_parents_size:           -1
% 7.16/1.49  bmc1_merge_next_fun:                    0
% 7.16/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.16/1.49  
% 7.16/1.49  ------ Instantiation
% 7.16/1.49  
% 7.16/1.49  inst_num_of_clauses:                    3001
% 7.16/1.49  inst_num_in_passive:                    715
% 7.16/1.49  inst_num_in_active:                     1065
% 7.16/1.49  inst_num_in_unprocessed:                1222
% 7.16/1.49  inst_num_of_loops:                      1080
% 7.16/1.49  inst_num_of_learning_restarts:          0
% 7.16/1.49  inst_num_moves_active_passive:          14
% 7.16/1.49  inst_lit_activity:                      0
% 7.16/1.49  inst_lit_activity_moves:                0
% 7.16/1.49  inst_num_tautologies:                   0
% 7.16/1.49  inst_num_prop_implied:                  0
% 7.16/1.49  inst_num_existing_simplified:           0
% 7.16/1.49  inst_num_eq_res_simplified:             0
% 7.16/1.49  inst_num_child_elim:                    0
% 7.16/1.49  inst_num_of_dismatching_blockings:      1302
% 7.16/1.49  inst_num_of_non_proper_insts:           2966
% 7.16/1.49  inst_num_of_duplicates:                 0
% 7.16/1.49  inst_inst_num_from_inst_to_res:         0
% 7.16/1.49  inst_dismatching_checking_time:         0.
% 7.16/1.49  
% 7.16/1.49  ------ Resolution
% 7.16/1.49  
% 7.16/1.49  res_num_of_clauses:                     0
% 7.16/1.49  res_num_in_passive:                     0
% 7.16/1.49  res_num_in_active:                      0
% 7.16/1.49  res_num_of_loops:                       165
% 7.16/1.49  res_forward_subset_subsumed:            218
% 7.16/1.49  res_backward_subset_subsumed:           6
% 7.16/1.49  res_forward_subsumed:                   0
% 7.16/1.49  res_backward_subsumed:                  0
% 7.16/1.49  res_forward_subsumption_resolution:     0
% 7.16/1.49  res_backward_subsumption_resolution:    0
% 7.16/1.49  res_clause_to_clause_subsumption:       1416
% 7.16/1.49  res_orphan_elimination:                 0
% 7.16/1.49  res_tautology_del:                      218
% 7.16/1.49  res_num_eq_res_simplified:              0
% 7.16/1.49  res_num_sel_changes:                    0
% 7.16/1.49  res_moves_from_active_to_pass:          0
% 7.16/1.49  
% 7.16/1.49  ------ Superposition
% 7.16/1.49  
% 7.16/1.49  sup_time_total:                         0.
% 7.16/1.49  sup_time_generating:                    0.
% 7.16/1.49  sup_time_sim_full:                      0.
% 7.16/1.49  sup_time_sim_immed:                     0.
% 7.16/1.49  
% 7.16/1.49  sup_num_of_clauses:                     356
% 7.16/1.49  sup_num_in_active:                      193
% 7.16/1.49  sup_num_in_passive:                     163
% 7.16/1.49  sup_num_of_loops:                       215
% 7.16/1.49  sup_fw_superposition:                   337
% 7.16/1.49  sup_bw_superposition:                   205
% 7.16/1.49  sup_immediate_simplified:               146
% 7.16/1.49  sup_given_eliminated:                   2
% 7.16/1.49  comparisons_done:                       0
% 7.16/1.49  comparisons_avoided:                    0
% 7.16/1.49  
% 7.16/1.49  ------ Simplifications
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  sim_fw_subset_subsumed:                 23
% 7.16/1.49  sim_bw_subset_subsumed:                 2
% 7.16/1.49  sim_fw_subsumed:                        63
% 7.16/1.49  sim_bw_subsumed:                        1
% 7.16/1.49  sim_fw_subsumption_res:                 1
% 7.16/1.49  sim_bw_subsumption_res:                 0
% 7.16/1.49  sim_tautology_del:                      9
% 7.16/1.49  sim_eq_tautology_del:                   19
% 7.16/1.49  sim_eq_res_simp:                        0
% 7.16/1.49  sim_fw_demodulated:                     67
% 7.16/1.49  sim_bw_demodulated:                     32
% 7.16/1.49  sim_light_normalised:                   47
% 7.16/1.49  sim_joinable_taut:                      0
% 7.16/1.49  sim_joinable_simp:                      0
% 7.16/1.49  sim_ac_normalised:                      0
% 7.16/1.49  sim_smt_subsumption:                    0
% 7.16/1.49  
%------------------------------------------------------------------------------
