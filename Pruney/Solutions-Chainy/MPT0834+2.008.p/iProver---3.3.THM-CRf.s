%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:00 EST 2020

% Result     : Theorem 31.77s
% Output     : CNFRefutation 31.77s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 493 expanded)
%              Number of clauses        :  119 ( 211 expanded)
%              Number of leaves         :   24 (  91 expanded)
%              Depth                    :   27
%              Number of atoms          :  435 (1163 expanded)
%              Number of equality atoms :  217 ( 561 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f52])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f78,plain,(
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

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f45])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1623,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_7])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_389,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_22])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_389])).

cnf(c_1622,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_2196,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1622])).

cnf(c_14,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2199,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1641])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1643,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6181,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2199,c_1643])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1624,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2959,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X3,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1642,c_1624])).

cnf(c_6419,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6181,c_2959])).

cnf(c_24,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1629,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10390,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6419,c_1629])).

cnf(c_46697,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_10390])).

cnf(c_19,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_59,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1633,plain,
    ( v4_relat_1(k6_relat_1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1636,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6893,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1636])).

cnf(c_47182,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46697,c_59,c_6893])).

cnf(c_47183,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_47182])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1637,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_47187,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_47183,c_1637])).

cnf(c_1632,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1634,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2440,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_1632,c_1634])).

cnf(c_21,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2441,plain,
    ( k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2440,c_21])).

cnf(c_47188,plain,
    ( k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_47187,c_2441])).

cnf(c_135595,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47188,c_59])).

cnf(c_135596,plain,
    ( k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_135595])).

cnf(c_135604,plain,
    ( k6_relat_1(k3_xboole_0(k2_relat_1(sK2),sK1)) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2196,c_135596])).

cnf(c_13,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_137215,plain,
    ( k3_xboole_0(k2_relat_1(sK2),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_135604,c_13])).

cnf(c_137232,plain,
    ( k3_xboole_0(k2_relat_1(sK2),sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_137215,c_13])).

cnf(c_1630,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2319,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1630])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1638,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4193,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2319,c_1638])).

cnf(c_140055,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_137232,c_4193])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1639,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1644,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2960,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1624])).

cnf(c_3679,plain,
    ( v4_relat_1(sK2,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2960,c_1629])).

cnf(c_4560,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1644,c_3679])).

cnf(c_5087,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4560,c_1637])).

cnf(c_7025,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5087,c_2319])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1640,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3134,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2319,c_1640])).

cnf(c_7028,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_7025,c_3134])).

cnf(c_20,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1631,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7184,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7028,c_1631])).

cnf(c_32183,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7184,c_2319])).

cnf(c_32184,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_32183])).

cnf(c_32202,plain,
    ( v4_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32184,c_3679])).

cnf(c_32511,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = sK2
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32202,c_1637])).

cnf(c_76551,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | k7_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32511,c_2319])).

cnf(c_76552,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = sK2
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_76551])).

cnf(c_76555,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_1644,c_76552])).

cnf(c_15,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1635,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_77021,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_76555,c_1635])).

cnf(c_78332,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_77021,c_2319])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1645,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_78338,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_78332,c_1645])).

cnf(c_84153,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_78338])).

cnf(c_84156,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_84153,c_2319])).

cnf(c_140062,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_140055,c_84156])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1626,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5693,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1623,c_1626])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1628,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4964,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1623,c_1628])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1627,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4285,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1623,c_1627])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4291,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4285,c_30])).

cnf(c_5225,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4964,c_4291])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1625,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5096,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1623,c_1625])).

cnf(c_5226,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5225,c_5096])).

cnf(c_6331,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5693,c_5226])).

cnf(c_3678,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1629])).

cnf(c_5086,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3678,c_1637])).

cnf(c_2323,plain,
    ( v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2319])).

cnf(c_3683,plain,
    ( v4_relat_1(sK2,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3678])).

cnf(c_4903,plain,
    ( ~ v4_relat_1(sK2,X0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4905,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK0) = sK2 ),
    inference(instantiation,[status(thm)],[c_4903])).

cnf(c_5301,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5086,c_2323,c_3683,c_4905])).

cnf(c_5304,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5301,c_3134])).

cnf(c_6332,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6331,c_5304])).

cnf(c_6333,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_6332])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_140062,c_6333])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:38:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.77/4.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.77/4.48  
% 31.77/4.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.77/4.48  
% 31.77/4.48  ------  iProver source info
% 31.77/4.48  
% 31.77/4.48  git: date: 2020-06-30 10:37:57 +0100
% 31.77/4.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.77/4.48  git: non_committed_changes: false
% 31.77/4.48  git: last_make_outside_of_git: false
% 31.77/4.48  
% 31.77/4.48  ------ 
% 31.77/4.48  
% 31.77/4.48  ------ Input Options
% 31.77/4.48  
% 31.77/4.48  --out_options                           all
% 31.77/4.48  --tptp_safe_out                         true
% 31.77/4.48  --problem_path                          ""
% 31.77/4.48  --include_path                          ""
% 31.77/4.48  --clausifier                            res/vclausify_rel
% 31.77/4.48  --clausifier_options                    ""
% 31.77/4.48  --stdin                                 false
% 31.77/4.48  --stats_out                             all
% 31.77/4.48  
% 31.77/4.48  ------ General Options
% 31.77/4.48  
% 31.77/4.48  --fof                                   false
% 31.77/4.48  --time_out_real                         305.
% 31.77/4.48  --time_out_virtual                      -1.
% 31.77/4.48  --symbol_type_check                     false
% 31.77/4.48  --clausify_out                          false
% 31.77/4.48  --sig_cnt_out                           false
% 31.77/4.48  --trig_cnt_out                          false
% 31.77/4.48  --trig_cnt_out_tolerance                1.
% 31.77/4.48  --trig_cnt_out_sk_spl                   false
% 31.77/4.48  --abstr_cl_out                          false
% 31.77/4.48  
% 31.77/4.48  ------ Global Options
% 31.77/4.48  
% 31.77/4.48  --schedule                              default
% 31.77/4.48  --add_important_lit                     false
% 31.77/4.48  --prop_solver_per_cl                    1000
% 31.77/4.48  --min_unsat_core                        false
% 31.77/4.48  --soft_assumptions                      false
% 31.77/4.48  --soft_lemma_size                       3
% 31.77/4.48  --prop_impl_unit_size                   0
% 31.77/4.48  --prop_impl_unit                        []
% 31.77/4.48  --share_sel_clauses                     true
% 31.77/4.48  --reset_solvers                         false
% 31.77/4.48  --bc_imp_inh                            [conj_cone]
% 31.77/4.48  --conj_cone_tolerance                   3.
% 31.77/4.48  --extra_neg_conj                        none
% 31.77/4.48  --large_theory_mode                     true
% 31.77/4.48  --prolific_symb_bound                   200
% 31.77/4.48  --lt_threshold                          2000
% 31.77/4.48  --clause_weak_htbl                      true
% 31.77/4.48  --gc_record_bc_elim                     false
% 31.77/4.48  
% 31.77/4.48  ------ Preprocessing Options
% 31.77/4.48  
% 31.77/4.48  --preprocessing_flag                    true
% 31.77/4.48  --time_out_prep_mult                    0.1
% 31.77/4.48  --splitting_mode                        input
% 31.77/4.48  --splitting_grd                         true
% 31.77/4.48  --splitting_cvd                         false
% 31.77/4.48  --splitting_cvd_svl                     false
% 31.77/4.48  --splitting_nvd                         32
% 31.77/4.48  --sub_typing                            true
% 31.77/4.48  --prep_gs_sim                           true
% 31.77/4.48  --prep_unflatten                        true
% 31.77/4.48  --prep_res_sim                          true
% 31.77/4.48  --prep_upred                            true
% 31.77/4.48  --prep_sem_filter                       exhaustive
% 31.77/4.48  --prep_sem_filter_out                   false
% 31.77/4.48  --pred_elim                             true
% 31.77/4.48  --res_sim_input                         true
% 31.77/4.48  --eq_ax_congr_red                       true
% 31.77/4.48  --pure_diseq_elim                       true
% 31.77/4.48  --brand_transform                       false
% 31.77/4.48  --non_eq_to_eq                          false
% 31.77/4.48  --prep_def_merge                        true
% 31.77/4.48  --prep_def_merge_prop_impl              false
% 31.77/4.48  --prep_def_merge_mbd                    true
% 31.77/4.48  --prep_def_merge_tr_red                 false
% 31.77/4.48  --prep_def_merge_tr_cl                  false
% 31.77/4.48  --smt_preprocessing                     true
% 31.77/4.48  --smt_ac_axioms                         fast
% 31.77/4.48  --preprocessed_out                      false
% 31.77/4.48  --preprocessed_stats                    false
% 31.77/4.48  
% 31.77/4.48  ------ Abstraction refinement Options
% 31.77/4.48  
% 31.77/4.48  --abstr_ref                             []
% 31.77/4.48  --abstr_ref_prep                        false
% 31.77/4.48  --abstr_ref_until_sat                   false
% 31.77/4.48  --abstr_ref_sig_restrict                funpre
% 31.77/4.48  --abstr_ref_af_restrict_to_split_sk     false
% 31.77/4.48  --abstr_ref_under                       []
% 31.77/4.48  
% 31.77/4.48  ------ SAT Options
% 31.77/4.48  
% 31.77/4.48  --sat_mode                              false
% 31.77/4.48  --sat_fm_restart_options                ""
% 31.77/4.48  --sat_gr_def                            false
% 31.77/4.48  --sat_epr_types                         true
% 31.77/4.48  --sat_non_cyclic_types                  false
% 31.77/4.48  --sat_finite_models                     false
% 31.77/4.48  --sat_fm_lemmas                         false
% 31.77/4.48  --sat_fm_prep                           false
% 31.77/4.48  --sat_fm_uc_incr                        true
% 31.77/4.48  --sat_out_model                         small
% 31.77/4.48  --sat_out_clauses                       false
% 31.77/4.48  
% 31.77/4.48  ------ QBF Options
% 31.77/4.48  
% 31.77/4.48  --qbf_mode                              false
% 31.77/4.48  --qbf_elim_univ                         false
% 31.77/4.48  --qbf_dom_inst                          none
% 31.77/4.48  --qbf_dom_pre_inst                      false
% 31.77/4.48  --qbf_sk_in                             false
% 31.77/4.48  --qbf_pred_elim                         true
% 31.77/4.48  --qbf_split                             512
% 31.77/4.48  
% 31.77/4.48  ------ BMC1 Options
% 31.77/4.48  
% 31.77/4.48  --bmc1_incremental                      false
% 31.77/4.48  --bmc1_axioms                           reachable_all
% 31.77/4.48  --bmc1_min_bound                        0
% 31.77/4.48  --bmc1_max_bound                        -1
% 31.77/4.48  --bmc1_max_bound_default                -1
% 31.77/4.48  --bmc1_symbol_reachability              true
% 31.77/4.48  --bmc1_property_lemmas                  false
% 31.77/4.48  --bmc1_k_induction                      false
% 31.77/4.48  --bmc1_non_equiv_states                 false
% 31.77/4.48  --bmc1_deadlock                         false
% 31.77/4.48  --bmc1_ucm                              false
% 31.77/4.48  --bmc1_add_unsat_core                   none
% 31.77/4.48  --bmc1_unsat_core_children              false
% 31.77/4.48  --bmc1_unsat_core_extrapolate_axioms    false
% 31.77/4.48  --bmc1_out_stat                         full
% 31.77/4.48  --bmc1_ground_init                      false
% 31.77/4.48  --bmc1_pre_inst_next_state              false
% 31.77/4.48  --bmc1_pre_inst_state                   false
% 31.77/4.48  --bmc1_pre_inst_reach_state             false
% 31.77/4.48  --bmc1_out_unsat_core                   false
% 31.77/4.48  --bmc1_aig_witness_out                  false
% 31.77/4.48  --bmc1_verbose                          false
% 31.77/4.48  --bmc1_dump_clauses_tptp                false
% 31.77/4.48  --bmc1_dump_unsat_core_tptp             false
% 31.77/4.48  --bmc1_dump_file                        -
% 31.77/4.48  --bmc1_ucm_expand_uc_limit              128
% 31.77/4.48  --bmc1_ucm_n_expand_iterations          6
% 31.77/4.48  --bmc1_ucm_extend_mode                  1
% 31.77/4.48  --bmc1_ucm_init_mode                    2
% 31.77/4.48  --bmc1_ucm_cone_mode                    none
% 31.77/4.48  --bmc1_ucm_reduced_relation_type        0
% 31.77/4.48  --bmc1_ucm_relax_model                  4
% 31.77/4.48  --bmc1_ucm_full_tr_after_sat            true
% 31.77/4.48  --bmc1_ucm_expand_neg_assumptions       false
% 31.77/4.48  --bmc1_ucm_layered_model                none
% 31.77/4.48  --bmc1_ucm_max_lemma_size               10
% 31.77/4.48  
% 31.77/4.48  ------ AIG Options
% 31.77/4.48  
% 31.77/4.48  --aig_mode                              false
% 31.77/4.48  
% 31.77/4.48  ------ Instantiation Options
% 31.77/4.48  
% 31.77/4.48  --instantiation_flag                    true
% 31.77/4.48  --inst_sos_flag                         true
% 31.77/4.48  --inst_sos_phase                        true
% 31.77/4.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.77/4.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.77/4.48  --inst_lit_sel_side                     num_symb
% 31.77/4.48  --inst_solver_per_active                1400
% 31.77/4.48  --inst_solver_calls_frac                1.
% 31.77/4.48  --inst_passive_queue_type               priority_queues
% 31.77/4.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.77/4.48  --inst_passive_queues_freq              [25;2]
% 31.77/4.48  --inst_dismatching                      true
% 31.77/4.48  --inst_eager_unprocessed_to_passive     true
% 31.77/4.48  --inst_prop_sim_given                   true
% 31.77/4.48  --inst_prop_sim_new                     false
% 31.77/4.48  --inst_subs_new                         false
% 31.77/4.48  --inst_eq_res_simp                      false
% 31.77/4.48  --inst_subs_given                       false
% 31.77/4.48  --inst_orphan_elimination               true
% 31.77/4.48  --inst_learning_loop_flag               true
% 31.77/4.48  --inst_learning_start                   3000
% 31.77/4.48  --inst_learning_factor                  2
% 31.77/4.48  --inst_start_prop_sim_after_learn       3
% 31.77/4.48  --inst_sel_renew                        solver
% 31.77/4.48  --inst_lit_activity_flag                true
% 31.77/4.48  --inst_restr_to_given                   false
% 31.77/4.48  --inst_activity_threshold               500
% 31.77/4.48  --inst_out_proof                        true
% 31.77/4.48  
% 31.77/4.48  ------ Resolution Options
% 31.77/4.48  
% 31.77/4.48  --resolution_flag                       true
% 31.77/4.48  --res_lit_sel                           adaptive
% 31.77/4.48  --res_lit_sel_side                      none
% 31.77/4.48  --res_ordering                          kbo
% 31.77/4.48  --res_to_prop_solver                    active
% 31.77/4.48  --res_prop_simpl_new                    false
% 31.77/4.48  --res_prop_simpl_given                  true
% 31.77/4.48  --res_passive_queue_type                priority_queues
% 31.77/4.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.77/4.48  --res_passive_queues_freq               [15;5]
% 31.77/4.48  --res_forward_subs                      full
% 31.77/4.48  --res_backward_subs                     full
% 31.77/4.48  --res_forward_subs_resolution           true
% 31.77/4.48  --res_backward_subs_resolution          true
% 31.77/4.48  --res_orphan_elimination                true
% 31.77/4.48  --res_time_limit                        2.
% 31.77/4.48  --res_out_proof                         true
% 31.77/4.48  
% 31.77/4.48  ------ Superposition Options
% 31.77/4.48  
% 31.77/4.48  --superposition_flag                    true
% 31.77/4.48  --sup_passive_queue_type                priority_queues
% 31.77/4.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.77/4.48  --sup_passive_queues_freq               [8;1;4]
% 31.77/4.48  --demod_completeness_check              fast
% 31.77/4.48  --demod_use_ground                      true
% 31.77/4.48  --sup_to_prop_solver                    passive
% 31.77/4.48  --sup_prop_simpl_new                    true
% 31.77/4.48  --sup_prop_simpl_given                  true
% 31.77/4.48  --sup_fun_splitting                     true
% 31.77/4.48  --sup_smt_interval                      50000
% 31.77/4.48  
% 31.77/4.48  ------ Superposition Simplification Setup
% 31.77/4.48  
% 31.77/4.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.77/4.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.77/4.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.77/4.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.77/4.48  --sup_full_triv                         [TrivRules;PropSubs]
% 31.77/4.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.77/4.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.77/4.48  --sup_immed_triv                        [TrivRules]
% 31.77/4.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.48  --sup_immed_bw_main                     []
% 31.77/4.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.77/4.48  --sup_input_triv                        [Unflattening;TrivRules]
% 31.77/4.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.48  --sup_input_bw                          []
% 31.77/4.48  
% 31.77/4.48  ------ Combination Options
% 31.77/4.48  
% 31.77/4.48  --comb_res_mult                         3
% 31.77/4.48  --comb_sup_mult                         2
% 31.77/4.48  --comb_inst_mult                        10
% 31.77/4.48  
% 31.77/4.48  ------ Debug Options
% 31.77/4.48  
% 31.77/4.48  --dbg_backtrace                         false
% 31.77/4.48  --dbg_dump_prop_clauses                 false
% 31.77/4.48  --dbg_dump_prop_clauses_file            -
% 31.77/4.48  --dbg_out_stat                          false
% 31.77/4.48  ------ Parsing...
% 31.77/4.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.77/4.48  
% 31.77/4.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.77/4.48  
% 31.77/4.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.77/4.48  
% 31.77/4.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.77/4.48  ------ Proving...
% 31.77/4.48  ------ Problem Properties 
% 31.77/4.48  
% 31.77/4.48  
% 31.77/4.48  clauses                                 29
% 31.77/4.48  conjectures                             2
% 31.77/4.48  EPR                                     4
% 31.77/4.48  Horn                                    29
% 31.77/4.48  unary                                   8
% 31.77/4.48  binary                                  15
% 31.77/4.48  lits                                    57
% 31.77/4.48  lits eq                                 14
% 31.77/4.48  fd_pure                                 0
% 31.77/4.48  fd_pseudo                               0
% 31.77/4.48  fd_cond                                 0
% 31.77/4.48  fd_pseudo_cond                          1
% 31.77/4.48  AC symbols                              0
% 31.77/4.48  
% 31.77/4.48  ------ Schedule dynamic 5 is on 
% 31.77/4.48  
% 31.77/4.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.77/4.48  
% 31.77/4.48  
% 31.77/4.48  ------ 
% 31.77/4.48  Current options:
% 31.77/4.48  ------ 
% 31.77/4.48  
% 31.77/4.48  ------ Input Options
% 31.77/4.48  
% 31.77/4.48  --out_options                           all
% 31.77/4.48  --tptp_safe_out                         true
% 31.77/4.48  --problem_path                          ""
% 31.77/4.48  --include_path                          ""
% 31.77/4.48  --clausifier                            res/vclausify_rel
% 31.77/4.48  --clausifier_options                    ""
% 31.77/4.48  --stdin                                 false
% 31.77/4.48  --stats_out                             all
% 31.77/4.48  
% 31.77/4.48  ------ General Options
% 31.77/4.48  
% 31.77/4.48  --fof                                   false
% 31.77/4.48  --time_out_real                         305.
% 31.77/4.48  --time_out_virtual                      -1.
% 31.77/4.48  --symbol_type_check                     false
% 31.77/4.48  --clausify_out                          false
% 31.77/4.48  --sig_cnt_out                           false
% 31.77/4.48  --trig_cnt_out                          false
% 31.77/4.48  --trig_cnt_out_tolerance                1.
% 31.77/4.48  --trig_cnt_out_sk_spl                   false
% 31.77/4.48  --abstr_cl_out                          false
% 31.77/4.48  
% 31.77/4.48  ------ Global Options
% 31.77/4.48  
% 31.77/4.48  --schedule                              default
% 31.77/4.48  --add_important_lit                     false
% 31.77/4.48  --prop_solver_per_cl                    1000
% 31.77/4.48  --min_unsat_core                        false
% 31.77/4.48  --soft_assumptions                      false
% 31.77/4.48  --soft_lemma_size                       3
% 31.77/4.48  --prop_impl_unit_size                   0
% 31.77/4.48  --prop_impl_unit                        []
% 31.77/4.48  --share_sel_clauses                     true
% 31.77/4.48  --reset_solvers                         false
% 31.77/4.48  --bc_imp_inh                            [conj_cone]
% 31.77/4.48  --conj_cone_tolerance                   3.
% 31.77/4.48  --extra_neg_conj                        none
% 31.77/4.48  --large_theory_mode                     true
% 31.77/4.48  --prolific_symb_bound                   200
% 31.77/4.48  --lt_threshold                          2000
% 31.77/4.48  --clause_weak_htbl                      true
% 31.77/4.48  --gc_record_bc_elim                     false
% 31.77/4.48  
% 31.77/4.48  ------ Preprocessing Options
% 31.77/4.48  
% 31.77/4.48  --preprocessing_flag                    true
% 31.77/4.48  --time_out_prep_mult                    0.1
% 31.77/4.48  --splitting_mode                        input
% 31.77/4.48  --splitting_grd                         true
% 31.77/4.48  --splitting_cvd                         false
% 31.77/4.48  --splitting_cvd_svl                     false
% 31.77/4.48  --splitting_nvd                         32
% 31.77/4.48  --sub_typing                            true
% 31.77/4.48  --prep_gs_sim                           true
% 31.77/4.48  --prep_unflatten                        true
% 31.77/4.48  --prep_res_sim                          true
% 31.77/4.48  --prep_upred                            true
% 31.77/4.48  --prep_sem_filter                       exhaustive
% 31.77/4.48  --prep_sem_filter_out                   false
% 31.77/4.48  --pred_elim                             true
% 31.77/4.48  --res_sim_input                         true
% 31.77/4.48  --eq_ax_congr_red                       true
% 31.77/4.48  --pure_diseq_elim                       true
% 31.77/4.48  --brand_transform                       false
% 31.77/4.48  --non_eq_to_eq                          false
% 31.77/4.48  --prep_def_merge                        true
% 31.77/4.48  --prep_def_merge_prop_impl              false
% 31.77/4.48  --prep_def_merge_mbd                    true
% 31.77/4.48  --prep_def_merge_tr_red                 false
% 31.77/4.48  --prep_def_merge_tr_cl                  false
% 31.77/4.48  --smt_preprocessing                     true
% 31.77/4.48  --smt_ac_axioms                         fast
% 31.77/4.48  --preprocessed_out                      false
% 31.77/4.48  --preprocessed_stats                    false
% 31.77/4.48  
% 31.77/4.48  ------ Abstraction refinement Options
% 31.77/4.48  
% 31.77/4.48  --abstr_ref                             []
% 31.77/4.48  --abstr_ref_prep                        false
% 31.77/4.48  --abstr_ref_until_sat                   false
% 31.77/4.48  --abstr_ref_sig_restrict                funpre
% 31.77/4.48  --abstr_ref_af_restrict_to_split_sk     false
% 31.77/4.48  --abstr_ref_under                       []
% 31.77/4.48  
% 31.77/4.48  ------ SAT Options
% 31.77/4.48  
% 31.77/4.48  --sat_mode                              false
% 31.77/4.48  --sat_fm_restart_options                ""
% 31.77/4.48  --sat_gr_def                            false
% 31.77/4.48  --sat_epr_types                         true
% 31.77/4.48  --sat_non_cyclic_types                  false
% 31.77/4.48  --sat_finite_models                     false
% 31.77/4.48  --sat_fm_lemmas                         false
% 31.77/4.48  --sat_fm_prep                           false
% 31.77/4.48  --sat_fm_uc_incr                        true
% 31.77/4.48  --sat_out_model                         small
% 31.77/4.48  --sat_out_clauses                       false
% 31.77/4.48  
% 31.77/4.48  ------ QBF Options
% 31.77/4.48  
% 31.77/4.48  --qbf_mode                              false
% 31.77/4.48  --qbf_elim_univ                         false
% 31.77/4.48  --qbf_dom_inst                          none
% 31.77/4.48  --qbf_dom_pre_inst                      false
% 31.77/4.48  --qbf_sk_in                             false
% 31.77/4.48  --qbf_pred_elim                         true
% 31.77/4.48  --qbf_split                             512
% 31.77/4.48  
% 31.77/4.48  ------ BMC1 Options
% 31.77/4.48  
% 31.77/4.48  --bmc1_incremental                      false
% 31.77/4.48  --bmc1_axioms                           reachable_all
% 31.77/4.48  --bmc1_min_bound                        0
% 31.77/4.48  --bmc1_max_bound                        -1
% 31.77/4.48  --bmc1_max_bound_default                -1
% 31.77/4.48  --bmc1_symbol_reachability              true
% 31.77/4.48  --bmc1_property_lemmas                  false
% 31.77/4.48  --bmc1_k_induction                      false
% 31.77/4.48  --bmc1_non_equiv_states                 false
% 31.77/4.48  --bmc1_deadlock                         false
% 31.77/4.48  --bmc1_ucm                              false
% 31.77/4.48  --bmc1_add_unsat_core                   none
% 31.77/4.48  --bmc1_unsat_core_children              false
% 31.77/4.48  --bmc1_unsat_core_extrapolate_axioms    false
% 31.77/4.48  --bmc1_out_stat                         full
% 31.77/4.48  --bmc1_ground_init                      false
% 31.77/4.48  --bmc1_pre_inst_next_state              false
% 31.77/4.48  --bmc1_pre_inst_state                   false
% 31.77/4.48  --bmc1_pre_inst_reach_state             false
% 31.77/4.48  --bmc1_out_unsat_core                   false
% 31.77/4.48  --bmc1_aig_witness_out                  false
% 31.77/4.48  --bmc1_verbose                          false
% 31.77/4.48  --bmc1_dump_clauses_tptp                false
% 31.77/4.48  --bmc1_dump_unsat_core_tptp             false
% 31.77/4.48  --bmc1_dump_file                        -
% 31.77/4.48  --bmc1_ucm_expand_uc_limit              128
% 31.77/4.48  --bmc1_ucm_n_expand_iterations          6
% 31.77/4.48  --bmc1_ucm_extend_mode                  1
% 31.77/4.48  --bmc1_ucm_init_mode                    2
% 31.77/4.48  --bmc1_ucm_cone_mode                    none
% 31.77/4.48  --bmc1_ucm_reduced_relation_type        0
% 31.77/4.48  --bmc1_ucm_relax_model                  4
% 31.77/4.48  --bmc1_ucm_full_tr_after_sat            true
% 31.77/4.48  --bmc1_ucm_expand_neg_assumptions       false
% 31.77/4.48  --bmc1_ucm_layered_model                none
% 31.77/4.48  --bmc1_ucm_max_lemma_size               10
% 31.77/4.48  
% 31.77/4.48  ------ AIG Options
% 31.77/4.48  
% 31.77/4.48  --aig_mode                              false
% 31.77/4.48  
% 31.77/4.48  ------ Instantiation Options
% 31.77/4.48  
% 31.77/4.48  --instantiation_flag                    true
% 31.77/4.48  --inst_sos_flag                         true
% 31.77/4.48  --inst_sos_phase                        true
% 31.77/4.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.77/4.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.77/4.48  --inst_lit_sel_side                     none
% 31.77/4.48  --inst_solver_per_active                1400
% 31.77/4.48  --inst_solver_calls_frac                1.
% 31.77/4.48  --inst_passive_queue_type               priority_queues
% 31.77/4.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.77/4.48  --inst_passive_queues_freq              [25;2]
% 31.77/4.48  --inst_dismatching                      true
% 31.77/4.48  --inst_eager_unprocessed_to_passive     true
% 31.77/4.48  --inst_prop_sim_given                   true
% 31.77/4.48  --inst_prop_sim_new                     false
% 31.77/4.48  --inst_subs_new                         false
% 31.77/4.48  --inst_eq_res_simp                      false
% 31.77/4.48  --inst_subs_given                       false
% 31.77/4.48  --inst_orphan_elimination               true
% 31.77/4.48  --inst_learning_loop_flag               true
% 31.77/4.48  --inst_learning_start                   3000
% 31.77/4.48  --inst_learning_factor                  2
% 31.77/4.48  --inst_start_prop_sim_after_learn       3
% 31.77/4.48  --inst_sel_renew                        solver
% 31.77/4.48  --inst_lit_activity_flag                true
% 31.77/4.48  --inst_restr_to_given                   false
% 31.77/4.48  --inst_activity_threshold               500
% 31.77/4.48  --inst_out_proof                        true
% 31.77/4.48  
% 31.77/4.48  ------ Resolution Options
% 31.77/4.48  
% 31.77/4.48  --resolution_flag                       false
% 31.77/4.48  --res_lit_sel                           adaptive
% 31.77/4.48  --res_lit_sel_side                      none
% 31.77/4.48  --res_ordering                          kbo
% 31.77/4.48  --res_to_prop_solver                    active
% 31.77/4.48  --res_prop_simpl_new                    false
% 31.77/4.48  --res_prop_simpl_given                  true
% 31.77/4.48  --res_passive_queue_type                priority_queues
% 31.77/4.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.77/4.48  --res_passive_queues_freq               [15;5]
% 31.77/4.48  --res_forward_subs                      full
% 31.77/4.48  --res_backward_subs                     full
% 31.77/4.48  --res_forward_subs_resolution           true
% 31.77/4.48  --res_backward_subs_resolution          true
% 31.77/4.48  --res_orphan_elimination                true
% 31.77/4.48  --res_time_limit                        2.
% 31.77/4.48  --res_out_proof                         true
% 31.77/4.48  
% 31.77/4.48  ------ Superposition Options
% 31.77/4.48  
% 31.77/4.48  --superposition_flag                    true
% 31.77/4.48  --sup_passive_queue_type                priority_queues
% 31.77/4.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.77/4.48  --sup_passive_queues_freq               [8;1;4]
% 31.77/4.48  --demod_completeness_check              fast
% 31.77/4.48  --demod_use_ground                      true
% 31.77/4.48  --sup_to_prop_solver                    passive
% 31.77/4.48  --sup_prop_simpl_new                    true
% 31.77/4.48  --sup_prop_simpl_given                  true
% 31.77/4.48  --sup_fun_splitting                     true
% 31.77/4.48  --sup_smt_interval                      50000
% 31.77/4.48  
% 31.77/4.48  ------ Superposition Simplification Setup
% 31.77/4.48  
% 31.77/4.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.77/4.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.77/4.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.77/4.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.77/4.48  --sup_full_triv                         [TrivRules;PropSubs]
% 31.77/4.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.77/4.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.77/4.48  --sup_immed_triv                        [TrivRules]
% 31.77/4.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.48  --sup_immed_bw_main                     []
% 31.77/4.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.77/4.48  --sup_input_triv                        [Unflattening;TrivRules]
% 31.77/4.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.48  --sup_input_bw                          []
% 31.77/4.48  
% 31.77/4.48  ------ Combination Options
% 31.77/4.48  
% 31.77/4.48  --comb_res_mult                         3
% 31.77/4.48  --comb_sup_mult                         2
% 31.77/4.48  --comb_inst_mult                        10
% 31.77/4.48  
% 31.77/4.48  ------ Debug Options
% 31.77/4.48  
% 31.77/4.48  --dbg_backtrace                         false
% 31.77/4.48  --dbg_dump_prop_clauses                 false
% 31.77/4.48  --dbg_dump_prop_clauses_file            -
% 31.77/4.48  --dbg_out_stat                          false
% 31.77/4.48  
% 31.77/4.48  
% 31.77/4.48  
% 31.77/4.48  
% 31.77/4.48  ------ Proving...
% 31.77/4.48  
% 31.77/4.48  
% 31.77/4.48  % SZS status Theorem for theBenchmark.p
% 31.77/4.48  
% 31.77/4.48  % SZS output start CNFRefutation for theBenchmark.p
% 31.77/4.48  
% 31.77/4.48  fof(f23,conjecture,(
% 31.77/4.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f24,negated_conjecture,(
% 31.77/4.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 31.77/4.48    inference(negated_conjecture,[],[f23])).
% 31.77/4.48  
% 31.77/4.48  fof(f47,plain,(
% 31.77/4.48    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.48    inference(ennf_transformation,[],[f24])).
% 31.77/4.48  
% 31.77/4.48  fof(f52,plain,(
% 31.77/4.48    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 31.77/4.48    introduced(choice_axiom,[])).
% 31.77/4.48  
% 31.77/4.48  fof(f53,plain,(
% 31.77/4.48    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.77/4.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f52])).
% 31.77/4.48  
% 31.77/4.48  fof(f84,plain,(
% 31.77/4.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.77/4.48    inference(cnf_transformation,[],[f53])).
% 31.77/4.48  
% 31.77/4.48  fof(f17,axiom,(
% 31.77/4.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f40,plain,(
% 31.77/4.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.48    inference(ennf_transformation,[],[f17])).
% 31.77/4.48  
% 31.77/4.48  fof(f78,plain,(
% 31.77/4.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f40])).
% 31.77/4.48  
% 31.77/4.48  fof(f4,axiom,(
% 31.77/4.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f27,plain,(
% 31.77/4.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(ennf_transformation,[],[f4])).
% 31.77/4.48  
% 31.77/4.48  fof(f51,plain,(
% 31.77/4.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(nnf_transformation,[],[f27])).
% 31.77/4.48  
% 31.77/4.48  fof(f60,plain,(
% 31.77/4.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f51])).
% 31.77/4.48  
% 31.77/4.48  fof(f16,axiom,(
% 31.77/4.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f39,plain,(
% 31.77/4.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.48    inference(ennf_transformation,[],[f16])).
% 31.77/4.48  
% 31.77/4.48  fof(f76,plain,(
% 31.77/4.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f39])).
% 31.77/4.48  
% 31.77/4.48  fof(f10,axiom,(
% 31.77/4.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f67,plain,(
% 31.77/4.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 31.77/4.48    inference(cnf_transformation,[],[f10])).
% 31.77/4.48  
% 31.77/4.48  fof(f3,axiom,(
% 31.77/4.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f50,plain,(
% 31.77/4.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.77/4.48    inference(nnf_transformation,[],[f3])).
% 31.77/4.48  
% 31.77/4.48  fof(f58,plain,(
% 31.77/4.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f50])).
% 31.77/4.48  
% 31.77/4.48  fof(f2,axiom,(
% 31.77/4.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f25,plain,(
% 31.77/4.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 31.77/4.48    inference(ennf_transformation,[],[f2])).
% 31.77/4.48  
% 31.77/4.48  fof(f26,plain,(
% 31.77/4.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 31.77/4.48    inference(flattening,[],[f25])).
% 31.77/4.48  
% 31.77/4.48  fof(f57,plain,(
% 31.77/4.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f26])).
% 31.77/4.48  
% 31.77/4.48  fof(f59,plain,(
% 31.77/4.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f50])).
% 31.77/4.48  
% 31.77/4.48  fof(f22,axiom,(
% 31.77/4.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f45,plain,(
% 31.77/4.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 31.77/4.48    inference(ennf_transformation,[],[f22])).
% 31.77/4.48  
% 31.77/4.48  fof(f46,plain,(
% 31.77/4.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 31.77/4.48    inference(flattening,[],[f45])).
% 31.77/4.48  
% 31.77/4.48  fof(f83,plain,(
% 31.77/4.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f46])).
% 31.77/4.48  
% 31.77/4.48  fof(f77,plain,(
% 31.77/4.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f40])).
% 31.77/4.48  
% 31.77/4.48  fof(f13,axiom,(
% 31.77/4.48    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f71,plain,(
% 31.77/4.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f13])).
% 31.77/4.48  
% 31.77/4.48  fof(f72,plain,(
% 31.77/4.48    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f13])).
% 31.77/4.48  
% 31.77/4.48  fof(f9,axiom,(
% 31.77/4.48    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f33,plain,(
% 31.77/4.48    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 31.77/4.48    inference(ennf_transformation,[],[f9])).
% 31.77/4.48  
% 31.77/4.48  fof(f34,plain,(
% 31.77/4.48    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 31.77/4.48    inference(flattening,[],[f33])).
% 31.77/4.48  
% 31.77/4.48  fof(f66,plain,(
% 31.77/4.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f34])).
% 31.77/4.48  
% 31.77/4.48  fof(f8,axiom,(
% 31.77/4.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f31,plain,(
% 31.77/4.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.77/4.48    inference(ennf_transformation,[],[f8])).
% 31.77/4.48  
% 31.77/4.48  fof(f32,plain,(
% 31.77/4.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(flattening,[],[f31])).
% 31.77/4.48  
% 31.77/4.48  fof(f65,plain,(
% 31.77/4.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f32])).
% 31.77/4.48  
% 31.77/4.48  fof(f12,axiom,(
% 31.77/4.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f36,plain,(
% 31.77/4.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(ennf_transformation,[],[f12])).
% 31.77/4.48  
% 31.77/4.48  fof(f70,plain,(
% 31.77/4.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f36])).
% 31.77/4.48  
% 31.77/4.48  fof(f15,axiom,(
% 31.77/4.48    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f75,plain,(
% 31.77/4.48    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f15])).
% 31.77/4.48  
% 31.77/4.48  fof(f68,plain,(
% 31.77/4.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 31.77/4.48    inference(cnf_transformation,[],[f10])).
% 31.77/4.48  
% 31.77/4.48  fof(f7,axiom,(
% 31.77/4.48    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f30,plain,(
% 31.77/4.48    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(ennf_transformation,[],[f7])).
% 31.77/4.48  
% 31.77/4.48  fof(f64,plain,(
% 31.77/4.48    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f30])).
% 31.77/4.48  
% 31.77/4.48  fof(f6,axiom,(
% 31.77/4.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f29,plain,(
% 31.77/4.48    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(ennf_transformation,[],[f6])).
% 31.77/4.48  
% 31.77/4.48  fof(f63,plain,(
% 31.77/4.48    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f29])).
% 31.77/4.48  
% 31.77/4.48  fof(f1,axiom,(
% 31.77/4.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f48,plain,(
% 31.77/4.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.77/4.48    inference(nnf_transformation,[],[f1])).
% 31.77/4.48  
% 31.77/4.48  fof(f49,plain,(
% 31.77/4.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.77/4.48    inference(flattening,[],[f48])).
% 31.77/4.48  
% 31.77/4.48  fof(f54,plain,(
% 31.77/4.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.77/4.48    inference(cnf_transformation,[],[f49])).
% 31.77/4.48  
% 31.77/4.48  fof(f87,plain,(
% 31.77/4.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.77/4.48    inference(equality_resolution,[],[f54])).
% 31.77/4.48  
% 31.77/4.48  fof(f5,axiom,(
% 31.77/4.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f28,plain,(
% 31.77/4.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(ennf_transformation,[],[f5])).
% 31.77/4.48  
% 31.77/4.48  fof(f62,plain,(
% 31.77/4.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f28])).
% 31.77/4.48  
% 31.77/4.48  fof(f14,axiom,(
% 31.77/4.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f37,plain,(
% 31.77/4.48    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(ennf_transformation,[],[f14])).
% 31.77/4.48  
% 31.77/4.48  fof(f38,plain,(
% 31.77/4.48    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(flattening,[],[f37])).
% 31.77/4.48  
% 31.77/4.48  fof(f74,plain,(
% 31.77/4.48    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f38])).
% 31.77/4.48  
% 31.77/4.48  fof(f11,axiom,(
% 31.77/4.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f35,plain,(
% 31.77/4.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 31.77/4.48    inference(ennf_transformation,[],[f11])).
% 31.77/4.48  
% 31.77/4.48  fof(f69,plain,(
% 31.77/4.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f35])).
% 31.77/4.48  
% 31.77/4.48  fof(f56,plain,(
% 31.77/4.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.77/4.48    inference(cnf_transformation,[],[f49])).
% 31.77/4.48  
% 31.77/4.48  fof(f20,axiom,(
% 31.77/4.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f43,plain,(
% 31.77/4.48    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.48    inference(ennf_transformation,[],[f20])).
% 31.77/4.48  
% 31.77/4.48  fof(f81,plain,(
% 31.77/4.48    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f43])).
% 31.77/4.48  
% 31.77/4.48  fof(f18,axiom,(
% 31.77/4.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f41,plain,(
% 31.77/4.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.48    inference(ennf_transformation,[],[f18])).
% 31.77/4.48  
% 31.77/4.48  fof(f79,plain,(
% 31.77/4.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f41])).
% 31.77/4.48  
% 31.77/4.48  fof(f19,axiom,(
% 31.77/4.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f42,plain,(
% 31.77/4.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.48    inference(ennf_transformation,[],[f19])).
% 31.77/4.48  
% 31.77/4.48  fof(f80,plain,(
% 31.77/4.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f42])).
% 31.77/4.48  
% 31.77/4.48  fof(f85,plain,(
% 31.77/4.48    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 31.77/4.48    inference(cnf_transformation,[],[f53])).
% 31.77/4.48  
% 31.77/4.48  fof(f21,axiom,(
% 31.77/4.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 31.77/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.48  
% 31.77/4.48  fof(f44,plain,(
% 31.77/4.48    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.48    inference(ennf_transformation,[],[f21])).
% 31.77/4.48  
% 31.77/4.48  fof(f82,plain,(
% 31.77/4.48    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.48    inference(cnf_transformation,[],[f44])).
% 31.77/4.48  
% 31.77/4.48  cnf(c_31,negated_conjecture,
% 31.77/4.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.77/4.48      inference(cnf_transformation,[],[f84]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1623,plain,
% 31.77/4.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_23,plain,
% 31.77/4.48      ( v5_relat_1(X0,X1)
% 31.77/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 31.77/4.48      inference(cnf_transformation,[],[f78]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_7,plain,
% 31.77/4.48      ( ~ v5_relat_1(X0,X1)
% 31.77/4.48      | r1_tarski(k2_relat_1(X0),X1)
% 31.77/4.48      | ~ v1_relat_1(X0) ),
% 31.77/4.48      inference(cnf_transformation,[],[f60]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_385,plain,
% 31.77/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.48      | r1_tarski(k2_relat_1(X0),X2)
% 31.77/4.48      | ~ v1_relat_1(X0) ),
% 31.77/4.48      inference(resolution,[status(thm)],[c_23,c_7]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_22,plain,
% 31.77/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.48      | v1_relat_1(X0) ),
% 31.77/4.48      inference(cnf_transformation,[],[f76]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_389,plain,
% 31.77/4.48      ( r1_tarski(k2_relat_1(X0),X2)
% 31.77/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.77/4.48      inference(global_propositional_subsumption,
% 31.77/4.48                [status(thm)],
% 31.77/4.48                [c_385,c_22]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_390,plain,
% 31.77/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.48      | r1_tarski(k2_relat_1(X0),X2) ),
% 31.77/4.48      inference(renaming,[status(thm)],[c_389]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1622,plain,
% 31.77/4.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.77/4.48      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_2196,plain,
% 31.77/4.48      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1623,c_1622]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_14,plain,
% 31.77/4.48      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 31.77/4.48      inference(cnf_transformation,[],[f67]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_5,plain,
% 31.77/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.77/4.48      inference(cnf_transformation,[],[f58]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1641,plain,
% 31.77/4.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.77/4.48      | r1_tarski(X0,X1) = iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_2199,plain,
% 31.77/4.48      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1623,c_1641]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_3,plain,
% 31.77/4.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 31.77/4.48      inference(cnf_transformation,[],[f57]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1643,plain,
% 31.77/4.48      ( r1_tarski(X0,X1) != iProver_top
% 31.77/4.48      | r1_tarski(X2,X0) != iProver_top
% 31.77/4.48      | r1_tarski(X2,X1) = iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_6181,plain,
% 31.77/4.48      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 31.77/4.48      | r1_tarski(X0,sK2) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_2199,c_1643]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_4,plain,
% 31.77/4.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.77/4.48      inference(cnf_transformation,[],[f59]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1642,plain,
% 31.77/4.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.77/4.48      | r1_tarski(X0,X1) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_29,plain,
% 31.77/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 31.77/4.48      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 31.77/4.48      inference(cnf_transformation,[],[f83]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1624,plain,
% 31.77/4.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.77/4.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_2959,plain,
% 31.77/4.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 31.77/4.48      | r1_tarski(X0,k2_zfmisc_1(X3,X2)) != iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1642,c_1624]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_6419,plain,
% 31.77/4.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 31.77/4.48      | r1_tarski(X0,sK2) != iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_6181,c_2959]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_24,plain,
% 31.77/4.48      ( v4_relat_1(X0,X1)
% 31.77/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.77/4.48      inference(cnf_transformation,[],[f77]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1629,plain,
% 31.77/4.48      ( v4_relat_1(X0,X1) = iProver_top
% 31.77/4.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_10390,plain,
% 31.77/4.48      ( v4_relat_1(X0,X1) = iProver_top
% 31.77/4.48      | r1_tarski(X0,sK2) != iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_6419,c_1629]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_46697,plain,
% 31.77/4.48      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 31.77/4.48      | r1_tarski(X0,X1) != iProver_top
% 31.77/4.48      | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_14,c_10390]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_19,plain,
% 31.77/4.48      ( v1_relat_1(k6_relat_1(X0)) ),
% 31.77/4.48      inference(cnf_transformation,[],[f71]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_59,plain,
% 31.77/4.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_18,plain,
% 31.77/4.48      ( v4_relat_1(k6_relat_1(X0),X0) ),
% 31.77/4.48      inference(cnf_transformation,[],[f72]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1633,plain,
% 31.77/4.48      ( v4_relat_1(k6_relat_1(X0),X0) = iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_12,plain,
% 31.77/4.48      ( ~ v4_relat_1(X0,X1)
% 31.77/4.48      | v4_relat_1(X0,X2)
% 31.77/4.48      | ~ r1_tarski(X1,X2)
% 31.77/4.48      | ~ v1_relat_1(X0) ),
% 31.77/4.48      inference(cnf_transformation,[],[f66]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1636,plain,
% 31.77/4.48      ( v4_relat_1(X0,X1) != iProver_top
% 31.77/4.48      | v4_relat_1(X0,X2) = iProver_top
% 31.77/4.48      | r1_tarski(X1,X2) != iProver_top
% 31.77/4.48      | v1_relat_1(X0) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_6893,plain,
% 31.77/4.48      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 31.77/4.48      | r1_tarski(X0,X1) != iProver_top
% 31.77/4.48      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1633,c_1636]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_47182,plain,
% 31.77/4.48      ( r1_tarski(X0,X1) != iProver_top
% 31.77/4.48      | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
% 31.77/4.48      inference(global_propositional_subsumption,
% 31.77/4.48                [status(thm)],
% 31.77/4.48                [c_46697,c_59,c_6893]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_47183,plain,
% 31.77/4.48      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 31.77/4.48      | r1_tarski(X0,X1) != iProver_top ),
% 31.77/4.48      inference(renaming,[status(thm)],[c_47182]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_11,plain,
% 31.77/4.48      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 31.77/4.48      inference(cnf_transformation,[],[f65]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1637,plain,
% 31.77/4.48      ( k7_relat_1(X0,X1) = X0
% 31.77/4.48      | v4_relat_1(X0,X1) != iProver_top
% 31.77/4.48      | v1_relat_1(X0) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_47187,plain,
% 31.77/4.48      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 31.77/4.48      | r1_tarski(X0,X1) != iProver_top
% 31.77/4.48      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_47183,c_1637]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1632,plain,
% 31.77/4.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_16,plain,
% 31.77/4.48      ( ~ v1_relat_1(X0)
% 31.77/4.48      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 31.77/4.48      inference(cnf_transformation,[],[f70]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1634,plain,
% 31.77/4.48      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 31.77/4.48      | v1_relat_1(X1) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_2440,plain,
% 31.77/4.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1632,c_1634]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_21,plain,
% 31.77/4.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
% 31.77/4.48      inference(cnf_transformation,[],[f75]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_2441,plain,
% 31.77/4.48      ( k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 31.77/4.48      inference(light_normalisation,[status(thm)],[c_2440,c_21]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_47188,plain,
% 31.77/4.48      ( k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0)
% 31.77/4.48      | r1_tarski(X0,X1) != iProver_top
% 31.77/4.48      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 31.77/4.48      inference(demodulation,[status(thm)],[c_47187,c_2441]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_135595,plain,
% 31.77/4.48      ( r1_tarski(X0,X1) != iProver_top
% 31.77/4.48      | k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0) ),
% 31.77/4.48      inference(global_propositional_subsumption,
% 31.77/4.48                [status(thm)],
% 31.77/4.48                [c_47188,c_59]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_135596,plain,
% 31.77/4.48      ( k6_relat_1(k3_xboole_0(X0,X1)) = k6_relat_1(X0)
% 31.77/4.48      | r1_tarski(X0,X1) != iProver_top ),
% 31.77/4.48      inference(renaming,[status(thm)],[c_135595]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_135604,plain,
% 31.77/4.48      ( k6_relat_1(k3_xboole_0(k2_relat_1(sK2),sK1)) = k6_relat_1(k2_relat_1(sK2)) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_2196,c_135596]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_13,plain,
% 31.77/4.48      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 31.77/4.48      inference(cnf_transformation,[],[f68]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_137215,plain,
% 31.77/4.48      ( k3_xboole_0(k2_relat_1(sK2),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_135604,c_13]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_137232,plain,
% 31.77/4.48      ( k3_xboole_0(k2_relat_1(sK2),sK1) = k2_relat_1(sK2) ),
% 31.77/4.48      inference(demodulation,[status(thm)],[c_137215,c_13]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1630,plain,
% 31.77/4.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.77/4.48      | v1_relat_1(X0) = iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_2319,plain,
% 31.77/4.48      ( v1_relat_1(sK2) = iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1623,c_1630]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_10,plain,
% 31.77/4.48      ( ~ v1_relat_1(X0)
% 31.77/4.48      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 31.77/4.48      inference(cnf_transformation,[],[f64]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1638,plain,
% 31.77/4.48      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 31.77/4.48      | v1_relat_1(X0) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_4193,plain,
% 31.77/4.48      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_2319,c_1638]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_140055,plain,
% 31.77/4.48      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_137232,c_4193]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_9,plain,
% 31.77/4.48      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 31.77/4.48      inference(cnf_transformation,[],[f63]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1639,plain,
% 31.77/4.48      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 31.77/4.48      | v1_relat_1(X0) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_2,plain,
% 31.77/4.48      ( r1_tarski(X0,X0) ),
% 31.77/4.48      inference(cnf_transformation,[],[f87]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1644,plain,
% 31.77/4.48      ( r1_tarski(X0,X0) = iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_2960,plain,
% 31.77/4.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1623,c_1624]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_3679,plain,
% 31.77/4.48      ( v4_relat_1(sK2,X0) = iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_2960,c_1629]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_4560,plain,
% 31.77/4.48      ( v4_relat_1(sK2,k1_relat_1(sK2)) = iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1644,c_3679]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_5087,plain,
% 31.77/4.48      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2
% 31.77/4.48      | v1_relat_1(sK2) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_4560,c_1637]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_7025,plain,
% 31.77/4.48      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 31.77/4.48      inference(global_propositional_subsumption,
% 31.77/4.48                [status(thm)],
% 31.77/4.48                [c_5087,c_2319]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_8,plain,
% 31.77/4.48      ( ~ v1_relat_1(X0)
% 31.77/4.48      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 31.77/4.48      inference(cnf_transformation,[],[f62]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1640,plain,
% 31.77/4.48      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 31.77/4.48      | v1_relat_1(X0) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_3134,plain,
% 31.77/4.48      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_2319,c_1640]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_7028,plain,
% 31.77/4.48      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_7025,c_3134]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_20,plain,
% 31.77/4.48      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 31.77/4.48      | ~ r1_tarski(X0,k1_relat_1(X1))
% 31.77/4.48      | ~ v1_relat_1(X1) ),
% 31.77/4.48      inference(cnf_transformation,[],[f74]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1631,plain,
% 31.77/4.48      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 31.77/4.48      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 31.77/4.48      | v1_relat_1(X1) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_7184,plain,
% 31.77/4.48      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 31.77/4.48      | v1_relat_1(sK2) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_7028,c_1631]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_32183,plain,
% 31.77/4.48      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top ),
% 31.77/4.48      inference(global_propositional_subsumption,
% 31.77/4.48                [status(thm)],
% 31.77/4.48                [c_7184,c_2319]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_32184,plain,
% 31.77/4.48      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 31.77/4.48      inference(renaming,[status(thm)],[c_32183]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_32202,plain,
% 31.77/4.48      ( v4_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
% 31.77/4.48      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_32184,c_3679]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_32511,plain,
% 31.77/4.48      ( k7_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = sK2
% 31.77/4.48      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 31.77/4.48      | v1_relat_1(sK2) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_32202,c_1637]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_76551,plain,
% 31.77/4.48      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 31.77/4.48      | k7_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = sK2 ),
% 31.77/4.48      inference(global_propositional_subsumption,
% 31.77/4.48                [status(thm)],
% 31.77/4.48                [c_32511,c_2319]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_76552,plain,
% 31.77/4.48      ( k7_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = sK2
% 31.77/4.48      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 31.77/4.48      inference(renaming,[status(thm)],[c_76551]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_76555,plain,
% 31.77/4.48      ( k7_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = sK2 ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1644,c_76552]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_15,plain,
% 31.77/4.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 31.77/4.48      inference(cnf_transformation,[],[f69]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1635,plain,
% 31.77/4.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 31.77/4.48      | v1_relat_1(X0) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_77021,plain,
% 31.77/4.48      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top
% 31.77/4.48      | v1_relat_1(sK2) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_76555,c_1635]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_78332,plain,
% 31.77/4.48      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) = iProver_top ),
% 31.77/4.48      inference(global_propositional_subsumption,
% 31.77/4.48                [status(thm)],
% 31.77/4.48                [c_77021,c_2319]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_0,plain,
% 31.77/4.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.77/4.48      inference(cnf_transformation,[],[f56]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1645,plain,
% 31.77/4.48      ( X0 = X1
% 31.77/4.48      | r1_tarski(X0,X1) != iProver_top
% 31.77/4.48      | r1_tarski(X1,X0) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_78338,plain,
% 31.77/4.48      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
% 31.77/4.48      | r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2)) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_78332,c_1645]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_84153,plain,
% 31.77/4.48      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
% 31.77/4.48      | v1_relat_1(sK2) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1639,c_78338]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_84156,plain,
% 31.77/4.48      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 31.77/4.48      inference(global_propositional_subsumption,
% 31.77/4.48                [status(thm)],
% 31.77/4.48                [c_84153,c_2319]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_140062,plain,
% 31.77/4.48      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 31.77/4.48      inference(light_normalisation,[status(thm)],[c_140055,c_84156]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_27,plain,
% 31.77/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.48      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 31.77/4.48      inference(cnf_transformation,[],[f81]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1626,plain,
% 31.77/4.48      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 31.77/4.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_5693,plain,
% 31.77/4.48      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1623,c_1626]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_25,plain,
% 31.77/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 31.77/4.48      inference(cnf_transformation,[],[f79]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1628,plain,
% 31.77/4.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.77/4.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_4964,plain,
% 31.77/4.48      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1623,c_1628]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_26,plain,
% 31.77/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.77/4.48      inference(cnf_transformation,[],[f80]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1627,plain,
% 31.77/4.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 31.77/4.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_4285,plain,
% 31.77/4.48      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1623,c_1627]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_30,negated_conjecture,
% 31.77/4.48      ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
% 31.77/4.48      | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
% 31.77/4.48      inference(cnf_transformation,[],[f85]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_4291,plain,
% 31.77/4.48      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
% 31.77/4.48      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 31.77/4.48      inference(demodulation,[status(thm)],[c_4285,c_30]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_5225,plain,
% 31.77/4.48      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
% 31.77/4.48      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 31.77/4.48      inference(demodulation,[status(thm)],[c_4964,c_4291]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_28,plain,
% 31.77/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.48      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 31.77/4.48      inference(cnf_transformation,[],[f82]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_1625,plain,
% 31.77/4.48      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 31.77/4.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.77/4.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_5096,plain,
% 31.77/4.48      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1623,c_1625]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_5226,plain,
% 31.77/4.48      ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
% 31.77/4.48      | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
% 31.77/4.48      inference(demodulation,[status(thm)],[c_5225,c_5096]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_6331,plain,
% 31.77/4.48      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
% 31.77/4.48      | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
% 31.77/4.48      inference(demodulation,[status(thm)],[c_5693,c_5226]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_3678,plain,
% 31.77/4.48      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_1623,c_1629]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_5086,plain,
% 31.77/4.48      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_3678,c_1637]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_2323,plain,
% 31.77/4.48      ( v1_relat_1(sK2) ),
% 31.77/4.48      inference(predicate_to_equality_rev,[status(thm)],[c_2319]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_3683,plain,
% 31.77/4.48      ( v4_relat_1(sK2,sK0) ),
% 31.77/4.48      inference(predicate_to_equality_rev,[status(thm)],[c_3678]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_4903,plain,
% 31.77/4.48      ( ~ v4_relat_1(sK2,X0)
% 31.77/4.48      | ~ v1_relat_1(sK2)
% 31.77/4.48      | k7_relat_1(sK2,X0) = sK2 ),
% 31.77/4.48      inference(instantiation,[status(thm)],[c_11]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_4905,plain,
% 31.77/4.48      ( ~ v4_relat_1(sK2,sK0)
% 31.77/4.48      | ~ v1_relat_1(sK2)
% 31.77/4.48      | k7_relat_1(sK2,sK0) = sK2 ),
% 31.77/4.48      inference(instantiation,[status(thm)],[c_4903]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_5301,plain,
% 31.77/4.48      ( k7_relat_1(sK2,sK0) = sK2 ),
% 31.77/4.48      inference(global_propositional_subsumption,
% 31.77/4.48                [status(thm)],
% 31.77/4.48                [c_5086,c_2323,c_3683,c_4905]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_5304,plain,
% 31.77/4.48      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 31.77/4.48      inference(superposition,[status(thm)],[c_5301,c_3134]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_6332,plain,
% 31.77/4.48      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
% 31.77/4.48      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 31.77/4.48      inference(light_normalisation,[status(thm)],[c_6331,c_5304]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(c_6333,plain,
% 31.77/4.48      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
% 31.77/4.48      inference(equality_resolution_simp,[status(thm)],[c_6332]) ).
% 31.77/4.48  
% 31.77/4.48  cnf(contradiction,plain,
% 31.77/4.48      ( $false ),
% 31.77/4.48      inference(minisat,[status(thm)],[c_140062,c_6333]) ).
% 31.77/4.48  
% 31.77/4.48  
% 31.77/4.48  % SZS output end CNFRefutation for theBenchmark.p
% 31.77/4.48  
% 31.77/4.48  ------                               Statistics
% 31.77/4.48  
% 31.77/4.48  ------ General
% 31.77/4.48  
% 31.77/4.48  abstr_ref_over_cycles:                  0
% 31.77/4.48  abstr_ref_under_cycles:                 0
% 31.77/4.48  gc_basic_clause_elim:                   0
% 31.77/4.48  forced_gc_time:                         0
% 31.77/4.48  parsing_time:                           0.009
% 31.77/4.48  unif_index_cands_time:                  0.
% 31.77/4.48  unif_index_add_time:                    0.
% 31.77/4.48  orderings_time:                         0.
% 31.77/4.48  out_proof_time:                         0.037
% 31.77/4.48  total_time:                             3.987
% 31.77/4.48  num_of_symbols:                         53
% 31.77/4.48  num_of_terms:                           112223
% 31.77/4.48  
% 31.77/4.48  ------ Preprocessing
% 31.77/4.48  
% 31.77/4.48  num_of_splits:                          0
% 31.77/4.48  num_of_split_atoms:                     0
% 31.77/4.48  num_of_reused_defs:                     0
% 31.77/4.48  num_eq_ax_congr_red:                    22
% 31.77/4.48  num_of_sem_filtered_clauses:            1
% 31.77/4.48  num_of_subtypes:                        0
% 31.77/4.48  monotx_restored_types:                  0
% 31.77/4.48  sat_num_of_epr_types:                   0
% 31.77/4.48  sat_num_of_non_cyclic_types:            0
% 31.77/4.48  sat_guarded_non_collapsed_types:        0
% 31.77/4.48  num_pure_diseq_elim:                    0
% 31.77/4.48  simp_replaced_by:                       0
% 31.77/4.48  res_preprocessed:                       155
% 31.77/4.48  prep_upred:                             0
% 31.77/4.48  prep_unflattend:                        20
% 31.77/4.48  smt_new_axioms:                         0
% 31.77/4.48  pred_elim_cands:                        4
% 31.77/4.48  pred_elim:                              1
% 31.77/4.48  pred_elim_cl:                           2
% 31.77/4.48  pred_elim_cycles:                       3
% 31.77/4.48  merged_defs:                            8
% 31.77/4.48  merged_defs_ncl:                        0
% 31.77/4.48  bin_hyper_res:                          8
% 31.77/4.48  prep_cycles:                            4
% 31.77/4.48  pred_elim_time:                         0.007
% 31.77/4.48  splitting_time:                         0.
% 31.77/4.48  sem_filter_time:                        0.
% 31.77/4.48  monotx_time:                            0.001
% 31.77/4.48  subtype_inf_time:                       0.
% 31.77/4.48  
% 31.77/4.48  ------ Problem properties
% 31.77/4.48  
% 31.77/4.48  clauses:                                29
% 31.77/4.48  conjectures:                            2
% 31.77/4.48  epr:                                    4
% 31.77/4.48  horn:                                   29
% 31.77/4.48  ground:                                 2
% 31.77/4.48  unary:                                  8
% 31.77/4.48  binary:                                 15
% 31.77/4.48  lits:                                   57
% 31.77/4.48  lits_eq:                                14
% 31.77/4.48  fd_pure:                                0
% 31.77/4.48  fd_pseudo:                              0
% 31.77/4.48  fd_cond:                                0
% 31.77/4.48  fd_pseudo_cond:                         1
% 31.77/4.48  ac_symbols:                             0
% 31.77/4.48  
% 31.77/4.48  ------ Propositional Solver
% 31.77/4.48  
% 31.77/4.48  prop_solver_calls:                      62
% 31.77/4.48  prop_fast_solver_calls:                 3059
% 31.77/4.48  smt_solver_calls:                       0
% 31.77/4.48  smt_fast_solver_calls:                  0
% 31.77/4.48  prop_num_of_clauses:                    61643
% 31.77/4.48  prop_preprocess_simplified:             99579
% 31.77/4.48  prop_fo_subsumed:                       107
% 31.77/4.48  prop_solver_time:                       0.
% 31.77/4.48  smt_solver_time:                        0.
% 31.77/4.48  smt_fast_solver_time:                   0.
% 31.77/4.48  prop_fast_solver_time:                  0.
% 31.77/4.48  prop_unsat_core_time:                   0.006
% 31.77/4.48  
% 31.77/4.48  ------ QBF
% 31.77/4.48  
% 31.77/4.48  qbf_q_res:                              0
% 31.77/4.48  qbf_num_tautologies:                    0
% 31.77/4.48  qbf_prep_cycles:                        0
% 31.77/4.48  
% 31.77/4.48  ------ BMC1
% 31.77/4.48  
% 31.77/4.48  bmc1_current_bound:                     -1
% 31.77/4.48  bmc1_last_solved_bound:                 -1
% 31.77/4.48  bmc1_unsat_core_size:                   -1
% 31.77/4.48  bmc1_unsat_core_parents_size:           -1
% 31.77/4.48  bmc1_merge_next_fun:                    0
% 31.77/4.48  bmc1_unsat_core_clauses_time:           0.
% 31.77/4.48  
% 31.77/4.48  ------ Instantiation
% 31.77/4.48  
% 31.77/4.48  inst_num_of_clauses:                    7090
% 31.77/4.48  inst_num_in_passive:                    4340
% 31.77/4.48  inst_num_in_active:                     4320
% 31.77/4.48  inst_num_in_unprocessed:                1218
% 31.77/4.48  inst_num_of_loops:                      5029
% 31.77/4.48  inst_num_of_learning_restarts:          1
% 31.77/4.48  inst_num_moves_active_passive:          707
% 31.77/4.48  inst_lit_activity:                      0
% 31.77/4.48  inst_lit_activity_moves:                2
% 31.77/4.48  inst_num_tautologies:                   0
% 31.77/4.48  inst_num_prop_implied:                  0
% 31.77/4.48  inst_num_existing_simplified:           0
% 31.77/4.48  inst_num_eq_res_simplified:             0
% 31.77/4.48  inst_num_child_elim:                    0
% 31.77/4.48  inst_num_of_dismatching_blockings:      13433
% 31.77/4.48  inst_num_of_non_proper_insts:           21360
% 31.77/4.48  inst_num_of_duplicates:                 0
% 31.77/4.48  inst_inst_num_from_inst_to_res:         0
% 31.77/4.48  inst_dismatching_checking_time:         0.
% 31.77/4.48  
% 31.77/4.48  ------ Resolution
% 31.77/4.48  
% 31.77/4.48  res_num_of_clauses:                     47
% 31.77/4.48  res_num_in_passive:                     47
% 31.77/4.48  res_num_in_active:                      0
% 31.77/4.48  res_num_of_loops:                       159
% 31.77/4.48  res_forward_subset_subsumed:            1820
% 31.77/4.48  res_backward_subset_subsumed:           0
% 31.77/4.48  res_forward_subsumed:                   0
% 31.77/4.48  res_backward_subsumed:                  0
% 31.77/4.48  res_forward_subsumption_resolution:     0
% 31.77/4.48  res_backward_subsumption_resolution:    0
% 31.77/4.48  res_clause_to_clause_subsumption:       21656
% 31.77/4.48  res_orphan_elimination:                 0
% 31.77/4.48  res_tautology_del:                      2200
% 31.77/4.48  res_num_eq_res_simplified:              0
% 31.77/4.48  res_num_sel_changes:                    0
% 31.77/4.48  res_moves_from_active_to_pass:          0
% 31.77/4.48  
% 31.77/4.48  ------ Superposition
% 31.77/4.48  
% 31.77/4.48  sup_time_total:                         0.
% 31.77/4.48  sup_time_generating:                    0.
% 31.77/4.48  sup_time_sim_full:                      0.
% 31.77/4.48  sup_time_sim_immed:                     0.
% 31.77/4.48  
% 31.77/4.48  sup_num_of_clauses:                     5822
% 31.77/4.48  sup_num_in_active:                      941
% 31.77/4.48  sup_num_in_passive:                     4881
% 31.77/4.48  sup_num_of_loops:                       1005
% 31.77/4.48  sup_fw_superposition:                   4269
% 31.77/4.48  sup_bw_superposition:                   3509
% 31.77/4.48  sup_immediate_simplified:               1428
% 31.77/4.48  sup_given_eliminated:                   5
% 31.77/4.48  comparisons_done:                       0
% 31.77/4.48  comparisons_avoided:                    0
% 31.77/4.48  
% 31.77/4.48  ------ Simplifications
% 31.77/4.48  
% 31.77/4.48  
% 31.77/4.48  sim_fw_subset_subsumed:                 378
% 31.77/4.48  sim_bw_subset_subsumed:                 60
% 31.77/4.48  sim_fw_subsumed:                        556
% 31.77/4.48  sim_bw_subsumed:                        53
% 31.77/4.48  sim_fw_subsumption_res:                 0
% 31.77/4.48  sim_bw_subsumption_res:                 0
% 31.77/4.48  sim_tautology_del:                      15
% 31.77/4.48  sim_eq_tautology_del:                   162
% 31.77/4.48  sim_eq_res_simp:                        1
% 31.77/4.48  sim_fw_demodulated:                     464
% 31.77/4.48  sim_bw_demodulated:                     88
% 31.77/4.48  sim_light_normalised:                   300
% 31.77/4.48  sim_joinable_taut:                      0
% 31.77/4.48  sim_joinable_simp:                      0
% 31.77/4.48  sim_ac_normalised:                      0
% 31.77/4.48  sim_smt_subsumption:                    0
% 31.77/4.48  
%------------------------------------------------------------------------------
