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
% DateTime   : Thu Dec  3 11:56:03 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  284 (20809 expanded)
%              Number of clauses        :  197 (8132 expanded)
%              Number of leaves         :   25 (3925 expanded)
%              Depth                    :   39
%              Number of atoms          :  604 (49759 expanded)
%              Number of equality atoms :  442 (23722 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f79,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

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

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f71,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1476,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1481,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2227,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1481])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1490,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6774,plain,
    ( k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_1490])).

cnf(c_7453,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK2)) = k10_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2227,c_6774])).

cnf(c_24,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1482,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7451,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_1482,c_6774])).

cnf(c_20,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7466,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_7451,c_20])).

cnf(c_8,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1491,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8479,plain,
    ( r1_tarski(k10_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1),k10_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7466,c_1491])).

cnf(c_10749,plain,
    ( r1_tarski(k10_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2))),X0),k1_relat_1(k5_relat_1(sK2,sK2))) = iProver_top
    | v1_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7453,c_8479])).

cnf(c_11,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1483,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5903,plain,
    ( k7_relat_1(k2_zfmisc_1(X0,X1),X2) = k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1483])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_92,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14343,plain,
    ( r1_tarski(X0,X2) != iProver_top
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k7_relat_1(k2_zfmisc_1(X0,X1),X2) = k2_zfmisc_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5903,c_92])).

cnf(c_14344,plain,
    ( k7_relat_1(k2_zfmisc_1(X0,X1),X2) = k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_14343])).

cnf(c_14369,plain,
    ( k10_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2))),X0) = k1_xboole_0
    | k7_relat_1(k2_zfmisc_1(k10_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2))),X0),X1),k1_relat_1(k5_relat_1(sK2,sK2))) = k2_zfmisc_1(k10_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2))),X0),X1)
    | k1_xboole_0 = X1
    | v1_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10749,c_14344])).

cnf(c_16,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1486,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3140,plain,
    ( k6_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1486])).

cnf(c_52,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3915,plain,
    ( k1_xboole_0 != X0
    | k6_relat_1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3140,c_52])).

cnf(c_3916,plain,
    ( k6_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3915])).

cnf(c_3920,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3916])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1496,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1495,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_26,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_26,c_12])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_26,c_25,c_12])).

cnf(c_1475,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_1865,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1475])).

cnf(c_2219,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1865])).

cnf(c_2821,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1496,c_2219])).

cnf(c_1493,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2027,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1493])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1484,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2364,plain,
    ( k5_relat_1(k6_relat_1(X0),k1_xboole_0) = k7_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2027,c_1484])).

cnf(c_2824,plain,
    ( k5_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2821,c_2364])).

cnf(c_4157,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3920,c_2824])).

cnf(c_10,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2039,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1494])).

cnf(c_1864,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_1476,c_1475])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1492,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3001,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2227,c_1492])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1489,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12091,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3001,c_1489])).

cnf(c_21,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1485,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6710,plain,
    ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k7_relat_1(sK2,X0)
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3001,c_1485])).

cnf(c_12788,plain,
    ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(k2_relat_1(X1))) = k7_relat_1(sK2,X0)
    | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12091,c_6710])).

cnf(c_14093,plain,
    ( k5_relat_1(k7_relat_1(sK2,sK0),k6_relat_1(k2_relat_1(X0))) = k7_relat_1(sK2,sK0)
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_12788])).

cnf(c_14094,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(X0))) = sK2
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14093,c_1864])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1685,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1686,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1685])).

cnf(c_14099,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | k5_relat_1(sK2,k6_relat_1(k2_relat_1(X0))) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14094,c_33,c_1686])).

cnf(c_14100,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(X0))) = sK2
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14099])).

cnf(c_14108,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(k2_zfmisc_1(sK0,sK1)))) = sK2
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2039,c_14100])).

cnf(c_6636,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6637,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6636])).

cnf(c_14199,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(k2_zfmisc_1(sK0,sK1)))) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14108,c_6637])).

cnf(c_14202,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK1)) = sK2
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_14199])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1478,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5799,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1476,c_1478])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1477,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5132,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1476,c_1477])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1480,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4387,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1476,c_1480])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1479,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3994,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1476,c_1479])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4019,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3994,c_31])).

cnf(c_4498,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4387,c_4019])).

cnf(c_5212,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5132,c_4498])).

cnf(c_5991,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5799,c_5212])).

cnf(c_3235,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1864,c_3001])).

cnf(c_5992,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5991,c_3235])).

cnf(c_5993,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_5992])).

cnf(c_14205,plain,
    ( k10_relat_1(sK2,k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_14199,c_7466])).

cnf(c_14221,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2)
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_14205])).

cnf(c_14270,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14202,c_5993,c_14221])).

cnf(c_14274,plain,
    ( k10_relat_1(sK2,k2_relat_1(k2_zfmisc_1(sK0,k1_xboole_0))) = k1_relat_1(sK2)
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14270,c_14205])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14332,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_relat_1(sK2)
    | sK0 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14274,c_1,c_15])).

cnf(c_14278,plain,
    ( k10_relat_1(sK2,k1_xboole_0) != k1_relat_1(sK2)
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14270,c_5993])).

cnf(c_14334,plain,
    ( sK0 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14332,c_14278])).

cnf(c_14355,plain,
    ( k7_relat_1(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,X0)
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_2039,c_14344])).

cnf(c_16523,plain,
    ( k7_relat_1(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(k1_xboole_0,sK1)) = k2_zfmisc_1(sK2,X0)
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_14334,c_14355])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_16569,plain,
    ( k7_relat_1(k2_zfmisc_1(sK2,X0),k1_xboole_0) = k2_zfmisc_1(sK2,X0)
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_16523,c_2])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1487,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3780,plain,
    ( k9_relat_1(sK2,X0) != k1_xboole_0
    | k7_relat_1(sK2,X0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3001,c_1487])).

cnf(c_4089,plain,
    ( k7_relat_1(sK2,sK0) = k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3235,c_3780])).

cnf(c_4090,plain,
    ( k7_relat_1(sK2,sK0) = k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4089,c_1864])).

cnf(c_4091,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4090,c_1864])).

cnf(c_4148,plain,
    ( sK2 = k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4091,c_33,c_1686])).

cnf(c_4149,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4148])).

cnf(c_5905,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1483])).

cnf(c_7120,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5905,c_52])).

cnf(c_7121,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7120])).

cnf(c_12787,plain,
    ( k7_relat_1(k6_relat_1(k9_relat_1(sK2,X0)),k2_relat_1(X1)) = k6_relat_1(k9_relat_1(sK2,X0))
    | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12091,c_7121])).

cnf(c_15634,plain,
    ( k7_relat_1(k6_relat_1(k9_relat_1(sK2,sK0)),k2_relat_1(X0)) = k6_relat_1(k9_relat_1(sK2,sK0))
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_12787])).

cnf(c_15635,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(X0)) = k6_relat_1(k2_relat_1(sK2))
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15634,c_1864,c_3235])).

cnf(c_15640,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(X0)) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15635,c_33,c_1686])).

cnf(c_15641,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(X0)) = k6_relat_1(k2_relat_1(sK2))
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15640])).

cnf(c_15649,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k6_relat_1(k2_relat_1(sK2))
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2039,c_15641])).

cnf(c_15654,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15649,c_6637])).

cnf(c_2999,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_1482,c_1492])).

cnf(c_15658,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_15654,c_2999])).

cnf(c_19,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15660,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_15658,c_19])).

cnf(c_16517,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(k1_xboole_0,sK1))) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_14334,c_15660])).

cnf(c_16518,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(k1_xboole_0,sK1))) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_14334,c_15654])).

cnf(c_12097,plain,
    ( r1_tarski(X0,k7_relat_1(sK2,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3001,c_1489])).

cnf(c_12886,plain,
    ( k5_relat_1(X0,k6_relat_1(k9_relat_1(sK2,X1))) = X0
    | r1_tarski(X0,k7_relat_1(sK2,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12097,c_1485])).

cnf(c_13381,plain,
    ( k5_relat_1(X0,k6_relat_1(k9_relat_1(sK2,sK0))) = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_12886])).

cnf(c_13386,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(sK2))) = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13381,c_1864,c_3235])).

cnf(c_13425,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(sK2))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13386,c_33,c_1686])).

cnf(c_13426,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(sK2))) = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13425])).

cnf(c_13434,plain,
    ( k5_relat_1(k1_xboole_0,k6_relat_1(k2_relat_1(sK2))) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_13426])).

cnf(c_2363,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_1482,c_1484])).

cnf(c_4158,plain,
    ( k5_relat_1(k1_xboole_0,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3920,c_2363])).

cnf(c_13451,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13434,c_4158])).

cnf(c_49,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_51,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_1680,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1681,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1680])).

cnf(c_1683,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1681])).

cnf(c_1894,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1897,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_1899,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_13998,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13451,c_51,c_1683,c_1899])).

cnf(c_16598,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16518,c_2,c_15,c_13998])).

cnf(c_16600,plain,
    ( k9_relat_1(k1_xboole_0,k2_relat_1(k2_zfmisc_1(k1_xboole_0,sK1))) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_16517,c_16598])).

cnf(c_3000,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2027,c_1492])).

cnf(c_3005,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3000,c_15,c_2821])).

cnf(c_16602,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16600,c_3005])).

cnf(c_19020,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16569,c_4149,c_16602])).

cnf(c_25965,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | k7_relat_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,X0),X1),k1_xboole_0) = k2_zfmisc_1(k10_relat_1(k1_xboole_0,X0),X1)
    | k1_xboole_0 = X1
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14369,c_16,c_3920,c_4157,c_19020])).

cnf(c_25970,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | k7_relat_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,X0),X1),k1_xboole_0) = k2_zfmisc_1(k10_relat_1(k1_xboole_0,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_25965,c_2027])).

cnf(c_2460,plain,
    ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_1491])).

cnf(c_2978,plain,
    ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2460,c_51,c_1683,c_1899])).

cnf(c_2228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1481])).

cnf(c_2357,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_2228])).

cnf(c_2986,plain,
    ( v1_relat_1(k10_relat_1(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_2357])).

cnf(c_19063,plain,
    ( k5_relat_1(k1_xboole_0,k6_relat_1(k2_relat_1(X0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19020,c_14100])).

cnf(c_19308,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(X0)),k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19063,c_4158])).

cnf(c_103,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_22787,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(X0)),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19308,c_103])).

cnf(c_22796,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1482,c_22787])).

cnf(c_22812,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_22796,c_19])).

cnf(c_23304,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22812,c_2999])).

cnf(c_23307,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23304,c_15])).

cnf(c_7454,plain,
    ( k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))) = k10_relat_1(sK2,k1_relat_1(k10_relat_1(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_2986,c_6774])).

cnf(c_7842,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7454,c_1491])).

cnf(c_8761,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7842,c_33,c_1686])).

cnf(c_8768,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0)))),k1_relat_1(sK2)) = k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0)))) ),
    inference(superposition,[status(thm)],[c_8761,c_7121])).

cnf(c_10526,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0)))),k1_relat_1(sK2)) = k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))))) ),
    inference(superposition,[status(thm)],[c_8768,c_2999])).

cnf(c_10527,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0)))),k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))) ),
    inference(demodulation,[status(thm)],[c_10526,c_19])).

cnf(c_19085,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)))),k1_relat_1(k1_xboole_0)) = k1_relat_1(k5_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X0))) ),
    inference(demodulation,[status(thm)],[c_19020,c_10527])).

cnf(c_3388,plain,
    ( k5_relat_1(k6_relat_1(X0),k10_relat_1(k1_xboole_0,X1)) = k7_relat_1(k10_relat_1(k1_xboole_0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2986,c_1484])).

cnf(c_2985,plain,
    ( k7_relat_1(k10_relat_1(k1_xboole_0,X0),X1) = k10_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2978,c_2219])).

cnf(c_3713,plain,
    ( k5_relat_1(k6_relat_1(X0),k10_relat_1(k1_xboole_0,X1)) = k10_relat_1(k1_xboole_0,X1) ),
    inference(demodulation,[status(thm)],[c_3388,c_2985])).

cnf(c_4154,plain,
    ( k5_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)) = k10_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3920,c_3713])).

cnf(c_19193,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X0))),k1_xboole_0) = k1_relat_1(k10_relat_1(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_19085,c_16,c_4154])).

cnf(c_23312,plain,
    ( k1_relat_1(k10_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23307,c_19193])).

cnf(c_24270,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k10_relat_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23312,c_1486])).

cnf(c_25971,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25970,c_2986,c_24270])).

cnf(c_19109,plain,
    ( k10_relat_1(k1_xboole_0,sK1) != k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_19020,c_5993])).

cnf(c_19116,plain,
    ( k10_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19109,c_16])).

cnf(c_25987,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25971,c_19116])).

cnf(c_25988,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_25987])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:06:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.15/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/1.49  
% 7.15/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.15/1.49  
% 7.15/1.49  ------  iProver source info
% 7.15/1.49  
% 7.15/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.15/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.15/1.49  git: non_committed_changes: false
% 7.15/1.49  git: last_make_outside_of_git: false
% 7.15/1.49  
% 7.15/1.49  ------ 
% 7.15/1.49  
% 7.15/1.49  ------ Input Options
% 7.15/1.49  
% 7.15/1.49  --out_options                           all
% 7.15/1.49  --tptp_safe_out                         true
% 7.15/1.49  --problem_path                          ""
% 7.15/1.49  --include_path                          ""
% 7.15/1.49  --clausifier                            res/vclausify_rel
% 7.15/1.49  --clausifier_options                    --mode clausify
% 7.15/1.49  --stdin                                 false
% 7.15/1.49  --stats_out                             all
% 7.15/1.49  
% 7.15/1.49  ------ General Options
% 7.15/1.49  
% 7.15/1.49  --fof                                   false
% 7.15/1.49  --time_out_real                         305.
% 7.15/1.49  --time_out_virtual                      -1.
% 7.15/1.49  --symbol_type_check                     false
% 7.15/1.49  --clausify_out                          false
% 7.15/1.49  --sig_cnt_out                           false
% 7.15/1.49  --trig_cnt_out                          false
% 7.15/1.49  --trig_cnt_out_tolerance                1.
% 7.15/1.49  --trig_cnt_out_sk_spl                   false
% 7.15/1.49  --abstr_cl_out                          false
% 7.15/1.49  
% 7.15/1.49  ------ Global Options
% 7.15/1.49  
% 7.15/1.49  --schedule                              default
% 7.15/1.49  --add_important_lit                     false
% 7.15/1.49  --prop_solver_per_cl                    1000
% 7.15/1.49  --min_unsat_core                        false
% 7.15/1.49  --soft_assumptions                      false
% 7.15/1.49  --soft_lemma_size                       3
% 7.15/1.49  --prop_impl_unit_size                   0
% 7.15/1.49  --prop_impl_unit                        []
% 7.15/1.49  --share_sel_clauses                     true
% 7.15/1.49  --reset_solvers                         false
% 7.15/1.49  --bc_imp_inh                            [conj_cone]
% 7.15/1.49  --conj_cone_tolerance                   3.
% 7.15/1.49  --extra_neg_conj                        none
% 7.15/1.49  --large_theory_mode                     true
% 7.15/1.49  --prolific_symb_bound                   200
% 7.15/1.49  --lt_threshold                          2000
% 7.15/1.49  --clause_weak_htbl                      true
% 7.15/1.49  --gc_record_bc_elim                     false
% 7.15/1.49  
% 7.15/1.49  ------ Preprocessing Options
% 7.15/1.49  
% 7.15/1.49  --preprocessing_flag                    true
% 7.15/1.49  --time_out_prep_mult                    0.1
% 7.15/1.49  --splitting_mode                        input
% 7.15/1.49  --splitting_grd                         true
% 7.15/1.49  --splitting_cvd                         false
% 7.15/1.49  --splitting_cvd_svl                     false
% 7.15/1.49  --splitting_nvd                         32
% 7.15/1.49  --sub_typing                            true
% 7.15/1.49  --prep_gs_sim                           true
% 7.15/1.49  --prep_unflatten                        true
% 7.15/1.49  --prep_res_sim                          true
% 7.15/1.49  --prep_upred                            true
% 7.15/1.49  --prep_sem_filter                       exhaustive
% 7.15/1.49  --prep_sem_filter_out                   false
% 7.15/1.49  --pred_elim                             true
% 7.15/1.49  --res_sim_input                         true
% 7.15/1.49  --eq_ax_congr_red                       true
% 7.15/1.49  --pure_diseq_elim                       true
% 7.15/1.49  --brand_transform                       false
% 7.15/1.49  --non_eq_to_eq                          false
% 7.15/1.49  --prep_def_merge                        true
% 7.15/1.49  --prep_def_merge_prop_impl              false
% 7.15/1.49  --prep_def_merge_mbd                    true
% 7.15/1.49  --prep_def_merge_tr_red                 false
% 7.15/1.49  --prep_def_merge_tr_cl                  false
% 7.15/1.49  --smt_preprocessing                     true
% 7.15/1.49  --smt_ac_axioms                         fast
% 7.15/1.49  --preprocessed_out                      false
% 7.15/1.49  --preprocessed_stats                    false
% 7.15/1.49  
% 7.15/1.49  ------ Abstraction refinement Options
% 7.15/1.49  
% 7.15/1.49  --abstr_ref                             []
% 7.15/1.49  --abstr_ref_prep                        false
% 7.15/1.49  --abstr_ref_until_sat                   false
% 7.15/1.49  --abstr_ref_sig_restrict                funpre
% 7.15/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.15/1.49  --abstr_ref_under                       []
% 7.15/1.49  
% 7.15/1.49  ------ SAT Options
% 7.15/1.49  
% 7.15/1.49  --sat_mode                              false
% 7.15/1.49  --sat_fm_restart_options                ""
% 7.15/1.49  --sat_gr_def                            false
% 7.15/1.49  --sat_epr_types                         true
% 7.15/1.49  --sat_non_cyclic_types                  false
% 7.15/1.49  --sat_finite_models                     false
% 7.15/1.49  --sat_fm_lemmas                         false
% 7.15/1.49  --sat_fm_prep                           false
% 7.15/1.49  --sat_fm_uc_incr                        true
% 7.15/1.49  --sat_out_model                         small
% 7.15/1.49  --sat_out_clauses                       false
% 7.15/1.49  
% 7.15/1.49  ------ QBF Options
% 7.15/1.49  
% 7.15/1.49  --qbf_mode                              false
% 7.15/1.49  --qbf_elim_univ                         false
% 7.15/1.49  --qbf_dom_inst                          none
% 7.15/1.49  --qbf_dom_pre_inst                      false
% 7.15/1.49  --qbf_sk_in                             false
% 7.15/1.49  --qbf_pred_elim                         true
% 7.15/1.49  --qbf_split                             512
% 7.15/1.49  
% 7.15/1.49  ------ BMC1 Options
% 7.15/1.49  
% 7.15/1.49  --bmc1_incremental                      false
% 7.15/1.49  --bmc1_axioms                           reachable_all
% 7.15/1.49  --bmc1_min_bound                        0
% 7.15/1.49  --bmc1_max_bound                        -1
% 7.15/1.49  --bmc1_max_bound_default                -1
% 7.15/1.49  --bmc1_symbol_reachability              true
% 7.15/1.49  --bmc1_property_lemmas                  false
% 7.15/1.49  --bmc1_k_induction                      false
% 7.15/1.49  --bmc1_non_equiv_states                 false
% 7.15/1.49  --bmc1_deadlock                         false
% 7.15/1.49  --bmc1_ucm                              false
% 7.15/1.49  --bmc1_add_unsat_core                   none
% 7.15/1.49  --bmc1_unsat_core_children              false
% 7.15/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.15/1.49  --bmc1_out_stat                         full
% 7.15/1.49  --bmc1_ground_init                      false
% 7.15/1.49  --bmc1_pre_inst_next_state              false
% 7.15/1.49  --bmc1_pre_inst_state                   false
% 7.15/1.49  --bmc1_pre_inst_reach_state             false
% 7.15/1.49  --bmc1_out_unsat_core                   false
% 7.15/1.49  --bmc1_aig_witness_out                  false
% 7.15/1.49  --bmc1_verbose                          false
% 7.15/1.49  --bmc1_dump_clauses_tptp                false
% 7.15/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.15/1.49  --bmc1_dump_file                        -
% 7.15/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.15/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.15/1.49  --bmc1_ucm_extend_mode                  1
% 7.15/1.49  --bmc1_ucm_init_mode                    2
% 7.15/1.49  --bmc1_ucm_cone_mode                    none
% 7.15/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.15/1.49  --bmc1_ucm_relax_model                  4
% 7.15/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.15/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.15/1.49  --bmc1_ucm_layered_model                none
% 7.15/1.50  --bmc1_ucm_max_lemma_size               10
% 7.15/1.50  
% 7.15/1.50  ------ AIG Options
% 7.15/1.50  
% 7.15/1.50  --aig_mode                              false
% 7.15/1.50  
% 7.15/1.50  ------ Instantiation Options
% 7.15/1.50  
% 7.15/1.50  --instantiation_flag                    true
% 7.15/1.50  --inst_sos_flag                         false
% 7.15/1.50  --inst_sos_phase                        true
% 7.15/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.15/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.15/1.50  --inst_lit_sel_side                     num_symb
% 7.15/1.50  --inst_solver_per_active                1400
% 7.15/1.50  --inst_solver_calls_frac                1.
% 7.15/1.50  --inst_passive_queue_type               priority_queues
% 7.15/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.15/1.50  --inst_passive_queues_freq              [25;2]
% 7.15/1.50  --inst_dismatching                      true
% 7.15/1.50  --inst_eager_unprocessed_to_passive     true
% 7.15/1.50  --inst_prop_sim_given                   true
% 7.15/1.50  --inst_prop_sim_new                     false
% 7.15/1.50  --inst_subs_new                         false
% 7.15/1.50  --inst_eq_res_simp                      false
% 7.15/1.50  --inst_subs_given                       false
% 7.15/1.50  --inst_orphan_elimination               true
% 7.15/1.50  --inst_learning_loop_flag               true
% 7.15/1.50  --inst_learning_start                   3000
% 7.15/1.50  --inst_learning_factor                  2
% 7.15/1.50  --inst_start_prop_sim_after_learn       3
% 7.15/1.50  --inst_sel_renew                        solver
% 7.15/1.50  --inst_lit_activity_flag                true
% 7.15/1.50  --inst_restr_to_given                   false
% 7.15/1.50  --inst_activity_threshold               500
% 7.15/1.50  --inst_out_proof                        true
% 7.15/1.50  
% 7.15/1.50  ------ Resolution Options
% 7.15/1.50  
% 7.15/1.50  --resolution_flag                       true
% 7.15/1.50  --res_lit_sel                           adaptive
% 7.15/1.50  --res_lit_sel_side                      none
% 7.15/1.50  --res_ordering                          kbo
% 7.15/1.50  --res_to_prop_solver                    active
% 7.15/1.50  --res_prop_simpl_new                    false
% 7.15/1.50  --res_prop_simpl_given                  true
% 7.15/1.50  --res_passive_queue_type                priority_queues
% 7.15/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.15/1.50  --res_passive_queues_freq               [15;5]
% 7.15/1.50  --res_forward_subs                      full
% 7.15/1.50  --res_backward_subs                     full
% 7.15/1.50  --res_forward_subs_resolution           true
% 7.15/1.50  --res_backward_subs_resolution          true
% 7.15/1.50  --res_orphan_elimination                true
% 7.15/1.50  --res_time_limit                        2.
% 7.15/1.50  --res_out_proof                         true
% 7.15/1.50  
% 7.15/1.50  ------ Superposition Options
% 7.15/1.50  
% 7.15/1.50  --superposition_flag                    true
% 7.15/1.50  --sup_passive_queue_type                priority_queues
% 7.15/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.15/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.15/1.50  --demod_completeness_check              fast
% 7.15/1.50  --demod_use_ground                      true
% 7.15/1.50  --sup_to_prop_solver                    passive
% 7.15/1.50  --sup_prop_simpl_new                    true
% 7.15/1.50  --sup_prop_simpl_given                  true
% 7.15/1.50  --sup_fun_splitting                     false
% 7.15/1.50  --sup_smt_interval                      50000
% 7.15/1.50  
% 7.15/1.50  ------ Superposition Simplification Setup
% 7.15/1.50  
% 7.15/1.50  --sup_indices_passive                   []
% 7.15/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.15/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_full_bw                           [BwDemod]
% 7.15/1.50  --sup_immed_triv                        [TrivRules]
% 7.15/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.15/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_immed_bw_main                     []
% 7.15/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.15/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.50  
% 7.15/1.50  ------ Combination Options
% 7.15/1.50  
% 7.15/1.50  --comb_res_mult                         3
% 7.15/1.50  --comb_sup_mult                         2
% 7.15/1.50  --comb_inst_mult                        10
% 7.15/1.50  
% 7.15/1.50  ------ Debug Options
% 7.15/1.50  
% 7.15/1.50  --dbg_backtrace                         false
% 7.15/1.50  --dbg_dump_prop_clauses                 false
% 7.15/1.50  --dbg_dump_prop_clauses_file            -
% 7.15/1.50  --dbg_out_stat                          false
% 7.15/1.50  ------ Parsing...
% 7.15/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.15/1.50  ------ Proving...
% 7.15/1.50  ------ Problem Properties 
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  clauses                                 32
% 7.15/1.50  conjectures                             2
% 7.15/1.50  EPR                                     1
% 7.15/1.50  Horn                                    29
% 7.15/1.50  unary                                   10
% 7.15/1.50  binary                                  12
% 7.15/1.50  lits                                    66
% 7.15/1.50  lits eq                                 31
% 7.15/1.50  fd_pure                                 0
% 7.15/1.50  fd_pseudo                               0
% 7.15/1.50  fd_cond                                 3
% 7.15/1.50  fd_pseudo_cond                          0
% 7.15/1.50  AC symbols                              0
% 7.15/1.50  
% 7.15/1.50  ------ Schedule dynamic 5 is on 
% 7.15/1.50  
% 7.15/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  ------ 
% 7.15/1.50  Current options:
% 7.15/1.50  ------ 
% 7.15/1.50  
% 7.15/1.50  ------ Input Options
% 7.15/1.50  
% 7.15/1.50  --out_options                           all
% 7.15/1.50  --tptp_safe_out                         true
% 7.15/1.50  --problem_path                          ""
% 7.15/1.50  --include_path                          ""
% 7.15/1.50  --clausifier                            res/vclausify_rel
% 7.15/1.50  --clausifier_options                    --mode clausify
% 7.15/1.50  --stdin                                 false
% 7.15/1.50  --stats_out                             all
% 7.15/1.50  
% 7.15/1.50  ------ General Options
% 7.15/1.50  
% 7.15/1.50  --fof                                   false
% 7.15/1.50  --time_out_real                         305.
% 7.15/1.50  --time_out_virtual                      -1.
% 7.15/1.50  --symbol_type_check                     false
% 7.15/1.50  --clausify_out                          false
% 7.15/1.50  --sig_cnt_out                           false
% 7.15/1.50  --trig_cnt_out                          false
% 7.15/1.50  --trig_cnt_out_tolerance                1.
% 7.15/1.50  --trig_cnt_out_sk_spl                   false
% 7.15/1.50  --abstr_cl_out                          false
% 7.15/1.50  
% 7.15/1.50  ------ Global Options
% 7.15/1.50  
% 7.15/1.50  --schedule                              default
% 7.15/1.50  --add_important_lit                     false
% 7.15/1.50  --prop_solver_per_cl                    1000
% 7.15/1.50  --min_unsat_core                        false
% 7.15/1.50  --soft_assumptions                      false
% 7.15/1.50  --soft_lemma_size                       3
% 7.15/1.50  --prop_impl_unit_size                   0
% 7.15/1.50  --prop_impl_unit                        []
% 7.15/1.50  --share_sel_clauses                     true
% 7.15/1.50  --reset_solvers                         false
% 7.15/1.50  --bc_imp_inh                            [conj_cone]
% 7.15/1.50  --conj_cone_tolerance                   3.
% 7.15/1.50  --extra_neg_conj                        none
% 7.15/1.50  --large_theory_mode                     true
% 7.15/1.50  --prolific_symb_bound                   200
% 7.15/1.50  --lt_threshold                          2000
% 7.15/1.50  --clause_weak_htbl                      true
% 7.15/1.50  --gc_record_bc_elim                     false
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing Options
% 7.15/1.50  
% 7.15/1.50  --preprocessing_flag                    true
% 7.15/1.50  --time_out_prep_mult                    0.1
% 7.15/1.50  --splitting_mode                        input
% 7.15/1.50  --splitting_grd                         true
% 7.15/1.50  --splitting_cvd                         false
% 7.15/1.50  --splitting_cvd_svl                     false
% 7.15/1.50  --splitting_nvd                         32
% 7.15/1.50  --sub_typing                            true
% 7.15/1.50  --prep_gs_sim                           true
% 7.15/1.50  --prep_unflatten                        true
% 7.15/1.50  --prep_res_sim                          true
% 7.15/1.50  --prep_upred                            true
% 7.15/1.50  --prep_sem_filter                       exhaustive
% 7.15/1.50  --prep_sem_filter_out                   false
% 7.15/1.50  --pred_elim                             true
% 7.15/1.50  --res_sim_input                         true
% 7.15/1.50  --eq_ax_congr_red                       true
% 7.15/1.50  --pure_diseq_elim                       true
% 7.15/1.50  --brand_transform                       false
% 7.15/1.50  --non_eq_to_eq                          false
% 7.15/1.50  --prep_def_merge                        true
% 7.15/1.50  --prep_def_merge_prop_impl              false
% 7.15/1.50  --prep_def_merge_mbd                    true
% 7.15/1.50  --prep_def_merge_tr_red                 false
% 7.15/1.50  --prep_def_merge_tr_cl                  false
% 7.15/1.50  --smt_preprocessing                     true
% 7.15/1.50  --smt_ac_axioms                         fast
% 7.15/1.50  --preprocessed_out                      false
% 7.15/1.50  --preprocessed_stats                    false
% 7.15/1.50  
% 7.15/1.50  ------ Abstraction refinement Options
% 7.15/1.50  
% 7.15/1.50  --abstr_ref                             []
% 7.15/1.50  --abstr_ref_prep                        false
% 7.15/1.50  --abstr_ref_until_sat                   false
% 7.15/1.50  --abstr_ref_sig_restrict                funpre
% 7.15/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.15/1.50  --abstr_ref_under                       []
% 7.15/1.50  
% 7.15/1.50  ------ SAT Options
% 7.15/1.50  
% 7.15/1.50  --sat_mode                              false
% 7.15/1.50  --sat_fm_restart_options                ""
% 7.15/1.50  --sat_gr_def                            false
% 7.15/1.50  --sat_epr_types                         true
% 7.15/1.50  --sat_non_cyclic_types                  false
% 7.15/1.50  --sat_finite_models                     false
% 7.15/1.50  --sat_fm_lemmas                         false
% 7.15/1.50  --sat_fm_prep                           false
% 7.15/1.50  --sat_fm_uc_incr                        true
% 7.15/1.50  --sat_out_model                         small
% 7.15/1.50  --sat_out_clauses                       false
% 7.15/1.50  
% 7.15/1.50  ------ QBF Options
% 7.15/1.50  
% 7.15/1.50  --qbf_mode                              false
% 7.15/1.50  --qbf_elim_univ                         false
% 7.15/1.50  --qbf_dom_inst                          none
% 7.15/1.50  --qbf_dom_pre_inst                      false
% 7.15/1.50  --qbf_sk_in                             false
% 7.15/1.50  --qbf_pred_elim                         true
% 7.15/1.50  --qbf_split                             512
% 7.15/1.50  
% 7.15/1.50  ------ BMC1 Options
% 7.15/1.50  
% 7.15/1.50  --bmc1_incremental                      false
% 7.15/1.50  --bmc1_axioms                           reachable_all
% 7.15/1.50  --bmc1_min_bound                        0
% 7.15/1.50  --bmc1_max_bound                        -1
% 7.15/1.50  --bmc1_max_bound_default                -1
% 7.15/1.50  --bmc1_symbol_reachability              true
% 7.15/1.50  --bmc1_property_lemmas                  false
% 7.15/1.50  --bmc1_k_induction                      false
% 7.15/1.50  --bmc1_non_equiv_states                 false
% 7.15/1.50  --bmc1_deadlock                         false
% 7.15/1.50  --bmc1_ucm                              false
% 7.15/1.50  --bmc1_add_unsat_core                   none
% 7.15/1.50  --bmc1_unsat_core_children              false
% 7.15/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.15/1.50  --bmc1_out_stat                         full
% 7.15/1.50  --bmc1_ground_init                      false
% 7.15/1.50  --bmc1_pre_inst_next_state              false
% 7.15/1.50  --bmc1_pre_inst_state                   false
% 7.15/1.50  --bmc1_pre_inst_reach_state             false
% 7.15/1.50  --bmc1_out_unsat_core                   false
% 7.15/1.50  --bmc1_aig_witness_out                  false
% 7.15/1.50  --bmc1_verbose                          false
% 7.15/1.50  --bmc1_dump_clauses_tptp                false
% 7.15/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.15/1.50  --bmc1_dump_file                        -
% 7.15/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.15/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.15/1.50  --bmc1_ucm_extend_mode                  1
% 7.15/1.50  --bmc1_ucm_init_mode                    2
% 7.15/1.50  --bmc1_ucm_cone_mode                    none
% 7.15/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.15/1.50  --bmc1_ucm_relax_model                  4
% 7.15/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.15/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.15/1.50  --bmc1_ucm_layered_model                none
% 7.15/1.50  --bmc1_ucm_max_lemma_size               10
% 7.15/1.50  
% 7.15/1.50  ------ AIG Options
% 7.15/1.50  
% 7.15/1.50  --aig_mode                              false
% 7.15/1.50  
% 7.15/1.50  ------ Instantiation Options
% 7.15/1.50  
% 7.15/1.50  --instantiation_flag                    true
% 7.15/1.50  --inst_sos_flag                         false
% 7.15/1.50  --inst_sos_phase                        true
% 7.15/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.15/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.15/1.50  --inst_lit_sel_side                     none
% 7.15/1.50  --inst_solver_per_active                1400
% 7.15/1.50  --inst_solver_calls_frac                1.
% 7.15/1.50  --inst_passive_queue_type               priority_queues
% 7.15/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.15/1.50  --inst_passive_queues_freq              [25;2]
% 7.15/1.50  --inst_dismatching                      true
% 7.15/1.50  --inst_eager_unprocessed_to_passive     true
% 7.15/1.50  --inst_prop_sim_given                   true
% 7.15/1.50  --inst_prop_sim_new                     false
% 7.15/1.50  --inst_subs_new                         false
% 7.15/1.50  --inst_eq_res_simp                      false
% 7.15/1.50  --inst_subs_given                       false
% 7.15/1.50  --inst_orphan_elimination               true
% 7.15/1.50  --inst_learning_loop_flag               true
% 7.15/1.50  --inst_learning_start                   3000
% 7.15/1.50  --inst_learning_factor                  2
% 7.15/1.50  --inst_start_prop_sim_after_learn       3
% 7.15/1.50  --inst_sel_renew                        solver
% 7.15/1.50  --inst_lit_activity_flag                true
% 7.15/1.50  --inst_restr_to_given                   false
% 7.15/1.50  --inst_activity_threshold               500
% 7.15/1.50  --inst_out_proof                        true
% 7.15/1.50  
% 7.15/1.50  ------ Resolution Options
% 7.15/1.50  
% 7.15/1.50  --resolution_flag                       false
% 7.15/1.50  --res_lit_sel                           adaptive
% 7.15/1.50  --res_lit_sel_side                      none
% 7.15/1.50  --res_ordering                          kbo
% 7.15/1.50  --res_to_prop_solver                    active
% 7.15/1.50  --res_prop_simpl_new                    false
% 7.15/1.50  --res_prop_simpl_given                  true
% 7.15/1.50  --res_passive_queue_type                priority_queues
% 7.15/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.15/1.50  --res_passive_queues_freq               [15;5]
% 7.15/1.50  --res_forward_subs                      full
% 7.15/1.50  --res_backward_subs                     full
% 7.15/1.50  --res_forward_subs_resolution           true
% 7.15/1.50  --res_backward_subs_resolution          true
% 7.15/1.50  --res_orphan_elimination                true
% 7.15/1.50  --res_time_limit                        2.
% 7.15/1.50  --res_out_proof                         true
% 7.15/1.50  
% 7.15/1.50  ------ Superposition Options
% 7.15/1.50  
% 7.15/1.50  --superposition_flag                    true
% 7.15/1.50  --sup_passive_queue_type                priority_queues
% 7.15/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.15/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.15/1.50  --demod_completeness_check              fast
% 7.15/1.50  --demod_use_ground                      true
% 7.15/1.50  --sup_to_prop_solver                    passive
% 7.15/1.50  --sup_prop_simpl_new                    true
% 7.15/1.50  --sup_prop_simpl_given                  true
% 7.15/1.50  --sup_fun_splitting                     false
% 7.15/1.50  --sup_smt_interval                      50000
% 7.15/1.50  
% 7.15/1.50  ------ Superposition Simplification Setup
% 7.15/1.50  
% 7.15/1.50  --sup_indices_passive                   []
% 7.15/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.15/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_full_bw                           [BwDemod]
% 7.15/1.50  --sup_immed_triv                        [TrivRules]
% 7.15/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.15/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_immed_bw_main                     []
% 7.15/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.15/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.50  
% 7.15/1.50  ------ Combination Options
% 7.15/1.50  
% 7.15/1.50  --comb_res_mult                         3
% 7.15/1.50  --comb_sup_mult                         2
% 7.15/1.50  --comb_inst_mult                        10
% 7.15/1.50  
% 7.15/1.50  ------ Debug Options
% 7.15/1.50  
% 7.15/1.50  --dbg_backtrace                         false
% 7.15/1.50  --dbg_dump_prop_clauses                 false
% 7.15/1.50  --dbg_dump_prop_clauses_file            -
% 7.15/1.50  --dbg_out_stat                          false
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  ------ Proving...
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  % SZS status Theorem for theBenchmark.p
% 7.15/1.50  
% 7.15/1.50   Resolution empty clause
% 7.15/1.50  
% 7.15/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  fof(f24,conjecture,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f25,negated_conjecture,(
% 7.15/1.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 7.15/1.50    inference(negated_conjecture,[],[f24])).
% 7.15/1.50  
% 7.15/1.50  fof(f49,plain,(
% 7.15/1.50    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f25])).
% 7.15/1.50  
% 7.15/1.50  fof(f53,plain,(
% 7.15/1.50    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 7.15/1.50    introduced(choice_axiom,[])).
% 7.15/1.50  
% 7.15/1.50  fof(f54,plain,(
% 7.15/1.50    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.15/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53])).
% 7.15/1.50  
% 7.15/1.50  fof(f86,plain,(
% 7.15/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.15/1.50    inference(cnf_transformation,[],[f54])).
% 7.15/1.50  
% 7.15/1.50  fof(f18,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f43,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f18])).
% 7.15/1.50  
% 7.15/1.50  fof(f80,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f43])).
% 7.15/1.50  
% 7.15/1.50  fof(f7,axiom,(
% 7.15/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f30,plain,(
% 7.15/1.50    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f7])).
% 7.15/1.50  
% 7.15/1.50  fof(f64,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f30])).
% 7.15/1.50  
% 7.15/1.50  fof(f17,axiom,(
% 7.15/1.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f27,plain,(
% 7.15/1.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 7.15/1.50    inference(pure_predicate_removal,[],[f17])).
% 7.15/1.50  
% 7.15/1.50  fof(f79,plain,(
% 7.15/1.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f27])).
% 7.15/1.50  
% 7.15/1.50  fof(f13,axiom,(
% 7.15/1.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f74,plain,(
% 7.15/1.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.15/1.50    inference(cnf_transformation,[],[f13])).
% 7.15/1.50  
% 7.15/1.50  fof(f6,axiom,(
% 7.15/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f29,plain,(
% 7.15/1.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(ennf_transformation,[],[f6])).
% 7.15/1.50  
% 7.15/1.50  fof(f63,plain,(
% 7.15/1.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f29])).
% 7.15/1.50  
% 7.15/1.50  fof(f8,axiom,(
% 7.15/1.50    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f31,plain,(
% 7.15/1.50    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.15/1.50    inference(ennf_transformation,[],[f8])).
% 7.15/1.50  
% 7.15/1.50  fof(f65,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.15/1.50    inference(cnf_transformation,[],[f31])).
% 7.15/1.50  
% 7.15/1.50  fof(f16,axiom,(
% 7.15/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f41,plain,(
% 7.15/1.50    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(ennf_transformation,[],[f16])).
% 7.15/1.50  
% 7.15/1.50  fof(f42,plain,(
% 7.15/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(flattening,[],[f41])).
% 7.15/1.50  
% 7.15/1.50  fof(f78,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f42])).
% 7.15/1.50  
% 7.15/1.50  fof(f4,axiom,(
% 7.15/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f61,plain,(
% 7.15/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f4])).
% 7.15/1.50  
% 7.15/1.50  fof(f11,axiom,(
% 7.15/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f70,plain,(
% 7.15/1.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.15/1.50    inference(cnf_transformation,[],[f11])).
% 7.15/1.50  
% 7.15/1.50  fof(f12,axiom,(
% 7.15/1.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f36,plain,(
% 7.15/1.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f12])).
% 7.15/1.50  
% 7.15/1.50  fof(f37,plain,(
% 7.15/1.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.15/1.50    inference(flattening,[],[f36])).
% 7.15/1.50  
% 7.15/1.50  fof(f72,plain,(
% 7.15/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f37])).
% 7.15/1.50  
% 7.15/1.50  fof(f1,axiom,(
% 7.15/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f55,plain,(
% 7.15/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f1])).
% 7.15/1.50  
% 7.15/1.50  fof(f3,axiom,(
% 7.15/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f52,plain,(
% 7.15/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.15/1.50    inference(nnf_transformation,[],[f3])).
% 7.15/1.50  
% 7.15/1.50  fof(f60,plain,(
% 7.15/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f52])).
% 7.15/1.50  
% 7.15/1.50  fof(f2,axiom,(
% 7.15/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f50,plain,(
% 7.15/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.15/1.50    inference(nnf_transformation,[],[f2])).
% 7.15/1.50  
% 7.15/1.50  fof(f51,plain,(
% 7.15/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.15/1.50    inference(flattening,[],[f50])).
% 7.15/1.50  
% 7.15/1.50  fof(f58,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.15/1.50    inference(cnf_transformation,[],[f51])).
% 7.15/1.50  
% 7.15/1.50  fof(f88,plain,(
% 7.15/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.15/1.50    inference(equality_resolution,[],[f58])).
% 7.15/1.50  
% 7.15/1.50  fof(f19,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f26,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.15/1.50    inference(pure_predicate_removal,[],[f19])).
% 7.15/1.50  
% 7.15/1.50  fof(f44,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f26])).
% 7.15/1.50  
% 7.15/1.50  fof(f81,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f44])).
% 7.15/1.50  
% 7.15/1.50  fof(f9,axiom,(
% 7.15/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f32,plain,(
% 7.15/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.15/1.50    inference(ennf_transformation,[],[f9])).
% 7.15/1.50  
% 7.15/1.50  fof(f33,plain,(
% 7.15/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(flattening,[],[f32])).
% 7.15/1.50  
% 7.15/1.50  fof(f67,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f33])).
% 7.15/1.50  
% 7.15/1.50  fof(f15,axiom,(
% 7.15/1.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f40,plain,(
% 7.15/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(ennf_transformation,[],[f15])).
% 7.15/1.50  
% 7.15/1.50  fof(f77,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f40])).
% 7.15/1.50  
% 7.15/1.50  fof(f66,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.15/1.50    inference(cnf_transformation,[],[f31])).
% 7.15/1.50  
% 7.15/1.50  fof(f59,plain,(
% 7.15/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f52])).
% 7.15/1.50  
% 7.15/1.50  fof(f5,axiom,(
% 7.15/1.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f28,plain,(
% 7.15/1.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(ennf_transformation,[],[f5])).
% 7.15/1.50  
% 7.15/1.50  fof(f62,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f28])).
% 7.15/1.50  
% 7.15/1.50  fof(f10,axiom,(
% 7.15/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f34,plain,(
% 7.15/1.50    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f10])).
% 7.15/1.50  
% 7.15/1.50  fof(f35,plain,(
% 7.15/1.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.15/1.50    inference(flattening,[],[f34])).
% 7.15/1.50  
% 7.15/1.50  fof(f69,plain,(
% 7.15/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f35])).
% 7.15/1.50  
% 7.15/1.50  fof(f14,axiom,(
% 7.15/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f38,plain,(
% 7.15/1.50    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(ennf_transformation,[],[f14])).
% 7.15/1.50  
% 7.15/1.50  fof(f39,plain,(
% 7.15/1.50    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(flattening,[],[f38])).
% 7.15/1.50  
% 7.15/1.50  fof(f76,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f39])).
% 7.15/1.50  
% 7.15/1.50  fof(f22,axiom,(
% 7.15/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f47,plain,(
% 7.15/1.50    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f22])).
% 7.15/1.50  
% 7.15/1.50  fof(f84,plain,(
% 7.15/1.50    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f47])).
% 7.15/1.50  
% 7.15/1.50  fof(f23,axiom,(
% 7.15/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f48,plain,(
% 7.15/1.50    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f23])).
% 7.15/1.50  
% 7.15/1.50  fof(f85,plain,(
% 7.15/1.50    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f48])).
% 7.15/1.50  
% 7.15/1.50  fof(f20,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f45,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f20])).
% 7.15/1.50  
% 7.15/1.50  fof(f82,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f45])).
% 7.15/1.50  
% 7.15/1.50  fof(f21,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f46,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f21])).
% 7.15/1.50  
% 7.15/1.50  fof(f83,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f46])).
% 7.15/1.50  
% 7.15/1.50  fof(f87,plain,(
% 7.15/1.50    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 7.15/1.50    inference(cnf_transformation,[],[f54])).
% 7.15/1.50  
% 7.15/1.50  fof(f71,plain,(
% 7.15/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.15/1.50    inference(cnf_transformation,[],[f11])).
% 7.15/1.50  
% 7.15/1.50  fof(f57,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.15/1.50    inference(cnf_transformation,[],[f51])).
% 7.15/1.50  
% 7.15/1.50  fof(f89,plain,(
% 7.15/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.15/1.50    inference(equality_resolution,[],[f57])).
% 7.15/1.50  
% 7.15/1.50  fof(f73,plain,(
% 7.15/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f37])).
% 7.15/1.50  
% 7.15/1.50  fof(f75,plain,(
% 7.15/1.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.15/1.50    inference(cnf_transformation,[],[f13])).
% 7.15/1.50  
% 7.15/1.50  cnf(c_32,negated_conjecture,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.15/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1476,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_25,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1481,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2227,plain,
% 7.15/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1476,c_1481]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_9,plain,
% 7.15/1.50      ( ~ v1_relat_1(X0)
% 7.15/1.50      | ~ v1_relat_1(X1)
% 7.15/1.50      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 7.15/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1490,plain,
% 7.15/1.50      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 7.15/1.50      | v1_relat_1(X1) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6774,plain,
% 7.15/1.50      ( k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2227,c_1490]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7453,plain,
% 7.15/1.50      ( k1_relat_1(k5_relat_1(sK2,sK2)) = k10_relat_1(sK2,k1_relat_1(sK2)) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2227,c_6774]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_24,plain,
% 7.15/1.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.15/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1482,plain,
% 7.15/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7451,plain,
% 7.15/1.50      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1482,c_6774]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_20,plain,
% 7.15/1.50      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7466,plain,
% 7.15/1.50      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_7451,c_20]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8,plain,
% 7.15/1.50      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1491,plain,
% 7.15/1.50      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8479,plain,
% 7.15/1.50      ( r1_tarski(k10_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1),k10_relat_1(sK2,X0)) = iProver_top
% 7.15/1.50      | v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_7466,c_1491]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_10749,plain,
% 7.15/1.50      ( r1_tarski(k10_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2))),X0),k1_relat_1(k5_relat_1(sK2,sK2))) = iProver_top
% 7.15/1.50      | v1_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2)))) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_7453,c_8479]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_11,plain,
% 7.15/1.50      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 7.15/1.50      | k1_xboole_0 = X1
% 7.15/1.50      | k1_xboole_0 = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_23,plain,
% 7.15/1.50      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.15/1.50      | ~ v1_relat_1(X0)
% 7.15/1.50      | k7_relat_1(X0,X1) = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1483,plain,
% 7.15/1.50      ( k7_relat_1(X0,X1) = X0
% 7.15/1.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5903,plain,
% 7.15/1.50      ( k7_relat_1(k2_zfmisc_1(X0,X1),X2) = k2_zfmisc_1(X0,X1)
% 7.15/1.50      | k1_xboole_0 = X0
% 7.15/1.50      | k1_xboole_0 = X1
% 7.15/1.50      | r1_tarski(X0,X2) != iProver_top
% 7.15/1.50      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_11,c_1483]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.15/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_92,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14343,plain,
% 7.15/1.50      ( r1_tarski(X0,X2) != iProver_top
% 7.15/1.50      | k1_xboole_0 = X1
% 7.15/1.50      | k1_xboole_0 = X0
% 7.15/1.50      | k7_relat_1(k2_zfmisc_1(X0,X1),X2) = k2_zfmisc_1(X0,X1) ),
% 7.15/1.50      inference(global_propositional_subsumption,[status(thm)],[c_5903,c_92]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14344,plain,
% 7.15/1.50      ( k7_relat_1(k2_zfmisc_1(X0,X1),X2) = k2_zfmisc_1(X0,X1)
% 7.15/1.50      | k1_xboole_0 = X1
% 7.15/1.50      | k1_xboole_0 = X0
% 7.15/1.50      | r1_tarski(X0,X2) != iProver_top ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_14343]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14369,plain,
% 7.15/1.50      ( k10_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2))),X0) = k1_xboole_0
% 7.15/1.50      | k7_relat_1(k2_zfmisc_1(k10_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2))),X0),X1),k1_relat_1(k5_relat_1(sK2,sK2))) = k2_zfmisc_1(k10_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2))),X0),X1)
% 7.15/1.50      | k1_xboole_0 = X1
% 7.15/1.50      | v1_relat_1(k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK2)))) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_10749,c_14344]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_16,plain,
% 7.15/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_18,plain,
% 7.15/1.50      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1486,plain,
% 7.15/1.50      ( k1_relat_1(X0) != k1_xboole_0
% 7.15/1.50      | k1_xboole_0 = X0
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3140,plain,
% 7.15/1.50      ( k6_relat_1(X0) = k1_xboole_0
% 7.15/1.50      | k1_xboole_0 != X0
% 7.15/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_20,c_1486]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_52,plain,
% 7.15/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3915,plain,
% 7.15/1.50      ( k1_xboole_0 != X0 | k6_relat_1(X0) = k1_xboole_0 ),
% 7.15/1.50      inference(global_propositional_subsumption,[status(thm)],[c_3140,c_52]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3916,plain,
% 7.15/1.50      ( k6_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_3915]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3920,plain,
% 7.15/1.50      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(equality_resolution,[status(thm)],[c_3916]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_0,plain,
% 7.15/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1496,plain,
% 7.15/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1495,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.15/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1,plain,
% 7.15/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_26,plain,
% 7.15/1.50      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.15/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12,plain,
% 7.15/1.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_343,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_relat_1(X0)
% 7.15/1.50      | k7_relat_1(X0,X1) = X0 ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_26,c_12]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_347,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | k7_relat_1(X0,X1) = X0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_343,c_26,c_25,c_12]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1475,plain,
% 7.15/1.50      ( k7_relat_1(X0,X1) = X0
% 7.15/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1865,plain,
% 7.15/1.50      ( k7_relat_1(X0,X1) = X0
% 7.15/1.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1,c_1475]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2219,plain,
% 7.15/1.50      ( k7_relat_1(X0,X1) = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1495,c_1865]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2821,plain,
% 7.15/1.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1496,c_2219]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1493,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2027,plain,
% 7.15/1.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1,c_1493]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_22,plain,
% 7.15/1.50      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1484,plain,
% 7.15/1.50      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.15/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2364,plain,
% 7.15/1.50      ( k5_relat_1(k6_relat_1(X0),k1_xboole_0) = k7_relat_1(k1_xboole_0,X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2027,c_1484]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2824,plain,
% 7.15/1.50      ( k5_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_2821,c_2364]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4157,plain,
% 7.15/1.50      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3920,c_2824]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_10,plain,
% 7.15/1.50      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 7.15/1.50      | k1_xboole_0 = X1
% 7.15/1.50      | k1_xboole_0 = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1494,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.15/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2039,plain,
% 7.15/1.50      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1476,c_1494]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1864,plain,
% 7.15/1.50      ( k7_relat_1(sK2,sK0) = sK2 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1476,c_1475]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7,plain,
% 7.15/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1492,plain,
% 7.15/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3001,plain,
% 7.15/1.50      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2227,c_1492]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13,plain,
% 7.15/1.50      ( ~ r1_tarski(X0,X1)
% 7.15/1.50      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.15/1.50      | ~ v1_relat_1(X1)
% 7.15/1.50      | ~ v1_relat_1(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1489,plain,
% 7.15/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.15/1.50      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12091,plain,
% 7.15/1.50      ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top
% 7.15/1.50      | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
% 7.15/1.50      | v1_relat_1(X1) != iProver_top
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3001,c_1489]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_21,plain,
% 7.15/1.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.15/1.50      | ~ v1_relat_1(X0)
% 7.15/1.50      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1485,plain,
% 7.15/1.50      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 7.15/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6710,plain,
% 7.15/1.50      ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k7_relat_1(sK2,X0)
% 7.15/1.50      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3001,c_1485]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12788,plain,
% 7.15/1.50      ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(k2_relat_1(X1))) = k7_relat_1(sK2,X0)
% 7.15/1.50      | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
% 7.15/1.50      | v1_relat_1(X1) != iProver_top
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_12091,c_6710]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14093,plain,
% 7.15/1.50      ( k5_relat_1(k7_relat_1(sK2,sK0),k6_relat_1(k2_relat_1(X0))) = k7_relat_1(sK2,sK0)
% 7.15/1.50      | r1_tarski(sK2,X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1864,c_12788]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14094,plain,
% 7.15/1.50      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(X0))) = sK2
% 7.15/1.50      | r1_tarski(sK2,X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_14093,c_1864]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_33,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1685,plain,
% 7.15/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.15/1.50      | v1_relat_1(sK2) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_25]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1686,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.15/1.50      | v1_relat_1(sK2) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_1685]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14099,plain,
% 7.15/1.50      ( v1_relat_1(X0) != iProver_top
% 7.15/1.50      | r1_tarski(sK2,X0) != iProver_top
% 7.15/1.50      | k5_relat_1(sK2,k6_relat_1(k2_relat_1(X0))) = sK2 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_14094,c_33,c_1686]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14100,plain,
% 7.15/1.50      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(X0))) = sK2
% 7.15/1.50      | r1_tarski(sK2,X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_14099]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14108,plain,
% 7.15/1.50      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(k2_zfmisc_1(sK0,sK1)))) = sK2
% 7.15/1.50      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2039,c_14100]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6636,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6637,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_6636]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14199,plain,
% 7.15/1.50      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(k2_zfmisc_1(sK0,sK1)))) = sK2 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_14108,c_6637]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14202,plain,
% 7.15/1.50      ( k5_relat_1(sK2,k6_relat_1(sK1)) = sK2
% 7.15/1.50      | sK1 = k1_xboole_0
% 7.15/1.50      | sK0 = k1_xboole_0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_10,c_14199]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_29,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.15/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1478,plain,
% 7.15/1.50      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.15/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5799,plain,
% 7.15/1.50      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1476,c_1478]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_30,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 7.15/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1477,plain,
% 7.15/1.50      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 7.15/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5132,plain,
% 7.15/1.50      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1476,c_1477]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_27,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1480,plain,
% 7.15/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.15/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4387,plain,
% 7.15/1.50      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1476,c_1480]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_28,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1479,plain,
% 7.15/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.15/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3994,plain,
% 7.15/1.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1476,c_1479]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_31,negated_conjecture,
% 7.15/1.50      ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
% 7.15/1.50      | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4019,plain,
% 7.15/1.50      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
% 7.15/1.50      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3994,c_31]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4498,plain,
% 7.15/1.50      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
% 7.15/1.50      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_4387,c_4019]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5212,plain,
% 7.15/1.50      ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
% 7.15/1.50      | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_5132,c_4498]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5991,plain,
% 7.15/1.50      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
% 7.15/1.50      | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_5799,c_5212]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3235,plain,
% 7.15/1.50      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1864,c_3001]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5992,plain,
% 7.15/1.50      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
% 7.15/1.50      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_5991,c_3235]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5993,plain,
% 7.15/1.50      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
% 7.15/1.50      inference(equality_resolution_simp,[status(thm)],[c_5992]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14205,plain,
% 7.15/1.50      ( k10_relat_1(sK2,k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k1_relat_1(sK2) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_14199,c_7466]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14221,plain,
% 7.15/1.50      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2)
% 7.15/1.50      | sK1 = k1_xboole_0
% 7.15/1.50      | sK0 = k1_xboole_0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_10,c_14205]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14270,plain,
% 7.15/1.50      ( sK1 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_14202,c_5993,c_14221]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14274,plain,
% 7.15/1.50      ( k10_relat_1(sK2,k2_relat_1(k2_zfmisc_1(sK0,k1_xboole_0))) = k1_relat_1(sK2)
% 7.15/1.50      | sK0 = k1_xboole_0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_14270,c_14205]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15,plain,
% 7.15/1.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14332,plain,
% 7.15/1.50      ( k10_relat_1(sK2,k1_xboole_0) = k1_relat_1(sK2) | sK0 = k1_xboole_0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_14274,c_1,c_15]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14278,plain,
% 7.15/1.50      ( k10_relat_1(sK2,k1_xboole_0) != k1_relat_1(sK2) | sK0 = k1_xboole_0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_14270,c_5993]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14334,plain,
% 7.15/1.50      ( sK0 = k1_xboole_0 ),
% 7.15/1.50      inference(backward_subsumption_resolution,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_14332,c_14278]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14355,plain,
% 7.15/1.50      ( k7_relat_1(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,X0)
% 7.15/1.50      | sK2 = k1_xboole_0
% 7.15/1.50      | k1_xboole_0 = X0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2039,c_14344]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_16523,plain,
% 7.15/1.50      ( k7_relat_1(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(k1_xboole_0,sK1)) = k2_zfmisc_1(sK2,X0)
% 7.15/1.50      | sK2 = k1_xboole_0
% 7.15/1.50      | k1_xboole_0 = X0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_14334,c_14355]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2,plain,
% 7.15/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_16569,plain,
% 7.15/1.50      ( k7_relat_1(k2_zfmisc_1(sK2,X0),k1_xboole_0) = k2_zfmisc_1(sK2,X0)
% 7.15/1.50      | sK2 = k1_xboole_0
% 7.15/1.50      | k1_xboole_0 = X0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_16523,c_2]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_17,plain,
% 7.15/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1487,plain,
% 7.15/1.50      ( k2_relat_1(X0) != k1_xboole_0
% 7.15/1.50      | k1_xboole_0 = X0
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3780,plain,
% 7.15/1.50      ( k9_relat_1(sK2,X0) != k1_xboole_0
% 7.15/1.50      | k7_relat_1(sK2,X0) = k1_xboole_0
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3001,c_1487]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4089,plain,
% 7.15/1.50      ( k7_relat_1(sK2,sK0) = k1_xboole_0
% 7.15/1.50      | k2_relat_1(sK2) != k1_xboole_0
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3235,c_3780]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4090,plain,
% 7.15/1.50      ( k7_relat_1(sK2,sK0) = k1_xboole_0
% 7.15/1.50      | k2_relat_1(sK2) != k1_xboole_0
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_4089,c_1864]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4091,plain,
% 7.15/1.50      ( k2_relat_1(sK2) != k1_xboole_0
% 7.15/1.50      | sK2 = k1_xboole_0
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_4090,c_1864]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4148,plain,
% 7.15/1.50      ( sK2 = k1_xboole_0 | k2_relat_1(sK2) != k1_xboole_0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_4091,c_33,c_1686]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4149,plain,
% 7.15/1.50      ( k2_relat_1(sK2) != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_4148]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5905,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 7.15/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.15/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_20,c_1483]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7120,plain,
% 7.15/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.15/1.50      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 7.15/1.50      inference(global_propositional_subsumption,[status(thm)],[c_5905,c_52]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7121,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 7.15/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_7120]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12787,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k9_relat_1(sK2,X0)),k2_relat_1(X1)) = k6_relat_1(k9_relat_1(sK2,X0))
% 7.15/1.50      | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
% 7.15/1.50      | v1_relat_1(X1) != iProver_top
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_12091,c_7121]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15634,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k9_relat_1(sK2,sK0)),k2_relat_1(X0)) = k6_relat_1(k9_relat_1(sK2,sK0))
% 7.15/1.50      | r1_tarski(sK2,X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1864,c_12787]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15635,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(X0)) = k6_relat_1(k2_relat_1(sK2))
% 7.15/1.50      | r1_tarski(sK2,X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_15634,c_1864,c_3235]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15640,plain,
% 7.15/1.50      ( v1_relat_1(X0) != iProver_top
% 7.15/1.50      | r1_tarski(sK2,X0) != iProver_top
% 7.15/1.50      | k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(X0)) = k6_relat_1(k2_relat_1(sK2)) ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_15635,c_33,c_1686]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15641,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(X0)) = k6_relat_1(k2_relat_1(sK2))
% 7.15/1.50      | r1_tarski(sK2,X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_15640]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15649,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k6_relat_1(k2_relat_1(sK2))
% 7.15/1.50      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2039,c_15641]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15654,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k6_relat_1(k2_relat_1(sK2)) ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_15649,c_6637]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2999,plain,
% 7.15/1.50      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1482,c_1492]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15658,plain,
% 7.15/1.50      ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_15654,c_2999]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_19,plain,
% 7.15/1.50      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15660,plain,
% 7.15/1.50      ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(sK0,sK1))) = k2_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_15658,c_19]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_16517,plain,
% 7.15/1.50      ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(k1_xboole_0,sK1))) = k2_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_14334,c_15660]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_16518,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k2_relat_1(k2_zfmisc_1(k1_xboole_0,sK1))) = k6_relat_1(k2_relat_1(sK2)) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_14334,c_15654]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12097,plain,
% 7.15/1.50      ( r1_tarski(X0,k7_relat_1(sK2,X1)) != iProver_top
% 7.15/1.50      | r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1)) = iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3001,c_1489]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12886,plain,
% 7.15/1.50      ( k5_relat_1(X0,k6_relat_1(k9_relat_1(sK2,X1))) = X0
% 7.15/1.50      | r1_tarski(X0,k7_relat_1(sK2,X1)) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_12097,c_1485]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13381,plain,
% 7.15/1.50      ( k5_relat_1(X0,k6_relat_1(k9_relat_1(sK2,sK0))) = X0
% 7.15/1.50      | r1_tarski(X0,sK2) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1864,c_12886]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13386,plain,
% 7.15/1.50      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(sK2))) = X0
% 7.15/1.50      | r1_tarski(X0,sK2) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_13381,c_1864,c_3235]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13425,plain,
% 7.15/1.50      ( v1_relat_1(X0) != iProver_top
% 7.15/1.50      | r1_tarski(X0,sK2) != iProver_top
% 7.15/1.50      | k5_relat_1(X0,k6_relat_1(k2_relat_1(sK2))) = X0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_13386,c_33,c_1686]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13426,plain,
% 7.15/1.50      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(sK2))) = X0
% 7.15/1.50      | r1_tarski(X0,sK2) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_13425]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13434,plain,
% 7.15/1.50      ( k5_relat_1(k1_xboole_0,k6_relat_1(k2_relat_1(sK2))) = k1_xboole_0
% 7.15/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1496,c_13426]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2363,plain,
% 7.15/1.50      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1482,c_1484]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4158,plain,
% 7.15/1.50      ( k5_relat_1(k1_xboole_0,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),k1_xboole_0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3920,c_2363]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13451,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k1_xboole_0) = k1_xboole_0
% 7.15/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_13434,c_4158]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_49,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_51,plain,
% 7.15/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.15/1.50      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_49]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1680,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1681,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.15/1.50      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_1680]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1683,plain,
% 7.15/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 7.15/1.50      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1681]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1894,plain,
% 7.15/1.50      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1897,plain,
% 7.15/1.50      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1899,plain,
% 7.15/1.50      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1897]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13998,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_13451,c_51,c_1683,c_1899]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_16598,plain,
% 7.15/1.50      ( k6_relat_1(k2_relat_1(sK2)) = k1_xboole_0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_16518,c_2,c_15,c_13998]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_16600,plain,
% 7.15/1.50      ( k9_relat_1(k1_xboole_0,k2_relat_1(k2_zfmisc_1(k1_xboole_0,sK1))) = k2_relat_1(sK2) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_16517,c_16598]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3000,plain,
% 7.15/1.50      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2027,c_1492]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3005,plain,
% 7.15/1.50      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_3000,c_15,c_2821]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_16602,plain,
% 7.15/1.50      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_16600,c_3005]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_19020,plain,
% 7.15/1.50      ( sK2 = k1_xboole_0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_16569,c_4149,c_16602]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_25965,plain,
% 7.15/1.50      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 7.15/1.50      | k7_relat_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,X0),X1),k1_xboole_0) = k2_zfmisc_1(k10_relat_1(k1_xboole_0,X0),X1)
% 7.15/1.50      | k1_xboole_0 = X1
% 7.15/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.15/1.50      inference(light_normalisation,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_14369,c_16,c_3920,c_4157,c_19020]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_25970,plain,
% 7.15/1.50      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 7.15/1.50      | k7_relat_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,X0),X1),k1_xboole_0) = k2_zfmisc_1(k10_relat_1(k1_xboole_0,X0),X1)
% 7.15/1.50      | k1_xboole_0 = X1 ),
% 7.15/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_25965,c_2027]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2460,plain,
% 7.15/1.50      ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 7.15/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_16,c_1491]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2978,plain,
% 7.15/1.50      ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_2460,c_51,c_1683,c_1899]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2228,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1,c_1481]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2357,plain,
% 7.15/1.50      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1495,c_2228]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2986,plain,
% 7.15/1.50      ( v1_relat_1(k10_relat_1(k1_xboole_0,X0)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2978,c_2357]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_19063,plain,
% 7.15/1.50      ( k5_relat_1(k1_xboole_0,k6_relat_1(k2_relat_1(X0))) = k1_xboole_0
% 7.15/1.50      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_19020,c_14100]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_19308,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(X0)),k1_xboole_0) = k1_xboole_0
% 7.15/1.50      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_19063,c_4158]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_103,plain,
% 7.15/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_22787,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(X0)),k1_xboole_0) = k1_xboole_0
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,[status(thm)],[c_19308,c_103]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_22796,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1482,c_22787]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_22812,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_22796,c_19]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_23304,plain,
% 7.15/1.50      ( k9_relat_1(k6_relat_1(X0),k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_22812,c_2999]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_23307,plain,
% 7.15/1.50      ( k9_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_23304,c_15]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7454,plain,
% 7.15/1.50      ( k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))) = k10_relat_1(sK2,k1_relat_1(k10_relat_1(k1_xboole_0,X0))) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2986,c_6774]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7842,plain,
% 7.15/1.50      ( r1_tarski(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))),k1_relat_1(sK2)) = iProver_top
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_7454,c_1491]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8761,plain,
% 7.15/1.50      ( r1_tarski(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))),k1_relat_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_7842,c_33,c_1686]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8768,plain,
% 7.15/1.50      ( k7_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0)))),k1_relat_1(sK2)) = k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0)))) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_8761,c_7121]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_10526,plain,
% 7.15/1.50      ( k9_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0)))),k1_relat_1(sK2)) = k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))))) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_8768,c_2999]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_10527,plain,
% 7.15/1.50      ( k9_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0)))),k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK2,k10_relat_1(k1_xboole_0,X0))) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_10526,c_19]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_19085,plain,
% 7.15/1.50      ( k9_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)))),k1_relat_1(k1_xboole_0)) = k1_relat_1(k5_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X0))) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_19020,c_10527]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3388,plain,
% 7.15/1.50      ( k5_relat_1(k6_relat_1(X0),k10_relat_1(k1_xboole_0,X1)) = k7_relat_1(k10_relat_1(k1_xboole_0,X1),X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2986,c_1484]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2985,plain,
% 7.15/1.50      ( k7_relat_1(k10_relat_1(k1_xboole_0,X0),X1) = k10_relat_1(k1_xboole_0,X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2978,c_2219]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3713,plain,
% 7.15/1.50      ( k5_relat_1(k6_relat_1(X0),k10_relat_1(k1_xboole_0,X1)) = k10_relat_1(k1_xboole_0,X1) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3388,c_2985]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4154,plain,
% 7.15/1.50      ( k5_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)) = k10_relat_1(k1_xboole_0,X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3920,c_3713]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_19193,plain,
% 7.15/1.50      ( k9_relat_1(k6_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X0))),k1_xboole_0) = k1_relat_1(k10_relat_1(k1_xboole_0,X0)) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_19085,c_16,c_4154]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_23312,plain,
% 7.15/1.50      ( k1_relat_1(k10_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_23307,c_19193]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_24270,plain,
% 7.15/1.50      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 7.15/1.50      | v1_relat_1(k10_relat_1(k1_xboole_0,X0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_23312,c_1486]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_25971,plain,
% 7.15/1.50      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_25970,c_2986,c_24270]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_19109,plain,
% 7.15/1.50      ( k10_relat_1(k1_xboole_0,sK1) != k1_relat_1(k1_xboole_0) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_19020,c_5993]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_19116,plain,
% 7.15/1.50      ( k10_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_19109,c_16]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_25987,plain,
% 7.15/1.50      ( k1_xboole_0 != k1_xboole_0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_25971,c_19116]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_25988,plain,
% 7.15/1.50      ( $false ),
% 7.15/1.50      inference(equality_resolution_simp,[status(thm)],[c_25987]) ).
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  ------                               Statistics
% 7.15/1.50  
% 7.15/1.50  ------ General
% 7.15/1.50  
% 7.15/1.50  abstr_ref_over_cycles:                  0
% 7.15/1.50  abstr_ref_under_cycles:                 0
% 7.15/1.50  gc_basic_clause_elim:                   0
% 7.15/1.50  forced_gc_time:                         0
% 7.15/1.50  parsing_time:                           0.01
% 7.15/1.50  unif_index_cands_time:                  0.
% 7.15/1.50  unif_index_add_time:                    0.
% 7.15/1.50  orderings_time:                         0.
% 7.15/1.50  out_proof_time:                         0.018
% 7.15/1.50  total_time:                             0.719
% 7.15/1.50  num_of_symbols:                         52
% 7.15/1.50  num_of_terms:                           22611
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing
% 7.15/1.50  
% 7.15/1.50  num_of_splits:                          0
% 7.15/1.50  num_of_split_atoms:                     0
% 7.15/1.50  num_of_reused_defs:                     0
% 7.15/1.50  num_eq_ax_congr_red:                    20
% 7.15/1.50  num_of_sem_filtered_clauses:            1
% 7.15/1.50  num_of_subtypes:                        0
% 7.15/1.50  monotx_restored_types:                  0
% 7.15/1.50  sat_num_of_epr_types:                   0
% 7.15/1.50  sat_num_of_non_cyclic_types:            0
% 7.15/1.50  sat_guarded_non_collapsed_types:        0
% 7.15/1.50  num_pure_diseq_elim:                    0
% 7.15/1.50  simp_replaced_by:                       0
% 7.15/1.50  res_preprocessed:                       160
% 7.15/1.50  prep_upred:                             0
% 7.15/1.50  prep_unflattend:                        26
% 7.15/1.50  smt_new_axioms:                         0
% 7.15/1.50  pred_elim_cands:                        3
% 7.15/1.50  pred_elim:                              1
% 7.15/1.50  pred_elim_cl:                           1
% 7.15/1.50  pred_elim_cycles:                       3
% 7.15/1.50  merged_defs:                            8
% 7.15/1.50  merged_defs_ncl:                        0
% 7.15/1.50  bin_hyper_res:                          8
% 7.15/1.50  prep_cycles:                            4
% 7.15/1.50  pred_elim_time:                         0.005
% 7.15/1.50  splitting_time:                         0.
% 7.15/1.50  sem_filter_time:                        0.
% 7.15/1.50  monotx_time:                            0.
% 7.15/1.50  subtype_inf_time:                       0.
% 7.15/1.50  
% 7.15/1.50  ------ Problem properties
% 7.15/1.50  
% 7.15/1.50  clauses:                                32
% 7.15/1.50  conjectures:                            2
% 7.15/1.50  epr:                                    1
% 7.15/1.50  horn:                                   29
% 7.15/1.50  ground:                                 4
% 7.15/1.50  unary:                                  10
% 7.15/1.50  binary:                                 12
% 7.15/1.50  lits:                                   66
% 7.15/1.50  lits_eq:                                31
% 7.15/1.50  fd_pure:                                0
% 7.15/1.50  fd_pseudo:                              0
% 7.15/1.50  fd_cond:                                3
% 7.15/1.50  fd_pseudo_cond:                         0
% 7.15/1.50  ac_symbols:                             0
% 7.15/1.50  
% 7.15/1.50  ------ Propositional Solver
% 7.15/1.50  
% 7.15/1.50  prop_solver_calls:                      31
% 7.15/1.50  prop_fast_solver_calls:                 1930
% 7.15/1.50  smt_solver_calls:                       0
% 7.15/1.50  smt_fast_solver_calls:                  0
% 7.15/1.50  prop_num_of_clauses:                    9170
% 7.15/1.50  prop_preprocess_simplified:             15590
% 7.15/1.50  prop_fo_subsumed:                       95
% 7.15/1.50  prop_solver_time:                       0.
% 7.15/1.50  smt_solver_time:                        0.
% 7.15/1.50  smt_fast_solver_time:                   0.
% 7.15/1.50  prop_fast_solver_time:                  0.
% 7.15/1.50  prop_unsat_core_time:                   0.
% 7.15/1.50  
% 7.15/1.50  ------ QBF
% 7.15/1.50  
% 7.15/1.50  qbf_q_res:                              0
% 7.15/1.50  qbf_num_tautologies:                    0
% 7.15/1.50  qbf_prep_cycles:                        0
% 7.15/1.50  
% 7.15/1.50  ------ BMC1
% 7.15/1.50  
% 7.15/1.50  bmc1_current_bound:                     -1
% 7.15/1.50  bmc1_last_solved_bound:                 -1
% 7.15/1.50  bmc1_unsat_core_size:                   -1
% 7.15/1.50  bmc1_unsat_core_parents_size:           -1
% 7.15/1.50  bmc1_merge_next_fun:                    0
% 7.15/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.15/1.50  
% 7.15/1.50  ------ Instantiation
% 7.15/1.50  
% 7.15/1.50  inst_num_of_clauses:                    3088
% 7.15/1.50  inst_num_in_passive:                    530
% 7.15/1.50  inst_num_in_active:                     1145
% 7.15/1.50  inst_num_in_unprocessed:                1414
% 7.15/1.50  inst_num_of_loops:                      1460
% 7.15/1.50  inst_num_of_learning_restarts:          0
% 7.15/1.50  inst_num_moves_active_passive:          311
% 7.15/1.50  inst_lit_activity:                      0
% 7.15/1.50  inst_lit_activity_moves:                0
% 7.15/1.50  inst_num_tautologies:                   0
% 7.15/1.50  inst_num_prop_implied:                  0
% 7.15/1.50  inst_num_existing_simplified:           0
% 7.15/1.50  inst_num_eq_res_simplified:             0
% 7.15/1.50  inst_num_child_elim:                    0
% 7.15/1.50  inst_num_of_dismatching_blockings:      834
% 7.15/1.50  inst_num_of_non_proper_insts:           2248
% 7.15/1.50  inst_num_of_duplicates:                 0
% 7.15/1.50  inst_inst_num_from_inst_to_res:         0
% 7.15/1.50  inst_dismatching_checking_time:         0.
% 7.15/1.50  
% 7.15/1.50  ------ Resolution
% 7.15/1.50  
% 7.15/1.50  res_num_of_clauses:                     0
% 7.15/1.50  res_num_in_passive:                     0
% 7.15/1.50  res_num_in_active:                      0
% 7.15/1.50  res_num_of_loops:                       164
% 7.15/1.50  res_forward_subset_subsumed:            186
% 7.15/1.50  res_backward_subset_subsumed:           4
% 7.15/1.50  res_forward_subsumed:                   0
% 7.15/1.50  res_backward_subsumed:                  0
% 7.15/1.50  res_forward_subsumption_resolution:     0
% 7.15/1.50  res_backward_subsumption_resolution:    0
% 7.15/1.50  res_clause_to_clause_subsumption:       2027
% 7.15/1.50  res_orphan_elimination:                 0
% 7.15/1.50  res_tautology_del:                      168
% 7.15/1.50  res_num_eq_res_simplified:              0
% 7.15/1.50  res_num_sel_changes:                    0
% 7.15/1.50  res_moves_from_active_to_pass:          0
% 7.15/1.50  
% 7.15/1.50  ------ Superposition
% 7.15/1.50  
% 7.15/1.50  sup_time_total:                         0.
% 7.15/1.50  sup_time_generating:                    0.
% 7.15/1.50  sup_time_sim_full:                      0.
% 7.15/1.50  sup_time_sim_immed:                     0.
% 7.15/1.50  
% 7.15/1.50  sup_num_of_clauses:                     542
% 7.15/1.50  sup_num_in_active:                      134
% 7.15/1.50  sup_num_in_passive:                     408
% 7.15/1.50  sup_num_of_loops:                       291
% 7.15/1.50  sup_fw_superposition:                   591
% 7.15/1.50  sup_bw_superposition:                   434
% 7.15/1.50  sup_immediate_simplified:               445
% 7.15/1.50  sup_given_eliminated:                   2
% 7.15/1.50  comparisons_done:                       0
% 7.15/1.50  comparisons_avoided:                    99
% 7.15/1.50  
% 7.15/1.50  ------ Simplifications
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  sim_fw_subset_subsumed:                 77
% 7.15/1.50  sim_bw_subset_subsumed:                 12
% 7.15/1.50  sim_fw_subsumed:                        103
% 7.15/1.50  sim_bw_subsumed:                        13
% 7.15/1.50  sim_fw_subsumption_res:                 27
% 7.15/1.50  sim_bw_subsumption_res:                 1
% 7.15/1.50  sim_tautology_del:                      16
% 7.15/1.50  sim_eq_tautology_del:                   160
% 7.15/1.50  sim_eq_res_simp:                        3
% 7.15/1.50  sim_fw_demodulated:                     160
% 7.15/1.50  sim_bw_demodulated:                     157
% 7.15/1.50  sim_light_normalised:                   367
% 7.15/1.50  sim_joinable_taut:                      0
% 7.15/1.50  sim_joinable_simp:                      0
% 7.15/1.50  sim_ac_normalised:                      0
% 7.15/1.50  sim_smt_subsumption:                    0
% 7.15/1.50  
%------------------------------------------------------------------------------
