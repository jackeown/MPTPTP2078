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
% DateTime   : Thu Dec  3 12:07:39 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  191 (1456 expanded)
%              Number of clauses        :  117 ( 455 expanded)
%              Number of leaves         :   18 ( 285 expanded)
%              Depth                    :   25
%              Number of atoms          :  612 (7440 expanded)
%              Number of equality atoms :  268 (2108 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
        | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46])).

fof(f77,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1160,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1161,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3061,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1161])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1472,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1474,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_3296,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3061,c_30,c_29,c_28,c_27,c_1474])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1165,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3766,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3296,c_1165])).

cnf(c_31,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_32,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_33,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4314,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3766,c_31,c_32,c_33,c_34])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_7])).

cnf(c_1155,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_4324,plain,
    ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4314,c_1155])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_94,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_96,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4319,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4314,c_1175])).

cnf(c_4572,plain,
    ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4324,c_96,c_4319])).

cnf(c_4479,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4319,c_96])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1173,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4484,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_4479,c_1173])).

cnf(c_4886,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4572,c_4484])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1166,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2492,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1166])).

cnf(c_1423,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1424,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1423])).

cnf(c_1426,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_2653,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2492,c_31,c_33,c_34,c_1426])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1176,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1169,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3069,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1169])).

cnf(c_4078,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2653,c_3069])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_387,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_388,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_404,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_388,c_11])).

cnf(c_1154,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_1540,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1154])).

cnf(c_95,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1541,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1540])).

cnf(c_1380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1600,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_1953,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1540,c_30,c_28,c_27,c_95,c_1541,c_1600])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1171,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2400,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1953,c_1171])).

cnf(c_1601,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1600])).

cnf(c_2922,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2400,c_31,c_34,c_96,c_1601])).

cnf(c_2930,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1176,c_2922])).

cnf(c_1827,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1175])).

cnf(c_1940,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1827,c_34,c_96,c_1601])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1172,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1946,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1940,c_1172])).

cnf(c_1985,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1946,c_1953])).

cnf(c_2935,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2930,c_1985])).

cnf(c_4079,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4078,c_2935])).

cnf(c_4576,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4079,c_31,c_34,c_96,c_1601])).

cnf(c_4897,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4886,c_4576])).

cnf(c_4322,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4314,c_1154])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1162,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3199,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1162])).

cnf(c_1457,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1458,plain,
    ( v1_funct_2(sK2,X0,X0) != iProver_top
    | v3_funct_2(sK2,X0,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(k2_funct_2(X0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_1460,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_3350,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3199,c_31,c_32,c_33,c_34,c_1460])).

cnf(c_3354,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3350,c_3296])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1164,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3293,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1164])).

cnf(c_1482,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | v3_funct_2(k2_funct_2(X0,sK2),X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1483,plain,
    ( v1_funct_2(sK2,X0,X0) != iProver_top
    | v3_funct_2(k2_funct_2(X0,sK2),X0,X0) = iProver_top
    | v3_funct_2(sK2,X0,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

cnf(c_1485,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_3526,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3293,c_31,c_32,c_33,c_34,c_1485])).

cnf(c_3530,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3526,c_3296])).

cnf(c_5221,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4322,c_96,c_3354,c_3530,c_4319])).

cnf(c_5659,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_4897,c_5221])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1170,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5669,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5659,c_1170])).

cnf(c_5971,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5669,c_31,c_33,c_34,c_96,c_1426,c_1601])).

cnf(c_5972,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5971])).

cnf(c_5980,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1160,c_5972])).

cnf(c_2931,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1160,c_2922])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1167,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2211,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1159,c_1167])).

cnf(c_25,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2563,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2211,c_25])).

cnf(c_2564,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2563,c_2211])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1168,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2391,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1159,c_1168])).

cnf(c_2733,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2564,c_2391])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5980,c_2931,c_2733])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.16/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/1.00  
% 3.16/1.00  ------  iProver source info
% 3.16/1.00  
% 3.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/1.00  git: non_committed_changes: false
% 3.16/1.00  git: last_make_outside_of_git: false
% 3.16/1.00  
% 3.16/1.00  ------ 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options
% 3.16/1.00  
% 3.16/1.00  --out_options                           all
% 3.16/1.00  --tptp_safe_out                         true
% 3.16/1.00  --problem_path                          ""
% 3.16/1.00  --include_path                          ""
% 3.16/1.00  --clausifier                            res/vclausify_rel
% 3.16/1.00  --clausifier_options                    --mode clausify
% 3.16/1.00  --stdin                                 false
% 3.16/1.00  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     num_symb
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       true
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  ------ Parsing...
% 3.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/1.00  ------ Proving...
% 3.16/1.00  ------ Problem Properties 
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  clauses                                 25
% 3.16/1.00  conjectures                             6
% 3.16/1.00  EPR                                     6
% 3.16/1.00  Horn                                    25
% 3.16/1.00  unary                                   7
% 3.16/1.00  binary                                  5
% 3.16/1.00  lits                                    74
% 3.16/1.00  lits eq                                 13
% 3.16/1.00  fd_pure                                 0
% 3.16/1.00  fd_pseudo                               0
% 3.16/1.00  fd_cond                                 0
% 3.16/1.00  fd_pseudo_cond                          2
% 3.16/1.00  AC symbols                              0
% 3.16/1.00  
% 3.16/1.00  ------ Schedule dynamic 5 is on 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ 
% 3.16/1.00  Current options:
% 3.16/1.00  ------ 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options
% 3.16/1.00  
% 3.16/1.00  --out_options                           all
% 3.16/1.00  --tptp_safe_out                         true
% 3.16/1.00  --problem_path                          ""
% 3.16/1.00  --include_path                          ""
% 3.16/1.00  --clausifier                            res/vclausify_rel
% 3.16/1.00  --clausifier_options                    --mode clausify
% 3.16/1.00  --stdin                                 false
% 3.16/1.00  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     none
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       false
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ Proving...
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS status Theorem for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  fof(f17,conjecture,(
% 3.16/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f18,negated_conjecture,(
% 3.16/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.16/1.00    inference(negated_conjecture,[],[f17])).
% 3.16/1.00  
% 3.16/1.00  fof(f41,plain,(
% 3.16/1.00    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 3.16/1.00    inference(ennf_transformation,[],[f18])).
% 3.16/1.00  
% 3.16/1.00  fof(f42,plain,(
% 3.16/1.00    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 3.16/1.00    inference(flattening,[],[f41])).
% 3.16/1.00  
% 3.16/1.00  fof(f46,plain,(
% 3.16/1.00    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f47,plain,(
% 3.16/1.00    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46])).
% 3.16/1.00  
% 3.16/1.00  fof(f77,plain,(
% 3.16/1.00    r1_tarski(sK1,sK0)),
% 3.16/1.00    inference(cnf_transformation,[],[f47])).
% 3.16/1.00  
% 3.16/1.00  fof(f76,plain,(
% 3.16/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.16/1.00    inference(cnf_transformation,[],[f47])).
% 3.16/1.00  
% 3.16/1.00  fof(f16,axiom,(
% 3.16/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f39,plain,(
% 3.16/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f16])).
% 3.16/1.00  
% 3.16/1.00  fof(f40,plain,(
% 3.16/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.16/1.00    inference(flattening,[],[f39])).
% 3.16/1.00  
% 3.16/1.00  fof(f72,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f73,plain,(
% 3.16/1.00    v1_funct_1(sK2)),
% 3.16/1.00    inference(cnf_transformation,[],[f47])).
% 3.16/1.00  
% 3.16/1.00  fof(f74,plain,(
% 3.16/1.00    v1_funct_2(sK2,sK0,sK0)),
% 3.16/1.00    inference(cnf_transformation,[],[f47])).
% 3.16/1.00  
% 3.16/1.00  fof(f75,plain,(
% 3.16/1.00    v3_funct_2(sK2,sK0,sK0)),
% 3.16/1.00    inference(cnf_transformation,[],[f47])).
% 3.16/1.00  
% 3.16/1.00  fof(f15,axiom,(
% 3.16/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f37,plain,(
% 3.16/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f15])).
% 3.16/1.00  
% 3.16/1.00  fof(f38,plain,(
% 3.16/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.16/1.00    inference(flattening,[],[f37])).
% 3.16/1.00  
% 3.16/1.00  fof(f71,plain,(
% 3.16/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f38])).
% 3.16/1.00  
% 3.16/1.00  fof(f10,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f30,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f10])).
% 3.16/1.00  
% 3.16/1.00  fof(f59,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f30])).
% 3.16/1.00  
% 3.16/1.00  fof(f6,axiom,(
% 3.16/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f22,plain,(
% 3.16/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f6])).
% 3.16/1.00  
% 3.16/1.00  fof(f23,plain,(
% 3.16/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f22])).
% 3.16/1.00  
% 3.16/1.00  fof(f55,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f23])).
% 3.16/1.00  
% 3.16/1.00  fof(f3,axiom,(
% 3.16/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f52,plain,(
% 3.16/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f3])).
% 3.16/1.00  
% 3.16/1.00  fof(f2,axiom,(
% 3.16/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f19,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.16/1.00    inference(ennf_transformation,[],[f2])).
% 3.16/1.00  
% 3.16/1.00  fof(f51,plain,(
% 3.16/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f19])).
% 3.16/1.00  
% 3.16/1.00  fof(f4,axiom,(
% 3.16/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f20,plain,(
% 3.16/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(ennf_transformation,[],[f4])).
% 3.16/1.00  
% 3.16/1.00  fof(f53,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f20])).
% 3.16/1.00  
% 3.16/1.00  fof(f13,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f33,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f13])).
% 3.16/1.00  
% 3.16/1.00  fof(f34,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(flattening,[],[f33])).
% 3.16/1.00  
% 3.16/1.00  fof(f64,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f34])).
% 3.16/1.00  
% 3.16/1.00  fof(f1,axiom,(
% 3.16/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f43,plain,(
% 3.16/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/1.00    inference(nnf_transformation,[],[f1])).
% 3.16/1.00  
% 3.16/1.00  fof(f44,plain,(
% 3.16/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/1.00    inference(flattening,[],[f43])).
% 3.16/1.00  
% 3.16/1.00  fof(f48,plain,(
% 3.16/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.16/1.00    inference(cnf_transformation,[],[f44])).
% 3.16/1.00  
% 3.16/1.00  fof(f80,plain,(
% 3.16/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.16/1.00    inference(equality_resolution,[],[f48])).
% 3.16/1.00  
% 3.16/1.00  fof(f9,axiom,(
% 3.16/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f28,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.16/1.00    inference(ennf_transformation,[],[f9])).
% 3.16/1.00  
% 3.16/1.00  fof(f29,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.16/1.00    inference(flattening,[],[f28])).
% 3.16/1.00  
% 3.16/1.00  fof(f58,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f29])).
% 3.16/1.00  
% 3.16/1.00  fof(f65,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f34])).
% 3.16/1.00  
% 3.16/1.00  fof(f14,axiom,(
% 3.16/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f35,plain,(
% 3.16/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f14])).
% 3.16/1.00  
% 3.16/1.00  fof(f36,plain,(
% 3.16/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f35])).
% 3.16/1.00  
% 3.16/1.00  fof(f45,plain,(
% 3.16/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(nnf_transformation,[],[f36])).
% 3.16/1.00  
% 3.16/1.00  fof(f66,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f45])).
% 3.16/1.00  
% 3.16/1.00  fof(f60,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f30])).
% 3.16/1.00  
% 3.16/1.00  fof(f7,axiom,(
% 3.16/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f24,plain,(
% 3.16/1.00    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f7])).
% 3.16/1.00  
% 3.16/1.00  fof(f25,plain,(
% 3.16/1.00    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f24])).
% 3.16/1.00  
% 3.16/1.00  fof(f56,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f25])).
% 3.16/1.00  
% 3.16/1.00  fof(f5,axiom,(
% 3.16/1.00    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f21,plain,(
% 3.16/1.00    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.16/1.00    inference(ennf_transformation,[],[f5])).
% 3.16/1.00  
% 3.16/1.00  fof(f54,plain,(
% 3.16/1.00    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f21])).
% 3.16/1.00  
% 3.16/1.00  fof(f68,plain,(
% 3.16/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f38])).
% 3.16/1.00  
% 3.16/1.00  fof(f70,plain,(
% 3.16/1.00    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f38])).
% 3.16/1.00  
% 3.16/1.00  fof(f8,axiom,(
% 3.16/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f26,plain,(
% 3.16/1.00    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f8])).
% 3.16/1.00  
% 3.16/1.00  fof(f27,plain,(
% 3.16/1.00    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f26])).
% 3.16/1.00  
% 3.16/1.00  fof(f57,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f27])).
% 3.16/1.00  
% 3.16/1.00  fof(f12,axiom,(
% 3.16/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f32,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f12])).
% 3.16/1.00  
% 3.16/1.00  fof(f62,plain,(
% 3.16/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f32])).
% 3.16/1.00  
% 3.16/1.00  fof(f78,plain,(
% 3.16/1.00    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 3.16/1.00    inference(cnf_transformation,[],[f47])).
% 3.16/1.00  
% 3.16/1.00  fof(f11,axiom,(
% 3.16/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f31,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f11])).
% 3.16/1.00  
% 3.16/1.00  fof(f61,plain,(
% 3.16/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f31])).
% 3.16/1.00  
% 3.16/1.00  cnf(c_26,negated_conjecture,
% 3.16/1.00      ( r1_tarski(sK1,sK0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1160,plain,
% 3.16/1.00      ( r1_tarski(sK1,sK0) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_27,negated_conjecture,
% 3.16/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.16/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1159,plain,
% 3.16/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_24,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.16/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.00      | ~ v1_funct_1(X0)
% 3.16/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1161,plain,
% 3.16/1.00      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.16/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.16/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.16/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.16/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3061,plain,
% 3.16/1.00      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
% 3.16/1.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1159,c_1161]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_30,negated_conjecture,
% 3.16/1.00      ( v1_funct_1(sK2) ),
% 3.16/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_29,negated_conjecture,
% 3.16/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_28,negated_conjecture,
% 3.16/1.00      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1472,plain,
% 3.16/1.00      ( ~ v1_funct_2(sK2,X0,X0)
% 3.16/1.00      | ~ v3_funct_2(sK2,X0,X0)
% 3.16/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.16/1.00      | ~ v1_funct_1(sK2)
% 3.16/1.00      | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1474,plain,
% 3.16/1.00      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.16/1.00      | ~ v3_funct_2(sK2,sK0,sK0)
% 3.16/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.16/1.00      | ~ v1_funct_1(sK2)
% 3.16/1.00      | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1472]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3296,plain,
% 3.16/1.00      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_3061,c_30,c_29,c_28,c_27,c_1474]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_20,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.16/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.00      | ~ v1_funct_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1165,plain,
% 3.16/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.16/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.16/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.16/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.16/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3766,plain,
% 3.16/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.16/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3296,c_1165]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_31,plain,
% 3.16/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_32,plain,
% 3.16/1.00      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_33,plain,
% 3.16/1.00      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_34,plain,
% 3.16/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4314,plain,
% 3.16/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_3766,c_31,c_32,c_33,c_34]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_12,plain,
% 3.16/1.00      ( v4_relat_1(X0,X1)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.16/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_7,plain,
% 3.16/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_330,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | ~ v1_relat_1(X0)
% 3.16/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.16/1.00      inference(resolution,[status(thm)],[c_12,c_7]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1155,plain,
% 3.16/1.00      ( k7_relat_1(X0,X1) = X0
% 3.16/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4324,plain,
% 3.16/1.00      ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2)
% 3.16/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_4314,c_1155]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_94,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_96,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_94]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | v1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1175,plain,
% 3.16/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.16/1.00      | v1_relat_1(X1) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4319,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.16/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_4314,c_1175]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4572,plain,
% 3.16/1.00      ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2) ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_4324,c_96,c_4319]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4479,plain,
% 3.16/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_4319,c_96]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5,plain,
% 3.16/1.00      ( ~ v1_relat_1(X0)
% 3.16/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1173,plain,
% 3.16/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4484,plain,
% 3.16/1.00      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_4479,c_1173]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4886,plain,
% 3.16/1.00      ( k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_4572,c_4484]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_16,plain,
% 3.16/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | v2_funct_1(X0)
% 3.16/1.00      | ~ v1_funct_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1166,plain,
% 3.16/1.00      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.16/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.16/1.00      | v2_funct_1(X0) = iProver_top
% 3.16/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2492,plain,
% 3.16/1.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v2_funct_1(sK2) = iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1159,c_1166]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1423,plain,
% 3.16/1.00      ( ~ v3_funct_2(sK2,X0,X1)
% 3.16/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/1.00      | v2_funct_1(sK2)
% 3.16/1.00      | ~ v1_funct_1(sK2) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1424,plain,
% 3.16/1.00      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 3.16/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.16/1.00      | v2_funct_1(sK2) = iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1423]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1426,plain,
% 3.16/1.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.16/1.00      | v2_funct_1(sK2) = iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1424]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2653,plain,
% 3.16/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_2492,c_31,c_33,c_34,c_1426]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2,plain,
% 3.16/1.00      ( r1_tarski(X0,X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1176,plain,
% 3.16/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_10,plain,
% 3.16/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.16/1.00      | ~ v2_funct_1(X1)
% 3.16/1.00      | ~ v1_funct_1(X1)
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1169,plain,
% 3.16/1.00      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
% 3.16/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.16/1.00      | v2_funct_1(X0) != iProver_top
% 3.16/1.00      | v1_funct_1(X0) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3069,plain,
% 3.16/1.00      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
% 3.16/1.00      | v2_funct_1(X0) != iProver_top
% 3.16/1.00      | v1_funct_1(X0) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1176,c_1169]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4078,plain,
% 3.16/1.00      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top
% 3.16/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2653,c_3069]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_15,plain,
% 3.16/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.16/1.00      | v2_funct_2(X0,X2)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | ~ v1_funct_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_19,plain,
% 3.16/1.00      ( ~ v2_funct_2(X0,X1)
% 3.16/1.00      | ~ v5_relat_1(X0,X1)
% 3.16/1.00      | ~ v1_relat_1(X0)
% 3.16/1.00      | k2_relat_1(X0) = X1 ),
% 3.16/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_387,plain,
% 3.16/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.16/1.00      | ~ v5_relat_1(X3,X4)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | ~ v1_funct_1(X0)
% 3.16/1.00      | ~ v1_relat_1(X3)
% 3.16/1.00      | X3 != X0
% 3.16/1.00      | X4 != X2
% 3.16/1.00      | k2_relat_1(X3) = X4 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_388,plain,
% 3.16/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.16/1.00      | ~ v5_relat_1(X0,X2)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | ~ v1_funct_1(X0)
% 3.16/1.00      | ~ v1_relat_1(X0)
% 3.16/1.00      | k2_relat_1(X0) = X2 ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_387]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_11,plain,
% 3.16/1.00      ( v5_relat_1(X0,X1)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.16/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_404,plain,
% 3.16/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | ~ v1_funct_1(X0)
% 3.16/1.00      | ~ v1_relat_1(X0)
% 3.16/1.00      | k2_relat_1(X0) = X2 ),
% 3.16/1.00      inference(forward_subsumption_resolution,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_388,c_11]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1154,plain,
% 3.16/1.00      ( k2_relat_1(X0) = X1
% 3.16/1.00      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.16/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.16/1.00      | v1_funct_1(X0) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1540,plain,
% 3.16/1.00      ( k2_relat_1(sK2) = sK0
% 3.16/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top
% 3.16/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1159,c_1154]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_95,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1541,plain,
% 3.16/1.00      ( ~ v3_funct_2(sK2,sK0,sK0)
% 3.16/1.00      | ~ v1_funct_1(sK2)
% 3.16/1.00      | ~ v1_relat_1(sK2)
% 3.16/1.00      | k2_relat_1(sK2) = sK0 ),
% 3.16/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1540]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1380,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | v1_relat_1(X0)
% 3.16/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1600,plain,
% 3.16/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.16/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.16/1.00      | v1_relat_1(sK2) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1380]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1953,plain,
% 3.16/1.00      ( k2_relat_1(sK2) = sK0 ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_1540,c_30,c_28,c_27,c_95,c_1541,c_1600]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_8,plain,
% 3.16/1.00      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.16/1.00      | ~ v1_funct_1(X1)
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1171,plain,
% 3.16/1.00      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.16/1.00      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.16/1.00      | v1_funct_1(X0) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2400,plain,
% 3.16/1.00      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.16/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top
% 3.16/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1953,c_1171]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1601,plain,
% 3.16/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.16/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.16/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1600]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2922,plain,
% 3.16/1.00      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.16/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_2400,c_31,c_34,c_96,c_1601]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2930,plain,
% 3.16/1.00      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1176,c_2922]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1827,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.16/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1159,c_1175]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1940,plain,
% 3.16/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_1827,c_34,c_96,c_1601]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6,plain,
% 3.16/1.00      ( ~ v1_relat_1(X0)
% 3.16/1.00      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1172,plain,
% 3.16/1.00      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1946,plain,
% 3.16/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1940,c_1172]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1985,plain,
% 3.16/1.00      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_1946,c_1953]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2935,plain,
% 3.16/1.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_2930,c_1985]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4079,plain,
% 3.16/1.00      ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2)
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top
% 3.16/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_4078,c_2935]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4576,plain,
% 3.16/1.00      ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2) ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_4079,c_31,c_34,c_96,c_1601]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4897,plain,
% 3.16/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_4886,c_4576]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4322,plain,
% 3.16/1.00      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 3.16/1.00      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 3.16/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.16/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_4314,c_1154]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_23,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.16/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.00      | ~ v1_funct_1(X0)
% 3.16/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1162,plain,
% 3.16/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.16/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.16/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.16/1.00      | v1_funct_1(X0) != iProver_top
% 3.16/1.00      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3199,plain,
% 3.16/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1159,c_1162]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1457,plain,
% 3.16/1.00      ( ~ v1_funct_2(sK2,X0,X0)
% 3.16/1.00      | ~ v3_funct_2(sK2,X0,X0)
% 3.16/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.16/1.00      | v1_funct_1(k2_funct_2(X0,sK2))
% 3.16/1.00      | ~ v1_funct_1(sK2) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1458,plain,
% 3.16/1.00      ( v1_funct_2(sK2,X0,X0) != iProver_top
% 3.16/1.00      | v3_funct_2(sK2,X0,X0) != iProver_top
% 3.16/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.16/1.00      | v1_funct_1(k2_funct_2(X0,sK2)) = iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1460,plain,
% 3.16/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.16/1.00      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1458]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3350,plain,
% 3.16/1.00      ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_3199,c_31,c_32,c_33,c_34,c_1460]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3354,plain,
% 3.16/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_3350,c_3296]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_21,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.16/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.16/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.00      | ~ v1_funct_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1164,plain,
% 3.16/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.16/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.16/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.16/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.16/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3293,plain,
% 3.16/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 3.16/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1159,c_1164]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1482,plain,
% 3.16/1.00      ( ~ v1_funct_2(sK2,X0,X0)
% 3.16/1.00      | v3_funct_2(k2_funct_2(X0,sK2),X0,X0)
% 3.16/1.00      | ~ v3_funct_2(sK2,X0,X0)
% 3.16/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.16/1.00      | ~ v1_funct_1(sK2) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1483,plain,
% 3.16/1.00      ( v1_funct_2(sK2,X0,X0) != iProver_top
% 3.16/1.00      | v3_funct_2(k2_funct_2(X0,sK2),X0,X0) = iProver_top
% 3.16/1.00      | v3_funct_2(sK2,X0,X0) != iProver_top
% 3.16/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1482]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1485,plain,
% 3.16/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 3.16/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.16/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1483]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3526,plain,
% 3.16/1.00      ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_3293,c_31,c_32,c_33,c_34,c_1485]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3530,plain,
% 3.16/1.00      ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_3526,c_3296]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5221,plain,
% 3.16/1.00      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_4322,c_96,c_3354,c_3530,c_4319]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5659,plain,
% 3.16/1.00      ( k1_relat_1(sK2) = sK0 ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_4897,c_5221]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_9,plain,
% 3.16/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.16/1.00      | ~ v2_funct_1(X1)
% 3.16/1.00      | ~ v1_funct_1(X1)
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1170,plain,
% 3.16/1.00      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.16/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.16/1.00      | v2_funct_1(X0) != iProver_top
% 3.16/1.00      | v1_funct_1(X0) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5669,plain,
% 3.16/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.16/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.16/1.00      | v2_funct_1(sK2) != iProver_top
% 3.16/1.00      | v1_funct_1(sK2) != iProver_top
% 3.16/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_5659,c_1170]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5971,plain,
% 3.16/1.00      ( r1_tarski(X0,sK0) != iProver_top
% 3.16/1.00      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_5669,c_31,c_33,c_34,c_96,c_1426,c_1601]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5972,plain,
% 3.16/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.16/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 3.16/1.00      inference(renaming,[status(thm)],[c_5971]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5980,plain,
% 3.16/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1160,c_5972]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2931,plain,
% 3.16/1.00      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1160,c_2922]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_14,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.16/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1167,plain,
% 3.16/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.16/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2211,plain,
% 3.16/1.00      ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1159,c_1167]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_25,negated_conjecture,
% 3.16/1.00      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.16/1.00      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.16/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2563,plain,
% 3.16/1.00      ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.16/1.00      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_2211,c_25]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2564,plain,
% 3.16/1.00      ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
% 3.16/1.00      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_2563,c_2211]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_13,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.16/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1168,plain,
% 3.16/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.16/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2391,plain,
% 3.16/1.00      ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_1159,c_1168]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2733,plain,
% 3.16/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
% 3.16/1.00      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_2564,c_2391]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(contradiction,plain,
% 3.16/1.00      ( $false ),
% 3.16/1.00      inference(minisat,[status(thm)],[c_5980,c_2931,c_2733]) ).
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  ------                               Statistics
% 3.16/1.00  
% 3.16/1.00  ------ General
% 3.16/1.00  
% 3.16/1.00  abstr_ref_over_cycles:                  0
% 3.16/1.00  abstr_ref_under_cycles:                 0
% 3.16/1.00  gc_basic_clause_elim:                   0
% 3.16/1.00  forced_gc_time:                         0
% 3.16/1.00  parsing_time:                           0.01
% 3.16/1.00  unif_index_cands_time:                  0.
% 3.16/1.00  unif_index_add_time:                    0.
% 3.16/1.00  orderings_time:                         0.
% 3.16/1.00  out_proof_time:                         0.012
% 3.16/1.00  total_time:                             0.224
% 3.16/1.00  num_of_symbols:                         55
% 3.16/1.00  num_of_terms:                           8963
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing
% 3.16/1.00  
% 3.16/1.00  num_of_splits:                          0
% 3.16/1.00  num_of_split_atoms:                     0
% 3.16/1.00  num_of_reused_defs:                     0
% 3.16/1.00  num_eq_ax_congr_red:                    28
% 3.16/1.00  num_of_sem_filtered_clauses:            1
% 3.16/1.00  num_of_subtypes:                        0
% 3.16/1.00  monotx_restored_types:                  0
% 3.16/1.00  sat_num_of_epr_types:                   0
% 3.16/1.00  sat_num_of_non_cyclic_types:            0
% 3.16/1.00  sat_guarded_non_collapsed_types:        0
% 3.16/1.00  num_pure_diseq_elim:                    0
% 3.16/1.00  simp_replaced_by:                       0
% 3.16/1.00  res_preprocessed:                       135
% 3.16/1.00  prep_upred:                             0
% 3.16/1.00  prep_unflattend:                        10
% 3.16/1.00  smt_new_axioms:                         0
% 3.16/1.00  pred_elim_cands:                        7
% 3.16/1.00  pred_elim:                              3
% 3.16/1.00  pred_elim_cl:                           4
% 3.16/1.00  pred_elim_cycles:                       6
% 3.16/1.00  merged_defs:                            0
% 3.16/1.00  merged_defs_ncl:                        0
% 3.16/1.00  bin_hyper_res:                          0
% 3.16/1.00  prep_cycles:                            4
% 3.16/1.00  pred_elim_time:                         0.005
% 3.16/1.00  splitting_time:                         0.
% 3.16/1.00  sem_filter_time:                        0.
% 3.16/1.00  monotx_time:                            0.001
% 3.16/1.00  subtype_inf_time:                       0.
% 3.16/1.00  
% 3.16/1.00  ------ Problem properties
% 3.16/1.00  
% 3.16/1.00  clauses:                                25
% 3.16/1.00  conjectures:                            6
% 3.16/1.00  epr:                                    6
% 3.16/1.00  horn:                                   25
% 3.16/1.00  ground:                                 6
% 3.16/1.00  unary:                                  7
% 3.16/1.00  binary:                                 5
% 3.16/1.00  lits:                                   74
% 3.16/1.00  lits_eq:                                13
% 3.16/1.00  fd_pure:                                0
% 3.16/1.00  fd_pseudo:                              0
% 3.16/1.00  fd_cond:                                0
% 3.16/1.00  fd_pseudo_cond:                         2
% 3.16/1.00  ac_symbols:                             0
% 3.16/1.00  
% 3.16/1.00  ------ Propositional Solver
% 3.16/1.00  
% 3.16/1.00  prop_solver_calls:                      28
% 3.16/1.00  prop_fast_solver_calls:                 1094
% 3.16/1.00  smt_solver_calls:                       0
% 3.16/1.00  smt_fast_solver_calls:                  0
% 3.16/1.00  prop_num_of_clauses:                    2624
% 3.16/1.00  prop_preprocess_simplified:             6514
% 3.16/1.00  prop_fo_subsumed:                       52
% 3.16/1.00  prop_solver_time:                       0.
% 3.16/1.00  smt_solver_time:                        0.
% 3.16/1.00  smt_fast_solver_time:                   0.
% 3.16/1.00  prop_fast_solver_time:                  0.
% 3.16/1.00  prop_unsat_core_time:                   0.
% 3.16/1.00  
% 3.16/1.00  ------ QBF
% 3.16/1.00  
% 3.16/1.00  qbf_q_res:                              0
% 3.16/1.00  qbf_num_tautologies:                    0
% 3.16/1.00  qbf_prep_cycles:                        0
% 3.16/1.00  
% 3.16/1.00  ------ BMC1
% 3.16/1.00  
% 3.16/1.00  bmc1_current_bound:                     -1
% 3.16/1.00  bmc1_last_solved_bound:                 -1
% 3.16/1.00  bmc1_unsat_core_size:                   -1
% 3.16/1.00  bmc1_unsat_core_parents_size:           -1
% 3.16/1.00  bmc1_merge_next_fun:                    0
% 3.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation
% 3.16/1.00  
% 3.16/1.00  inst_num_of_clauses:                    712
% 3.16/1.00  inst_num_in_passive:                    321
% 3.16/1.00  inst_num_in_active:                     362
% 3.16/1.00  inst_num_in_unprocessed:                29
% 3.16/1.00  inst_num_of_loops:                      380
% 3.16/1.00  inst_num_of_learning_restarts:          0
% 3.16/1.00  inst_num_moves_active_passive:          14
% 3.16/1.00  inst_lit_activity:                      0
% 3.16/1.00  inst_lit_activity_moves:                0
% 3.16/1.00  inst_num_tautologies:                   0
% 3.16/1.00  inst_num_prop_implied:                  0
% 3.16/1.00  inst_num_existing_simplified:           0
% 3.16/1.00  inst_num_eq_res_simplified:             0
% 3.16/1.00  inst_num_child_elim:                    0
% 3.16/1.00  inst_num_of_dismatching_blockings:      153
% 3.16/1.00  inst_num_of_non_proper_insts:           563
% 3.16/1.00  inst_num_of_duplicates:                 0
% 3.16/1.00  inst_inst_num_from_inst_to_res:         0
% 3.16/1.00  inst_dismatching_checking_time:         0.
% 3.16/1.00  
% 3.16/1.00  ------ Resolution
% 3.16/1.00  
% 3.16/1.00  res_num_of_clauses:                     0
% 3.16/1.00  res_num_in_passive:                     0
% 3.16/1.00  res_num_in_active:                      0
% 3.16/1.00  res_num_of_loops:                       139
% 3.16/1.00  res_forward_subset_subsumed:            37
% 3.16/1.00  res_backward_subset_subsumed:           0
% 3.16/1.00  res_forward_subsumed:                   0
% 3.16/1.00  res_backward_subsumed:                  0
% 3.16/1.00  res_forward_subsumption_resolution:     1
% 3.16/1.00  res_backward_subsumption_resolution:    0
% 3.16/1.00  res_clause_to_clause_subsumption:       108
% 3.16/1.00  res_orphan_elimination:                 0
% 3.16/1.00  res_tautology_del:                      43
% 3.16/1.00  res_num_eq_res_simplified:              0
% 3.16/1.00  res_num_sel_changes:                    0
% 3.16/1.00  res_moves_from_active_to_pass:          0
% 3.16/1.00  
% 3.16/1.00  ------ Superposition
% 3.16/1.00  
% 3.16/1.00  sup_time_total:                         0.
% 3.16/1.00  sup_time_generating:                    0.
% 3.16/1.00  sup_time_sim_full:                      0.
% 3.16/1.00  sup_time_sim_immed:                     0.
% 3.16/1.00  
% 3.16/1.00  sup_num_of_clauses:                     90
% 3.16/1.00  sup_num_in_active:                      68
% 3.16/1.00  sup_num_in_passive:                     22
% 3.16/1.00  sup_num_of_loops:                       75
% 3.16/1.00  sup_fw_superposition:                   38
% 3.16/1.00  sup_bw_superposition:                   34
% 3.16/1.00  sup_immediate_simplified:               11
% 3.16/1.00  sup_given_eliminated:                   0
% 3.16/1.00  comparisons_done:                       0
% 3.16/1.00  comparisons_avoided:                    0
% 3.16/1.00  
% 3.16/1.00  ------ Simplifications
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  sim_fw_subset_subsumed:                 0
% 3.16/1.00  sim_bw_subset_subsumed:                 0
% 3.16/1.00  sim_fw_subsumed:                        0
% 3.16/1.00  sim_bw_subsumed:                        0
% 3.16/1.00  sim_fw_subsumption_res:                 0
% 3.16/1.00  sim_bw_subsumption_res:                 0
% 3.16/1.00  sim_tautology_del:                      0
% 3.16/1.00  sim_eq_tautology_del:                   5
% 3.16/1.00  sim_eq_res_simp:                        1
% 3.16/1.00  sim_fw_demodulated:                     2
% 3.16/1.00  sim_bw_demodulated:                     8
% 3.16/1.00  sim_light_normalised:                   18
% 3.16/1.00  sim_joinable_taut:                      0
% 3.16/1.00  sim_joinable_simp:                      0
% 3.16/1.00  sim_ac_normalised:                      0
% 3.16/1.00  sim_smt_subsumption:                    0
% 3.16/1.00  
%------------------------------------------------------------------------------
