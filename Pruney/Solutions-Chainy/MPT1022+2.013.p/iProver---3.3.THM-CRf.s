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
% DateTime   : Thu Dec  3 12:07:38 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  186 (1312 expanded)
%              Number of clauses        :  111 ( 411 expanded)
%              Number of leaves         :   18 ( 257 expanded)
%              Depth                    :   21
%              Number of atoms          :  599 (6651 expanded)
%              Number of equality atoms :  254 (1908 expanded)
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

fof(f47,plain,
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

fof(f48,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f47])).

fof(f79,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f73,plain,(
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

fof(f61,plain,(
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

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f67,plain,(
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

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
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

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

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

fof(f60,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f48])).

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

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1289,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1288,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1290,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2381,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1290])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1628,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1630,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_2809,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2381,c_31,c_30,c_29,c_28,c_1630])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1294,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4060,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2809,c_1294])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4515,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4060,c_32,c_33,c_34,c_35])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1298,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4525,plain,
    ( v4_relat_1(k2_funct_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4515,c_1298])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1302,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4676,plain,
    ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4525,c_1302])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_92,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_94,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1307,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4520,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4515,c_1307])).

cnf(c_5344,plain,
    ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4676,c_94,c_4520])).

cnf(c_4924,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4520,c_94])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1303,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4930,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_4924,c_1303])).

cnf(c_5347,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5344,c_4930])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_20,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_379,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_380,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_396,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_380,c_12])).

cnf(c_1284,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_4523,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4515,c_1284])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1291,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3092,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1291])).

cnf(c_3093,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3092,c_2809])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1293,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4051,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1293])).

cnf(c_4052,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4051,c_2809])).

cnf(c_5564,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4523,c_32,c_33,c_34,c_94,c_3093,c_4052,c_4520])).

cnf(c_17,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1295,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3364,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1295])).

cnf(c_1579,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1580,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1579])).

cnf(c_1582,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_3570,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3364,c_32,c_34,c_35,c_1582])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1308,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1299,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3541,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1299])).

cnf(c_6839,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_3541])).

cnf(c_2305,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1307])).

cnf(c_1528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1703,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_1704,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1703])).

cnf(c_2308,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2305,c_35,c_94,c_1704])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1306,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2681,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1306])).

cnf(c_2865,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_1302])).

cnf(c_2972,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2308,c_2865])).

cnf(c_2313,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2308,c_1303])).

cnf(c_2979,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2972,c_2313])).

cnf(c_1678,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1284])).

cnf(c_93,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1679,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1678])).

cnf(c_2080,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1678,c_31,c_29,c_28,c_93,c_1679,c_1703])).

cnf(c_2980,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2979,c_2080])).

cnf(c_6850,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6839,c_2980])).

cnf(c_7013,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6850,c_32,c_35,c_94,c_1704])).

cnf(c_9390,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_5347,c_5564,c_7013])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1300,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9422,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9390,c_1300])).

cnf(c_10333,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9422,c_32,c_34,c_35,c_94,c_1582,c_1704])).

cnf(c_10334,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10333])).

cnf(c_10343,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1289,c_10334])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1301,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3103,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_1301])).

cnf(c_3658,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3103,c_32,c_35,c_94,c_1704])).

cnf(c_3668,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1289,c_3658])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1296,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2526,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1288,c_1296])).

cnf(c_26,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2728,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2526,c_26])).

cnf(c_2729,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2728,c_2526])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1297,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2531,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1288,c_1297])).

cnf(c_2805,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2729,c_2531])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10343,c_3668,c_2805])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:48:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.47/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.00  
% 3.47/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/1.00  
% 3.47/1.00  ------  iProver source info
% 3.47/1.00  
% 3.47/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.47/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/1.00  git: non_committed_changes: false
% 3.47/1.00  git: last_make_outside_of_git: false
% 3.47/1.00  
% 3.47/1.00  ------ 
% 3.47/1.00  
% 3.47/1.00  ------ Input Options
% 3.47/1.00  
% 3.47/1.00  --out_options                           all
% 3.47/1.00  --tptp_safe_out                         true
% 3.47/1.00  --problem_path                          ""
% 3.47/1.00  --include_path                          ""
% 3.47/1.00  --clausifier                            res/vclausify_rel
% 3.47/1.00  --clausifier_options                    --mode clausify
% 3.47/1.00  --stdin                                 false
% 3.47/1.00  --stats_out                             all
% 3.47/1.00  
% 3.47/1.00  ------ General Options
% 3.47/1.00  
% 3.47/1.00  --fof                                   false
% 3.47/1.00  --time_out_real                         305.
% 3.47/1.00  --time_out_virtual                      -1.
% 3.47/1.00  --symbol_type_check                     false
% 3.47/1.00  --clausify_out                          false
% 3.47/1.00  --sig_cnt_out                           false
% 3.47/1.00  --trig_cnt_out                          false
% 3.47/1.00  --trig_cnt_out_tolerance                1.
% 3.47/1.00  --trig_cnt_out_sk_spl                   false
% 3.47/1.00  --abstr_cl_out                          false
% 3.47/1.00  
% 3.47/1.00  ------ Global Options
% 3.47/1.00  
% 3.47/1.00  --schedule                              default
% 3.47/1.00  --add_important_lit                     false
% 3.47/1.00  --prop_solver_per_cl                    1000
% 3.47/1.00  --min_unsat_core                        false
% 3.47/1.00  --soft_assumptions                      false
% 3.47/1.00  --soft_lemma_size                       3
% 3.47/1.00  --prop_impl_unit_size                   0
% 3.47/1.00  --prop_impl_unit                        []
% 3.47/1.00  --share_sel_clauses                     true
% 3.47/1.00  --reset_solvers                         false
% 3.47/1.00  --bc_imp_inh                            [conj_cone]
% 3.47/1.00  --conj_cone_tolerance                   3.
% 3.47/1.00  --extra_neg_conj                        none
% 3.47/1.00  --large_theory_mode                     true
% 3.47/1.00  --prolific_symb_bound                   200
% 3.47/1.00  --lt_threshold                          2000
% 3.47/1.00  --clause_weak_htbl                      true
% 3.47/1.00  --gc_record_bc_elim                     false
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing Options
% 3.47/1.00  
% 3.47/1.00  --preprocessing_flag                    true
% 3.47/1.00  --time_out_prep_mult                    0.1
% 3.47/1.00  --splitting_mode                        input
% 3.47/1.00  --splitting_grd                         true
% 3.47/1.00  --splitting_cvd                         false
% 3.47/1.00  --splitting_cvd_svl                     false
% 3.47/1.00  --splitting_nvd                         32
% 3.47/1.00  --sub_typing                            true
% 3.47/1.00  --prep_gs_sim                           true
% 3.47/1.00  --prep_unflatten                        true
% 3.47/1.00  --prep_res_sim                          true
% 3.47/1.00  --prep_upred                            true
% 3.47/1.00  --prep_sem_filter                       exhaustive
% 3.47/1.00  --prep_sem_filter_out                   false
% 3.47/1.00  --pred_elim                             true
% 3.47/1.00  --res_sim_input                         true
% 3.47/1.00  --eq_ax_congr_red                       true
% 3.47/1.00  --pure_diseq_elim                       true
% 3.47/1.00  --brand_transform                       false
% 3.47/1.00  --non_eq_to_eq                          false
% 3.47/1.00  --prep_def_merge                        true
% 3.47/1.00  --prep_def_merge_prop_impl              false
% 3.47/1.00  --prep_def_merge_mbd                    true
% 3.47/1.00  --prep_def_merge_tr_red                 false
% 3.47/1.00  --prep_def_merge_tr_cl                  false
% 3.47/1.00  --smt_preprocessing                     true
% 3.47/1.00  --smt_ac_axioms                         fast
% 3.47/1.00  --preprocessed_out                      false
% 3.47/1.00  --preprocessed_stats                    false
% 3.47/1.00  
% 3.47/1.00  ------ Abstraction refinement Options
% 3.47/1.00  
% 3.47/1.00  --abstr_ref                             []
% 3.47/1.00  --abstr_ref_prep                        false
% 3.47/1.00  --abstr_ref_until_sat                   false
% 3.47/1.00  --abstr_ref_sig_restrict                funpre
% 3.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/1.00  --abstr_ref_under                       []
% 3.47/1.00  
% 3.47/1.00  ------ SAT Options
% 3.47/1.00  
% 3.47/1.00  --sat_mode                              false
% 3.47/1.00  --sat_fm_restart_options                ""
% 3.47/1.00  --sat_gr_def                            false
% 3.47/1.00  --sat_epr_types                         true
% 3.47/1.00  --sat_non_cyclic_types                  false
% 3.47/1.00  --sat_finite_models                     false
% 3.47/1.00  --sat_fm_lemmas                         false
% 3.47/1.00  --sat_fm_prep                           false
% 3.47/1.00  --sat_fm_uc_incr                        true
% 3.47/1.00  --sat_out_model                         small
% 3.47/1.00  --sat_out_clauses                       false
% 3.47/1.00  
% 3.47/1.00  ------ QBF Options
% 3.47/1.00  
% 3.47/1.00  --qbf_mode                              false
% 3.47/1.00  --qbf_elim_univ                         false
% 3.47/1.00  --qbf_dom_inst                          none
% 3.47/1.00  --qbf_dom_pre_inst                      false
% 3.47/1.00  --qbf_sk_in                             false
% 3.47/1.00  --qbf_pred_elim                         true
% 3.47/1.00  --qbf_split                             512
% 3.47/1.00  
% 3.47/1.00  ------ BMC1 Options
% 3.47/1.00  
% 3.47/1.00  --bmc1_incremental                      false
% 3.47/1.00  --bmc1_axioms                           reachable_all
% 3.47/1.00  --bmc1_min_bound                        0
% 3.47/1.00  --bmc1_max_bound                        -1
% 3.47/1.00  --bmc1_max_bound_default                -1
% 3.47/1.00  --bmc1_symbol_reachability              true
% 3.47/1.00  --bmc1_property_lemmas                  false
% 3.47/1.00  --bmc1_k_induction                      false
% 3.47/1.00  --bmc1_non_equiv_states                 false
% 3.47/1.00  --bmc1_deadlock                         false
% 3.47/1.00  --bmc1_ucm                              false
% 3.47/1.00  --bmc1_add_unsat_core                   none
% 3.47/1.00  --bmc1_unsat_core_children              false
% 3.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/1.00  --bmc1_out_stat                         full
% 3.47/1.00  --bmc1_ground_init                      false
% 3.47/1.00  --bmc1_pre_inst_next_state              false
% 3.47/1.00  --bmc1_pre_inst_state                   false
% 3.47/1.00  --bmc1_pre_inst_reach_state             false
% 3.47/1.00  --bmc1_out_unsat_core                   false
% 3.47/1.00  --bmc1_aig_witness_out                  false
% 3.47/1.00  --bmc1_verbose                          false
% 3.47/1.00  --bmc1_dump_clauses_tptp                false
% 3.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.47/1.00  --bmc1_dump_file                        -
% 3.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.47/1.00  --bmc1_ucm_extend_mode                  1
% 3.47/1.00  --bmc1_ucm_init_mode                    2
% 3.47/1.00  --bmc1_ucm_cone_mode                    none
% 3.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.47/1.00  --bmc1_ucm_relax_model                  4
% 3.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/1.00  --bmc1_ucm_layered_model                none
% 3.47/1.00  --bmc1_ucm_max_lemma_size               10
% 3.47/1.00  
% 3.47/1.00  ------ AIG Options
% 3.47/1.00  
% 3.47/1.00  --aig_mode                              false
% 3.47/1.00  
% 3.47/1.00  ------ Instantiation Options
% 3.47/1.00  
% 3.47/1.00  --instantiation_flag                    true
% 3.47/1.00  --inst_sos_flag                         false
% 3.47/1.00  --inst_sos_phase                        true
% 3.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/1.00  --inst_lit_sel_side                     num_symb
% 3.47/1.00  --inst_solver_per_active                1400
% 3.47/1.00  --inst_solver_calls_frac                1.
% 3.47/1.00  --inst_passive_queue_type               priority_queues
% 3.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/1.00  --inst_passive_queues_freq              [25;2]
% 3.47/1.00  --inst_dismatching                      true
% 3.47/1.00  --inst_eager_unprocessed_to_passive     true
% 3.47/1.00  --inst_prop_sim_given                   true
% 3.47/1.00  --inst_prop_sim_new                     false
% 3.47/1.00  --inst_subs_new                         false
% 3.47/1.00  --inst_eq_res_simp                      false
% 3.47/1.00  --inst_subs_given                       false
% 3.47/1.00  --inst_orphan_elimination               true
% 3.47/1.00  --inst_learning_loop_flag               true
% 3.47/1.00  --inst_learning_start                   3000
% 3.47/1.00  --inst_learning_factor                  2
% 3.47/1.00  --inst_start_prop_sim_after_learn       3
% 3.47/1.00  --inst_sel_renew                        solver
% 3.47/1.00  --inst_lit_activity_flag                true
% 3.47/1.00  --inst_restr_to_given                   false
% 3.47/1.00  --inst_activity_threshold               500
% 3.47/1.00  --inst_out_proof                        true
% 3.47/1.00  
% 3.47/1.00  ------ Resolution Options
% 3.47/1.00  
% 3.47/1.00  --resolution_flag                       true
% 3.47/1.00  --res_lit_sel                           adaptive
% 3.47/1.00  --res_lit_sel_side                      none
% 3.47/1.00  --res_ordering                          kbo
% 3.47/1.00  --res_to_prop_solver                    active
% 3.47/1.00  --res_prop_simpl_new                    false
% 3.47/1.00  --res_prop_simpl_given                  true
% 3.47/1.00  --res_passive_queue_type                priority_queues
% 3.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/1.00  --res_passive_queues_freq               [15;5]
% 3.47/1.00  --res_forward_subs                      full
% 3.47/1.00  --res_backward_subs                     full
% 3.47/1.00  --res_forward_subs_resolution           true
% 3.47/1.00  --res_backward_subs_resolution          true
% 3.47/1.00  --res_orphan_elimination                true
% 3.47/1.00  --res_time_limit                        2.
% 3.47/1.00  --res_out_proof                         true
% 3.47/1.00  
% 3.47/1.00  ------ Superposition Options
% 3.47/1.00  
% 3.47/1.00  --superposition_flag                    true
% 3.47/1.00  --sup_passive_queue_type                priority_queues
% 3.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.47/1.00  --demod_completeness_check              fast
% 3.47/1.00  --demod_use_ground                      true
% 3.47/1.00  --sup_to_prop_solver                    passive
% 3.47/1.00  --sup_prop_simpl_new                    true
% 3.47/1.00  --sup_prop_simpl_given                  true
% 3.47/1.00  --sup_fun_splitting                     false
% 3.47/1.00  --sup_smt_interval                      50000
% 3.47/1.00  
% 3.47/1.00  ------ Superposition Simplification Setup
% 3.47/1.00  
% 3.47/1.00  --sup_indices_passive                   []
% 3.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_full_bw                           [BwDemod]
% 3.47/1.00  --sup_immed_triv                        [TrivRules]
% 3.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_immed_bw_main                     []
% 3.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/1.00  
% 3.47/1.00  ------ Combination Options
% 3.47/1.00  
% 3.47/1.00  --comb_res_mult                         3
% 3.47/1.00  --comb_sup_mult                         2
% 3.47/1.00  --comb_inst_mult                        10
% 3.47/1.00  
% 3.47/1.00  ------ Debug Options
% 3.47/1.00  
% 3.47/1.00  --dbg_backtrace                         false
% 3.47/1.00  --dbg_dump_prop_clauses                 false
% 3.47/1.00  --dbg_dump_prop_clauses_file            -
% 3.47/1.00  --dbg_out_stat                          false
% 3.47/1.00  ------ Parsing...
% 3.47/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/1.00  ------ Proving...
% 3.47/1.00  ------ Problem Properties 
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  clauses                                 27
% 3.47/1.00  conjectures                             6
% 3.47/1.00  EPR                                     6
% 3.47/1.00  Horn                                    27
% 3.47/1.00  unary                                   7
% 3.47/1.00  binary                                  5
% 3.47/1.00  lits                                    80
% 3.47/1.00  lits eq                                 12
% 3.47/1.00  fd_pure                                 0
% 3.47/1.00  fd_pseudo                               0
% 3.47/1.00  fd_cond                                 0
% 3.47/1.00  fd_pseudo_cond                          2
% 3.47/1.00  AC symbols                              0
% 3.47/1.00  
% 3.47/1.00  ------ Schedule dynamic 5 is on 
% 3.47/1.00  
% 3.47/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  ------ 
% 3.47/1.00  Current options:
% 3.47/1.00  ------ 
% 3.47/1.00  
% 3.47/1.00  ------ Input Options
% 3.47/1.00  
% 3.47/1.00  --out_options                           all
% 3.47/1.00  --tptp_safe_out                         true
% 3.47/1.00  --problem_path                          ""
% 3.47/1.00  --include_path                          ""
% 3.47/1.00  --clausifier                            res/vclausify_rel
% 3.47/1.00  --clausifier_options                    --mode clausify
% 3.47/1.00  --stdin                                 false
% 3.47/1.00  --stats_out                             all
% 3.47/1.00  
% 3.47/1.00  ------ General Options
% 3.47/1.00  
% 3.47/1.00  --fof                                   false
% 3.47/1.00  --time_out_real                         305.
% 3.47/1.00  --time_out_virtual                      -1.
% 3.47/1.00  --symbol_type_check                     false
% 3.47/1.00  --clausify_out                          false
% 3.47/1.00  --sig_cnt_out                           false
% 3.47/1.00  --trig_cnt_out                          false
% 3.47/1.00  --trig_cnt_out_tolerance                1.
% 3.47/1.00  --trig_cnt_out_sk_spl                   false
% 3.47/1.00  --abstr_cl_out                          false
% 3.47/1.00  
% 3.47/1.00  ------ Global Options
% 3.47/1.00  
% 3.47/1.00  --schedule                              default
% 3.47/1.00  --add_important_lit                     false
% 3.47/1.00  --prop_solver_per_cl                    1000
% 3.47/1.00  --min_unsat_core                        false
% 3.47/1.00  --soft_assumptions                      false
% 3.47/1.00  --soft_lemma_size                       3
% 3.47/1.00  --prop_impl_unit_size                   0
% 3.47/1.00  --prop_impl_unit                        []
% 3.47/1.00  --share_sel_clauses                     true
% 3.47/1.00  --reset_solvers                         false
% 3.47/1.00  --bc_imp_inh                            [conj_cone]
% 3.47/1.00  --conj_cone_tolerance                   3.
% 3.47/1.00  --extra_neg_conj                        none
% 3.47/1.00  --large_theory_mode                     true
% 3.47/1.00  --prolific_symb_bound                   200
% 3.47/1.00  --lt_threshold                          2000
% 3.47/1.00  --clause_weak_htbl                      true
% 3.47/1.00  --gc_record_bc_elim                     false
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing Options
% 3.47/1.00  
% 3.47/1.00  --preprocessing_flag                    true
% 3.47/1.00  --time_out_prep_mult                    0.1
% 3.47/1.00  --splitting_mode                        input
% 3.47/1.00  --splitting_grd                         true
% 3.47/1.00  --splitting_cvd                         false
% 3.47/1.00  --splitting_cvd_svl                     false
% 3.47/1.00  --splitting_nvd                         32
% 3.47/1.00  --sub_typing                            true
% 3.47/1.00  --prep_gs_sim                           true
% 3.47/1.00  --prep_unflatten                        true
% 3.47/1.00  --prep_res_sim                          true
% 3.47/1.00  --prep_upred                            true
% 3.47/1.00  --prep_sem_filter                       exhaustive
% 3.47/1.00  --prep_sem_filter_out                   false
% 3.47/1.00  --pred_elim                             true
% 3.47/1.00  --res_sim_input                         true
% 3.47/1.00  --eq_ax_congr_red                       true
% 3.47/1.00  --pure_diseq_elim                       true
% 3.47/1.00  --brand_transform                       false
% 3.47/1.00  --non_eq_to_eq                          false
% 3.47/1.00  --prep_def_merge                        true
% 3.47/1.00  --prep_def_merge_prop_impl              false
% 3.47/1.00  --prep_def_merge_mbd                    true
% 3.47/1.00  --prep_def_merge_tr_red                 false
% 3.47/1.00  --prep_def_merge_tr_cl                  false
% 3.47/1.00  --smt_preprocessing                     true
% 3.47/1.00  --smt_ac_axioms                         fast
% 3.47/1.00  --preprocessed_out                      false
% 3.47/1.00  --preprocessed_stats                    false
% 3.47/1.00  
% 3.47/1.00  ------ Abstraction refinement Options
% 3.47/1.00  
% 3.47/1.00  --abstr_ref                             []
% 3.47/1.00  --abstr_ref_prep                        false
% 3.47/1.00  --abstr_ref_until_sat                   false
% 3.47/1.00  --abstr_ref_sig_restrict                funpre
% 3.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/1.00  --abstr_ref_under                       []
% 3.47/1.00  
% 3.47/1.00  ------ SAT Options
% 3.47/1.00  
% 3.47/1.00  --sat_mode                              false
% 3.47/1.00  --sat_fm_restart_options                ""
% 3.47/1.00  --sat_gr_def                            false
% 3.47/1.00  --sat_epr_types                         true
% 3.47/1.00  --sat_non_cyclic_types                  false
% 3.47/1.00  --sat_finite_models                     false
% 3.47/1.00  --sat_fm_lemmas                         false
% 3.47/1.00  --sat_fm_prep                           false
% 3.47/1.00  --sat_fm_uc_incr                        true
% 3.47/1.00  --sat_out_model                         small
% 3.47/1.00  --sat_out_clauses                       false
% 3.47/1.00  
% 3.47/1.00  ------ QBF Options
% 3.47/1.00  
% 3.47/1.00  --qbf_mode                              false
% 3.47/1.00  --qbf_elim_univ                         false
% 3.47/1.00  --qbf_dom_inst                          none
% 3.47/1.00  --qbf_dom_pre_inst                      false
% 3.47/1.00  --qbf_sk_in                             false
% 3.47/1.00  --qbf_pred_elim                         true
% 3.47/1.00  --qbf_split                             512
% 3.47/1.00  
% 3.47/1.00  ------ BMC1 Options
% 3.47/1.00  
% 3.47/1.00  --bmc1_incremental                      false
% 3.47/1.00  --bmc1_axioms                           reachable_all
% 3.47/1.00  --bmc1_min_bound                        0
% 3.47/1.00  --bmc1_max_bound                        -1
% 3.47/1.00  --bmc1_max_bound_default                -1
% 3.47/1.00  --bmc1_symbol_reachability              true
% 3.47/1.00  --bmc1_property_lemmas                  false
% 3.47/1.00  --bmc1_k_induction                      false
% 3.47/1.00  --bmc1_non_equiv_states                 false
% 3.47/1.00  --bmc1_deadlock                         false
% 3.47/1.00  --bmc1_ucm                              false
% 3.47/1.00  --bmc1_add_unsat_core                   none
% 3.47/1.00  --bmc1_unsat_core_children              false
% 3.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/1.00  --bmc1_out_stat                         full
% 3.47/1.00  --bmc1_ground_init                      false
% 3.47/1.00  --bmc1_pre_inst_next_state              false
% 3.47/1.00  --bmc1_pre_inst_state                   false
% 3.47/1.00  --bmc1_pre_inst_reach_state             false
% 3.47/1.00  --bmc1_out_unsat_core                   false
% 3.47/1.00  --bmc1_aig_witness_out                  false
% 3.47/1.00  --bmc1_verbose                          false
% 3.47/1.00  --bmc1_dump_clauses_tptp                false
% 3.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.47/1.00  --bmc1_dump_file                        -
% 3.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.47/1.00  --bmc1_ucm_extend_mode                  1
% 3.47/1.00  --bmc1_ucm_init_mode                    2
% 3.47/1.00  --bmc1_ucm_cone_mode                    none
% 3.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.47/1.00  --bmc1_ucm_relax_model                  4
% 3.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/1.00  --bmc1_ucm_layered_model                none
% 3.47/1.00  --bmc1_ucm_max_lemma_size               10
% 3.47/1.00  
% 3.47/1.00  ------ AIG Options
% 3.47/1.00  
% 3.47/1.00  --aig_mode                              false
% 3.47/1.00  
% 3.47/1.00  ------ Instantiation Options
% 3.47/1.00  
% 3.47/1.00  --instantiation_flag                    true
% 3.47/1.00  --inst_sos_flag                         false
% 3.47/1.00  --inst_sos_phase                        true
% 3.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/1.00  --inst_lit_sel_side                     none
% 3.47/1.00  --inst_solver_per_active                1400
% 3.47/1.00  --inst_solver_calls_frac                1.
% 3.47/1.00  --inst_passive_queue_type               priority_queues
% 3.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/1.00  --inst_passive_queues_freq              [25;2]
% 3.47/1.00  --inst_dismatching                      true
% 3.47/1.00  --inst_eager_unprocessed_to_passive     true
% 3.47/1.00  --inst_prop_sim_given                   true
% 3.47/1.00  --inst_prop_sim_new                     false
% 3.47/1.00  --inst_subs_new                         false
% 3.47/1.00  --inst_eq_res_simp                      false
% 3.47/1.00  --inst_subs_given                       false
% 3.47/1.00  --inst_orphan_elimination               true
% 3.47/1.00  --inst_learning_loop_flag               true
% 3.47/1.00  --inst_learning_start                   3000
% 3.47/1.00  --inst_learning_factor                  2
% 3.47/1.00  --inst_start_prop_sim_after_learn       3
% 3.47/1.00  --inst_sel_renew                        solver
% 3.47/1.00  --inst_lit_activity_flag                true
% 3.47/1.00  --inst_restr_to_given                   false
% 3.47/1.00  --inst_activity_threshold               500
% 3.47/1.00  --inst_out_proof                        true
% 3.47/1.00  
% 3.47/1.00  ------ Resolution Options
% 3.47/1.00  
% 3.47/1.00  --resolution_flag                       false
% 3.47/1.00  --res_lit_sel                           adaptive
% 3.47/1.00  --res_lit_sel_side                      none
% 3.47/1.00  --res_ordering                          kbo
% 3.47/1.00  --res_to_prop_solver                    active
% 3.47/1.00  --res_prop_simpl_new                    false
% 3.47/1.00  --res_prop_simpl_given                  true
% 3.47/1.00  --res_passive_queue_type                priority_queues
% 3.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/1.00  --res_passive_queues_freq               [15;5]
% 3.47/1.00  --res_forward_subs                      full
% 3.47/1.00  --res_backward_subs                     full
% 3.47/1.00  --res_forward_subs_resolution           true
% 3.47/1.00  --res_backward_subs_resolution          true
% 3.47/1.00  --res_orphan_elimination                true
% 3.47/1.00  --res_time_limit                        2.
% 3.47/1.00  --res_out_proof                         true
% 3.47/1.00  
% 3.47/1.00  ------ Superposition Options
% 3.47/1.00  
% 3.47/1.00  --superposition_flag                    true
% 3.47/1.00  --sup_passive_queue_type                priority_queues
% 3.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.47/1.00  --demod_completeness_check              fast
% 3.47/1.00  --demod_use_ground                      true
% 3.47/1.00  --sup_to_prop_solver                    passive
% 3.47/1.00  --sup_prop_simpl_new                    true
% 3.47/1.00  --sup_prop_simpl_given                  true
% 3.47/1.00  --sup_fun_splitting                     false
% 3.47/1.00  --sup_smt_interval                      50000
% 3.47/1.00  
% 3.47/1.00  ------ Superposition Simplification Setup
% 3.47/1.00  
% 3.47/1.00  --sup_indices_passive                   []
% 3.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_full_bw                           [BwDemod]
% 3.47/1.00  --sup_immed_triv                        [TrivRules]
% 3.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_immed_bw_main                     []
% 3.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/1.00  
% 3.47/1.00  ------ Combination Options
% 3.47/1.00  
% 3.47/1.00  --comb_res_mult                         3
% 3.47/1.00  --comb_sup_mult                         2
% 3.47/1.00  --comb_inst_mult                        10
% 3.47/1.00  
% 3.47/1.00  ------ Debug Options
% 3.47/1.00  
% 3.47/1.00  --dbg_backtrace                         false
% 3.47/1.00  --dbg_dump_prop_clauses                 false
% 3.47/1.00  --dbg_dump_prop_clauses_file            -
% 3.47/1.00  --dbg_out_stat                          false
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  ------ Proving...
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  % SZS status Theorem for theBenchmark.p
% 3.47/1.00  
% 3.47/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/1.00  
% 3.47/1.00  fof(f17,conjecture,(
% 3.47/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f18,negated_conjecture,(
% 3.47/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.47/1.00    inference(negated_conjecture,[],[f17])).
% 3.47/1.00  
% 3.47/1.00  fof(f41,plain,(
% 3.47/1.00    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 3.47/1.00    inference(ennf_transformation,[],[f18])).
% 3.47/1.00  
% 3.47/1.00  fof(f42,plain,(
% 3.47/1.00    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 3.47/1.00    inference(flattening,[],[f41])).
% 3.47/1.00  
% 3.47/1.00  fof(f47,plain,(
% 3.47/1.00    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 3.47/1.00    introduced(choice_axiom,[])).
% 3.47/1.00  
% 3.47/1.00  fof(f48,plain,(
% 3.47/1.00    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 3.47/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f47])).
% 3.47/1.00  
% 3.47/1.00  fof(f79,plain,(
% 3.47/1.00    r1_tarski(sK1,sK0)),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f78,plain,(
% 3.47/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f16,axiom,(
% 3.47/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f39,plain,(
% 3.47/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.47/1.00    inference(ennf_transformation,[],[f16])).
% 3.47/1.00  
% 3.47/1.00  fof(f40,plain,(
% 3.47/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.47/1.00    inference(flattening,[],[f39])).
% 3.47/1.00  
% 3.47/1.00  fof(f74,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f40])).
% 3.47/1.00  
% 3.47/1.00  fof(f75,plain,(
% 3.47/1.00    v1_funct_1(sK2)),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f76,plain,(
% 3.47/1.00    v1_funct_2(sK2,sK0,sK0)),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f77,plain,(
% 3.47/1.00    v3_funct_2(sK2,sK0,sK0)),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f15,axiom,(
% 3.47/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f37,plain,(
% 3.47/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.47/1.00    inference(ennf_transformation,[],[f15])).
% 3.47/1.00  
% 3.47/1.00  fof(f38,plain,(
% 3.47/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.47/1.00    inference(flattening,[],[f37])).
% 3.47/1.00  
% 3.47/1.00  fof(f73,plain,(
% 3.47/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f38])).
% 3.47/1.00  
% 3.47/1.00  fof(f10,axiom,(
% 3.47/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f30,plain,(
% 3.47/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/1.00    inference(ennf_transformation,[],[f10])).
% 3.47/1.00  
% 3.47/1.00  fof(f61,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f30])).
% 3.47/1.00  
% 3.47/1.00  fof(f6,axiom,(
% 3.47/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f22,plain,(
% 3.47/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.47/1.00    inference(ennf_transformation,[],[f6])).
% 3.47/1.00  
% 3.47/1.00  fof(f23,plain,(
% 3.47/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.47/1.00    inference(flattening,[],[f22])).
% 3.47/1.00  
% 3.47/1.00  fof(f57,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f23])).
% 3.47/1.00  
% 3.47/1.00  fof(f4,axiom,(
% 3.47/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f55,plain,(
% 3.47/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f4])).
% 3.47/1.00  
% 3.47/1.00  fof(f2,axiom,(
% 3.47/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f19,plain,(
% 3.47/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.47/1.00    inference(ennf_transformation,[],[f2])).
% 3.47/1.00  
% 3.47/1.00  fof(f52,plain,(
% 3.47/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f19])).
% 3.47/1.00  
% 3.47/1.00  fof(f5,axiom,(
% 3.47/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f21,plain,(
% 3.47/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.47/1.00    inference(ennf_transformation,[],[f5])).
% 3.47/1.00  
% 3.47/1.00  fof(f56,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f21])).
% 3.47/1.00  
% 3.47/1.00  fof(f13,axiom,(
% 3.47/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f33,plain,(
% 3.47/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/1.00    inference(ennf_transformation,[],[f13])).
% 3.47/1.00  
% 3.47/1.00  fof(f34,plain,(
% 3.47/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/1.00    inference(flattening,[],[f33])).
% 3.47/1.00  
% 3.47/1.00  fof(f67,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f34])).
% 3.47/1.00  
% 3.47/1.00  fof(f14,axiom,(
% 3.47/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f35,plain,(
% 3.47/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.47/1.00    inference(ennf_transformation,[],[f14])).
% 3.47/1.00  
% 3.47/1.00  fof(f36,plain,(
% 3.47/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.47/1.00    inference(flattening,[],[f35])).
% 3.47/1.00  
% 3.47/1.00  fof(f46,plain,(
% 3.47/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.47/1.00    inference(nnf_transformation,[],[f36])).
% 3.47/1.00  
% 3.47/1.00  fof(f68,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f46])).
% 3.47/1.00  
% 3.47/1.00  fof(f62,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f30])).
% 3.47/1.00  
% 3.47/1.00  fof(f70,plain,(
% 3.47/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f38])).
% 3.47/1.00  
% 3.47/1.00  fof(f72,plain,(
% 3.47/1.00    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f38])).
% 3.47/1.00  
% 3.47/1.00  fof(f66,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f34])).
% 3.47/1.00  
% 3.47/1.00  fof(f1,axiom,(
% 3.47/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f43,plain,(
% 3.47/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.47/1.00    inference(nnf_transformation,[],[f1])).
% 3.47/1.00  
% 3.47/1.00  fof(f44,plain,(
% 3.47/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.47/1.00    inference(flattening,[],[f43])).
% 3.47/1.00  
% 3.47/1.00  fof(f49,plain,(
% 3.47/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.47/1.00    inference(cnf_transformation,[],[f44])).
% 3.47/1.00  
% 3.47/1.00  fof(f82,plain,(
% 3.47/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.47/1.00    inference(equality_resolution,[],[f49])).
% 3.47/1.00  
% 3.47/1.00  fof(f9,axiom,(
% 3.47/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f28,plain,(
% 3.47/1.00    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.47/1.00    inference(ennf_transformation,[],[f9])).
% 3.47/1.00  
% 3.47/1.00  fof(f29,plain,(
% 3.47/1.00    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.47/1.00    inference(flattening,[],[f28])).
% 3.47/1.00  
% 3.47/1.00  fof(f60,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f29])).
% 3.47/1.00  
% 3.47/1.00  fof(f3,axiom,(
% 3.47/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f20,plain,(
% 3.47/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.47/1.00    inference(ennf_transformation,[],[f3])).
% 3.47/1.00  
% 3.47/1.00  fof(f45,plain,(
% 3.47/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.47/1.00    inference(nnf_transformation,[],[f20])).
% 3.47/1.00  
% 3.47/1.00  fof(f54,plain,(
% 3.47/1.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f45])).
% 3.47/1.00  
% 3.47/1.00  fof(f8,axiom,(
% 3.47/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f26,plain,(
% 3.47/1.00    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.47/1.00    inference(ennf_transformation,[],[f8])).
% 3.47/1.00  
% 3.47/1.00  fof(f27,plain,(
% 3.47/1.00    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.47/1.00    inference(flattening,[],[f26])).
% 3.47/1.00  
% 3.47/1.00  fof(f59,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f27])).
% 3.47/1.00  
% 3.47/1.00  fof(f7,axiom,(
% 3.47/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f24,plain,(
% 3.47/1.00    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.47/1.00    inference(ennf_transformation,[],[f7])).
% 3.47/1.00  
% 3.47/1.00  fof(f25,plain,(
% 3.47/1.00    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.47/1.00    inference(flattening,[],[f24])).
% 3.47/1.00  
% 3.47/1.00  fof(f58,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f25])).
% 3.47/1.00  
% 3.47/1.00  fof(f12,axiom,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f32,plain,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/1.00    inference(ennf_transformation,[],[f12])).
% 3.47/1.00  
% 3.47/1.00  fof(f64,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f32])).
% 3.47/1.00  
% 3.47/1.00  fof(f80,plain,(
% 3.47/1.00    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f11,axiom,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f31,plain,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/1.00    inference(ennf_transformation,[],[f11])).
% 3.47/1.00  
% 3.47/1.00  fof(f63,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f31])).
% 3.47/1.00  
% 3.47/1.00  cnf(c_27,negated_conjecture,
% 3.47/1.00      ( r1_tarski(sK1,sK0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1289,plain,
% 3.47/1.00      ( r1_tarski(sK1,sK0) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_28,negated_conjecture,
% 3.47/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.47/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1288,plain,
% 3.47/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_25,plain,
% 3.47/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.47/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/1.00      | ~ v1_funct_1(X0)
% 3.47/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1290,plain,
% 3.47/1.00      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.47/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.47/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.47/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.47/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2381,plain,
% 3.47/1.00      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
% 3.47/1.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1288,c_1290]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_31,negated_conjecture,
% 3.47/1.00      ( v1_funct_1(sK2) ),
% 3.47/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_30,negated_conjecture,
% 3.47/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_29,negated_conjecture,
% 3.47/1.00      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1628,plain,
% 3.47/1.00      ( ~ v1_funct_2(sK2,X0,X0)
% 3.47/1.00      | ~ v3_funct_2(sK2,X0,X0)
% 3.47/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.47/1.00      | ~ v1_funct_1(sK2)
% 3.47/1.00      | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1630,plain,
% 3.47/1.00      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.47/1.00      | ~ v3_funct_2(sK2,sK0,sK0)
% 3.47/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.47/1.00      | ~ v1_funct_1(sK2)
% 3.47/1.00      | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_1628]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2809,plain,
% 3.47/1.00      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_2381,c_31,c_30,c_29,c_28,c_1630]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_21,plain,
% 3.47/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.47/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/1.00      | ~ v1_funct_1(X0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1294,plain,
% 3.47/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.47/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.47/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.47/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.47/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4060,plain,
% 3.47/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.47/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2809,c_1294]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_32,plain,
% 3.47/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_33,plain,
% 3.47/1.00      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_34,plain,
% 3.47/1.00      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_35,plain,
% 3.47/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4515,plain,
% 3.47/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_4060,c_32,c_33,c_34,c_35]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_13,plain,
% 3.47/1.00      ( v4_relat_1(X0,X1)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.47/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1298,plain,
% 3.47/1.00      ( v4_relat_1(X0,X1) = iProver_top
% 3.47/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4525,plain,
% 3.47/1.00      ( v4_relat_1(k2_funct_1(sK2),sK0) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_4515,c_1298]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_8,plain,
% 3.47/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1302,plain,
% 3.47/1.00      ( k7_relat_1(X0,X1) = X0
% 3.47/1.00      | v4_relat_1(X0,X1) != iProver_top
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4676,plain,
% 3.47/1.00      ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2)
% 3.47/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_4525,c_1302]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_6,plain,
% 3.47/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.47/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_92,plain,
% 3.47/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_94,plain,
% 3.47/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_92]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.47/1.00      | ~ v1_relat_1(X1)
% 3.47/1.00      | v1_relat_1(X0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1307,plain,
% 3.47/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.47/1.00      | v1_relat_1(X1) != iProver_top
% 3.47/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4520,plain,
% 3.47/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.47/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_4515,c_1307]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_5344,plain,
% 3.47/1.00      ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2) ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_4676,c_94,c_4520]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4924,plain,
% 3.47/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_4520,c_94]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_7,plain,
% 3.47/1.00      ( ~ v1_relat_1(X0)
% 3.47/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.47/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1303,plain,
% 3.47/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4930,plain,
% 3.47/1.00      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_4924,c_1303]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_5347,plain,
% 3.47/1.00      ( k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_5344,c_4930]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_16,plain,
% 3.47/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/1.00      | v2_funct_2(X0,X2)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/1.00      | ~ v1_funct_1(X0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_20,plain,
% 3.47/1.00      ( ~ v2_funct_2(X0,X1)
% 3.47/1.00      | ~ v5_relat_1(X0,X1)
% 3.47/1.00      | ~ v1_relat_1(X0)
% 3.47/1.00      | k2_relat_1(X0) = X1 ),
% 3.47/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_379,plain,
% 3.47/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/1.00      | ~ v5_relat_1(X3,X4)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/1.00      | ~ v1_funct_1(X0)
% 3.47/1.00      | ~ v1_relat_1(X3)
% 3.47/1.00      | X3 != X0
% 3.47/1.00      | X4 != X2
% 3.47/1.00      | k2_relat_1(X3) = X4 ),
% 3.47/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_380,plain,
% 3.47/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/1.00      | ~ v5_relat_1(X0,X2)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/1.00      | ~ v1_funct_1(X0)
% 3.47/1.00      | ~ v1_relat_1(X0)
% 3.47/1.00      | k2_relat_1(X0) = X2 ),
% 3.47/1.00      inference(unflattening,[status(thm)],[c_379]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_12,plain,
% 3.47/1.00      ( v5_relat_1(X0,X1)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.47/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_396,plain,
% 3.47/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/1.00      | ~ v1_funct_1(X0)
% 3.47/1.00      | ~ v1_relat_1(X0)
% 3.47/1.00      | k2_relat_1(X0) = X2 ),
% 3.47/1.00      inference(forward_subsumption_resolution,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_380,c_12]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1284,plain,
% 3.47/1.00      ( k2_relat_1(X0) = X1
% 3.47/1.00      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.47/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.47/1.00      | v1_funct_1(X0) != iProver_top
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4523,plain,
% 3.47/1.00      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 3.47/1.00      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 3.47/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.47/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_4515,c_1284]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_24,plain,
% 3.47/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.47/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/1.00      | ~ v1_funct_1(X0)
% 3.47/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.47/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1291,plain,
% 3.47/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.47/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.47/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.47/1.00      | v1_funct_1(X0) != iProver_top
% 3.47/1.00      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3092,plain,
% 3.47/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1288,c_1291]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3093,plain,
% 3.47/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.47/1.00      inference(light_normalisation,[status(thm)],[c_3092,c_2809]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_22,plain,
% 3.47/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.47/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.47/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/1.00      | ~ v1_funct_1(X0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1293,plain,
% 3.47/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.47/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.47/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.47/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.47/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4051,plain,
% 3.47/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 3.47/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1288,c_1293]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4052,plain,
% 3.47/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top
% 3.47/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.47/1.00      inference(light_normalisation,[status(thm)],[c_4051,c_2809]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_5564,plain,
% 3.47/1.00      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_4523,c_32,c_33,c_34,c_94,c_3093,c_4052,c_4520]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_17,plain,
% 3.47/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/1.00      | v2_funct_1(X0)
% 3.47/1.00      | ~ v1_funct_1(X0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1295,plain,
% 3.47/1.00      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.47/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.47/1.00      | v2_funct_1(X0) = iProver_top
% 3.47/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3364,plain,
% 3.47/1.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v2_funct_1(sK2) = iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1288,c_1295]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1579,plain,
% 3.47/1.00      ( ~ v3_funct_2(sK2,X0,X1)
% 3.47/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.47/1.00      | v2_funct_1(sK2)
% 3.47/1.00      | ~ v1_funct_1(sK2) ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1580,plain,
% 3.47/1.00      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 3.47/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.47/1.00      | v2_funct_1(sK2) = iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1579]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1582,plain,
% 3.47/1.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/1.00      | v2_funct_1(sK2) = iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_1580]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3570,plain,
% 3.47/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_3364,c_32,c_34,c_35,c_1582]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2,plain,
% 3.47/1.00      ( r1_tarski(X0,X0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1308,plain,
% 3.47/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_11,plain,
% 3.47/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.47/1.00      | ~ v2_funct_1(X1)
% 3.47/1.00      | ~ v1_funct_1(X1)
% 3.47/1.00      | ~ v1_relat_1(X1)
% 3.47/1.00      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1299,plain,
% 3.47/1.00      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
% 3.47/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.47/1.00      | v2_funct_1(X0) != iProver_top
% 3.47/1.00      | v1_funct_1(X0) != iProver_top
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3541,plain,
% 3.47/1.00      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
% 3.47/1.00      | v2_funct_1(X0) != iProver_top
% 3.47/1.00      | v1_funct_1(X0) != iProver_top
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1308,c_1299]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_6839,plain,
% 3.47/1.00      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top
% 3.47/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_3570,c_3541]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2305,plain,
% 3.47/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.47/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1288,c_1307]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1528,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/1.00      | v1_relat_1(X0)
% 3.47/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1703,plain,
% 3.47/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.47/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.47/1.00      | v1_relat_1(sK2) ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_1528]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1704,plain,
% 3.47/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.47/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1703]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2308,plain,
% 3.47/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_2305,c_35,c_94,c_1704]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4,plain,
% 3.47/1.00      ( v4_relat_1(X0,X1)
% 3.47/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.47/1.00      | ~ v1_relat_1(X0) ),
% 3.47/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1306,plain,
% 3.47/1.00      ( v4_relat_1(X0,X1) = iProver_top
% 3.47/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2681,plain,
% 3.47/1.00      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1308,c_1306]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2865,plain,
% 3.47/1.00      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2681,c_1302]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2972,plain,
% 3.47/1.00      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2308,c_2865]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2313,plain,
% 3.47/1.00      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2308,c_1303]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2979,plain,
% 3.47/1.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2972,c_2313]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1678,plain,
% 3.47/1.00      ( k2_relat_1(sK2) = sK0
% 3.47/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top
% 3.47/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1288,c_1284]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_93,plain,
% 3.47/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1679,plain,
% 3.47/1.00      ( ~ v3_funct_2(sK2,sK0,sK0)
% 3.47/1.00      | ~ v1_funct_1(sK2)
% 3.47/1.00      | ~ v1_relat_1(sK2)
% 3.47/1.00      | k2_relat_1(sK2) = sK0 ),
% 3.47/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1678]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2080,plain,
% 3.47/1.00      ( k2_relat_1(sK2) = sK0 ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_1678,c_31,c_29,c_28,c_93,c_1679,c_1703]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2980,plain,
% 3.47/1.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
% 3.47/1.00      inference(light_normalisation,[status(thm)],[c_2979,c_2080]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_6850,plain,
% 3.47/1.00      ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2)
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top
% 3.47/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.47/1.00      inference(light_normalisation,[status(thm)],[c_6839,c_2980]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_7013,plain,
% 3.47/1.00      ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2) ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_6850,c_32,c_35,c_94,c_1704]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9390,plain,
% 3.47/1.00      ( k1_relat_1(sK2) = sK0 ),
% 3.47/1.00      inference(light_normalisation,[status(thm)],[c_5347,c_5564,c_7013]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_10,plain,
% 3.47/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.47/1.00      | ~ v2_funct_1(X1)
% 3.47/1.00      | ~ v1_funct_1(X1)
% 3.47/1.00      | ~ v1_relat_1(X1)
% 3.47/1.00      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1300,plain,
% 3.47/1.00      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.47/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.47/1.00      | v2_funct_1(X0) != iProver_top
% 3.47/1.00      | v1_funct_1(X0) != iProver_top
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9422,plain,
% 3.47/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.47/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.47/1.00      | v2_funct_1(sK2) != iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top
% 3.47/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_9390,c_1300]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_10333,plain,
% 3.47/1.00      ( r1_tarski(X0,sK0) != iProver_top
% 3.47/1.00      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_9422,c_32,c_34,c_35,c_94,c_1582,c_1704]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_10334,plain,
% 3.47/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.47/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 3.47/1.00      inference(renaming,[status(thm)],[c_10333]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_10343,plain,
% 3.47/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1289,c_10334]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9,plain,
% 3.47/1.00      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.47/1.00      | ~ v1_funct_1(X1)
% 3.47/1.00      | ~ v1_relat_1(X1)
% 3.47/1.00      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1301,plain,
% 3.47/1.00      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.47/1.00      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.47/1.00      | v1_funct_1(X0) != iProver_top
% 3.47/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3103,plain,
% 3.47/1.00      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.47/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.47/1.00      | v1_funct_1(sK2) != iProver_top
% 3.47/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2080,c_1301]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3658,plain,
% 3.47/1.00      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.47/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_3103,c_32,c_35,c_94,c_1704]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3668,plain,
% 3.47/1.00      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1289,c_3658]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_15,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.47/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1296,plain,
% 3.47/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.47/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2526,plain,
% 3.47/1.00      ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1288,c_1296]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_26,negated_conjecture,
% 3.47/1.00      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.47/1.00      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.47/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2728,plain,
% 3.47/1.00      ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.47/1.00      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_2526,c_26]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2729,plain,
% 3.47/1.00      ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
% 3.47/1.00      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_2728,c_2526]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_14,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.47/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1297,plain,
% 3.47/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.47/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2531,plain,
% 3.47/1.00      ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_1288,c_1297]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2805,plain,
% 3.47/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
% 3.47/1.00      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_2729,c_2531]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(contradiction,plain,
% 3.47/1.00      ( $false ),
% 3.47/1.00      inference(minisat,[status(thm)],[c_10343,c_3668,c_2805]) ).
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/1.00  
% 3.47/1.00  ------                               Statistics
% 3.47/1.00  
% 3.47/1.00  ------ General
% 3.47/1.00  
% 3.47/1.00  abstr_ref_over_cycles:                  0
% 3.47/1.00  abstr_ref_under_cycles:                 0
% 3.47/1.00  gc_basic_clause_elim:                   0
% 3.47/1.00  forced_gc_time:                         0
% 3.47/1.00  parsing_time:                           0.011
% 3.47/1.00  unif_index_cands_time:                  0.
% 3.47/1.00  unif_index_add_time:                    0.
% 3.47/1.00  orderings_time:                         0.
% 3.47/1.00  out_proof_time:                         0.014
% 3.47/1.00  total_time:                             0.388
% 3.47/1.00  num_of_symbols:                         55
% 3.47/1.00  num_of_terms:                           14503
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing
% 3.47/1.00  
% 3.47/1.00  num_of_splits:                          0
% 3.47/1.00  num_of_split_atoms:                     0
% 3.47/1.00  num_of_reused_defs:                     0
% 3.47/1.00  num_eq_ax_congr_red:                    32
% 3.47/1.00  num_of_sem_filtered_clauses:            1
% 3.47/1.00  num_of_subtypes:                        0
% 3.47/1.00  monotx_restored_types:                  0
% 3.47/1.00  sat_num_of_epr_types:                   0
% 3.47/1.00  sat_num_of_non_cyclic_types:            0
% 3.47/1.00  sat_guarded_non_collapsed_types:        0
% 3.47/1.00  num_pure_diseq_elim:                    0
% 3.47/1.00  simp_replaced_by:                       0
% 3.47/1.00  res_preprocessed:                       142
% 3.47/1.00  prep_upred:                             0
% 3.47/1.00  prep_unflattend:                        10
% 3.47/1.00  smt_new_axioms:                         0
% 3.47/1.00  pred_elim_cands:                        8
% 3.47/1.00  pred_elim:                              2
% 3.47/1.00  pred_elim_cl:                           3
% 3.47/1.00  pred_elim_cycles:                       7
% 3.47/1.00  merged_defs:                            0
% 3.47/1.00  merged_defs_ncl:                        0
% 3.47/1.00  bin_hyper_res:                          0
% 3.47/1.00  prep_cycles:                            4
% 3.47/1.00  pred_elim_time:                         0.005
% 3.47/1.00  splitting_time:                         0.
% 3.47/1.00  sem_filter_time:                        0.
% 3.47/1.00  monotx_time:                            0.
% 3.47/1.00  subtype_inf_time:                       0.
% 3.47/1.00  
% 3.47/1.00  ------ Problem properties
% 3.47/1.00  
% 3.47/1.00  clauses:                                27
% 3.47/1.00  conjectures:                            6
% 3.47/1.00  epr:                                    6
% 3.47/1.00  horn:                                   27
% 3.47/1.00  ground:                                 6
% 3.47/1.00  unary:                                  7
% 3.47/1.00  binary:                                 5
% 3.47/1.00  lits:                                   80
% 3.47/1.00  lits_eq:                                12
% 3.47/1.00  fd_pure:                                0
% 3.47/1.00  fd_pseudo:                              0
% 3.47/1.00  fd_cond:                                0
% 3.47/1.00  fd_pseudo_cond:                         2
% 3.47/1.00  ac_symbols:                             0
% 3.47/1.00  
% 3.47/1.00  ------ Propositional Solver
% 3.47/1.00  
% 3.47/1.00  prop_solver_calls:                      27
% 3.47/1.00  prop_fast_solver_calls:                 1353
% 3.47/1.00  smt_solver_calls:                       0
% 3.47/1.00  smt_fast_solver_calls:                  0
% 3.47/1.00  prop_num_of_clauses:                    4539
% 3.47/1.00  prop_preprocess_simplified:             10293
% 3.47/1.00  prop_fo_subsumed:                       83
% 3.47/1.00  prop_solver_time:                       0.
% 3.47/1.00  smt_solver_time:                        0.
% 3.47/1.00  smt_fast_solver_time:                   0.
% 3.47/1.00  prop_fast_solver_time:                  0.
% 3.47/1.00  prop_unsat_core_time:                   0.
% 3.47/1.00  
% 3.47/1.00  ------ QBF
% 3.47/1.00  
% 3.47/1.00  qbf_q_res:                              0
% 3.47/1.00  qbf_num_tautologies:                    0
% 3.47/1.00  qbf_prep_cycles:                        0
% 3.47/1.00  
% 3.47/1.00  ------ BMC1
% 3.47/1.00  
% 3.47/1.00  bmc1_current_bound:                     -1
% 3.47/1.00  bmc1_last_solved_bound:                 -1
% 3.47/1.00  bmc1_unsat_core_size:                   -1
% 3.47/1.00  bmc1_unsat_core_parents_size:           -1
% 3.47/1.00  bmc1_merge_next_fun:                    0
% 3.47/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.47/1.00  
% 3.47/1.00  ------ Instantiation
% 3.47/1.00  
% 3.47/1.00  inst_num_of_clauses:                    1200
% 3.47/1.00  inst_num_in_passive:                    148
% 3.47/1.00  inst_num_in_active:                     607
% 3.47/1.00  inst_num_in_unprocessed:                445
% 3.47/1.00  inst_num_of_loops:                      630
% 3.47/1.00  inst_num_of_learning_restarts:          0
% 3.47/1.00  inst_num_moves_active_passive:          20
% 3.47/1.00  inst_lit_activity:                      0
% 3.47/1.00  inst_lit_activity_moves:                0
% 3.47/1.00  inst_num_tautologies:                   0
% 3.47/1.00  inst_num_prop_implied:                  0
% 3.47/1.00  inst_num_existing_simplified:           0
% 3.47/1.00  inst_num_eq_res_simplified:             0
% 3.47/1.00  inst_num_child_elim:                    0
% 3.47/1.00  inst_num_of_dismatching_blockings:      322
% 3.47/1.00  inst_num_of_non_proper_insts:           1062
% 3.47/1.00  inst_num_of_duplicates:                 0
% 3.47/1.00  inst_inst_num_from_inst_to_res:         0
% 3.47/1.00  inst_dismatching_checking_time:         0.
% 3.47/1.00  
% 3.47/1.00  ------ Resolution
% 3.47/1.00  
% 3.47/1.00  res_num_of_clauses:                     0
% 3.47/1.00  res_num_in_passive:                     0
% 3.47/1.00  res_num_in_active:                      0
% 3.47/1.00  res_num_of_loops:                       146
% 3.47/1.00  res_forward_subset_subsumed:            59
% 3.47/1.00  res_backward_subset_subsumed:           0
% 3.47/1.00  res_forward_subsumed:                   0
% 3.47/1.00  res_backward_subsumed:                  0
% 3.47/1.00  res_forward_subsumption_resolution:     1
% 3.47/1.00  res_backward_subsumption_resolution:    0
% 3.47/1.00  res_clause_to_clause_subsumption:       296
% 3.47/1.00  res_orphan_elimination:                 0
% 3.47/1.00  res_tautology_del:                      56
% 3.47/1.00  res_num_eq_res_simplified:              0
% 3.47/1.00  res_num_sel_changes:                    0
% 3.47/1.00  res_moves_from_active_to_pass:          0
% 3.47/1.00  
% 3.47/1.00  ------ Superposition
% 3.47/1.00  
% 3.47/1.00  sup_time_total:                         0.
% 3.47/1.00  sup_time_generating:                    0.
% 3.47/1.00  sup_time_sim_full:                      0.
% 3.47/1.00  sup_time_sim_immed:                     0.
% 3.47/1.00  
% 3.47/1.00  sup_num_of_clauses:                     154
% 3.47/1.00  sup_num_in_active:                      110
% 3.47/1.00  sup_num_in_passive:                     44
% 3.47/1.00  sup_num_of_loops:                       125
% 3.47/1.00  sup_fw_superposition:                   96
% 3.47/1.00  sup_bw_superposition:                   76
% 3.47/1.00  sup_immediate_simplified:               41
% 3.47/1.00  sup_given_eliminated:                   0
% 3.47/1.00  comparisons_done:                       0
% 3.47/1.00  comparisons_avoided:                    0
% 3.47/1.00  
% 3.47/1.00  ------ Simplifications
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  sim_fw_subset_subsumed:                 1
% 3.47/1.00  sim_bw_subset_subsumed:                 1
% 3.47/1.00  sim_fw_subsumed:                        5
% 3.47/1.00  sim_bw_subsumed:                        0
% 3.47/1.00  sim_fw_subsumption_res:                 1
% 3.47/1.00  sim_bw_subsumption_res:                 0
% 3.47/1.00  sim_tautology_del:                      1
% 3.47/1.00  sim_eq_tautology_del:                   11
% 3.47/1.00  sim_eq_res_simp:                        1
% 3.47/1.00  sim_fw_demodulated:                     3
% 3.47/1.00  sim_bw_demodulated:                     15
% 3.47/1.00  sim_light_normalised:                   43
% 3.47/1.00  sim_joinable_taut:                      0
% 3.47/1.00  sim_joinable_simp:                      0
% 3.47/1.00  sim_ac_normalised:                      0
% 3.47/1.00  sim_smt_subsumption:                    0
% 3.47/1.00  
%------------------------------------------------------------------------------
