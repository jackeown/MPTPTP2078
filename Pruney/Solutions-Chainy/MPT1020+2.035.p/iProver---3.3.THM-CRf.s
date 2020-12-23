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
% DateTime   : Thu Dec  3 12:07:11 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_39)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0))
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK2,X0,X0)
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f49,f48])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f89,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f77,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f92,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f85,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f83,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f88,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2297,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2309,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4028,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2297,c_2309])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2316,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4206,plain,
    ( k5_relat_1(sK1,k6_partfun1(X0)) = k8_relat_1(X0,sK1) ),
    inference(superposition,[status(thm)],[c_4028,c_2316])).

cnf(c_5261,plain,
    ( k5_relat_1(sK1,k1_xboole_0) = k8_relat_1(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_6,c_4206])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2310,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6587,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k2_relat_1(sK1)
    | k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5261,c_2310])).

cnf(c_5,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2766,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_6596,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0
    | k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6587,c_2766])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_499,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_2553,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2311,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3480,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2311])).

cnf(c_3481,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3480])).

cnf(c_6656,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_xboole_0)
    | k2_funct_1(sK1) = k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0
    | k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6596])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2301,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2308,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5616,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2297,c_2308])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_363,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_19])).

cnf(c_375,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_363,c_10])).

cnf(c_2293,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_4189,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2297,c_2293])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_509,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_510,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_512,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_34,c_31])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_375,c_512])).

cnf(c_590,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_592,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_4831,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4189,c_31,c_592])).

cnf(c_5622,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_5616,c_4831])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_186,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_23])).

cnf(c_187,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_186])).

cnf(c_2294,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_5768,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5622,c_2294])).

cnf(c_35,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_38,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5912,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5768,c_35,c_36,c_38])).

cnf(c_5913,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5912])).

cnf(c_5924,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2301,c_5913])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5925,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5924])).

cnf(c_5927,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5924,c_39,c_40,c_42])).

cnf(c_5928,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5927])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2302,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_528,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_529,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_531,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_529,c_34,c_33,c_31])).

cnf(c_2353,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2302,c_531])).

cnf(c_5931,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5928,c_2353])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2592,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2593,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2592])).

cnf(c_6016,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5931,c_42,c_2593])).

cnf(c_2300,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4188,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_2293])).

cnf(c_28,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_487,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_488,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_490,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_30,c_27])).

cnf(c_579,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_375,c_490])).

cnf(c_580,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_582,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_4542,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4188,c_27,c_582])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2314,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4546,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4542,c_2314])).

cnf(c_2550,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4557,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4546])).

cnf(c_5263,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4546,c_27,c_2550,c_4557])).

cnf(c_5264,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5263])).

cnf(c_6025,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6016,c_5264])).

cnf(c_6069,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6025])).

cnf(c_2298,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6834,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6069,c_2298])).

cnf(c_6840,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6834])).

cnf(c_7907,plain,
    ( k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1)
    | k2_relat_1(sK1) != k1_xboole_0
    | k2_funct_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6596,c_34,c_31,c_499,c_2553,c_3481,c_6656,c_6840])).

cnf(c_7908,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0
    | k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1) ),
    inference(renaming,[status(thm)],[c_7907])).

cnf(c_4,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2706,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2315,plain,
    ( k8_relat_1(k2_relat_1(X0),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3920,plain,
    ( k8_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3480,c_2315])).

cnf(c_3922,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3920,c_2706])).

cnf(c_4835,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4831,c_2314])).

cnf(c_2554,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2553])).

cnf(c_5380,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4835,c_38,c_2554])).

cnf(c_5381,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5380])).

cnf(c_6024,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6016,c_5381])).

cnf(c_6090,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6024])).

cnf(c_7909,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7908,c_6,c_2706,c_2766,c_3922,c_6090])).

cnf(c_7910,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7909])).

cnf(c_6030,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6016,c_2353])).

cnf(c_6073,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6069,c_6030])).

cnf(c_6092,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6090,c_6073])).

cnf(c_7913,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7910,c_6092])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2305,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3800,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2305])).

cnf(c_2307,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5596,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3800,c_2307])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7913,c_5596])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.20/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.99  
% 3.20/0.99  ------  iProver source info
% 3.20/0.99  
% 3.20/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.99  git: non_committed_changes: false
% 3.20/0.99  git: last_make_outside_of_git: false
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options
% 3.20/0.99  
% 3.20/0.99  --out_options                           all
% 3.20/0.99  --tptp_safe_out                         true
% 3.20/0.99  --problem_path                          ""
% 3.20/0.99  --include_path                          ""
% 3.20/0.99  --clausifier                            res/vclausify_rel
% 3.20/0.99  --clausifier_options                    --mode clausify
% 3.20/0.99  --stdin                                 false
% 3.20/0.99  --stats_out                             all
% 3.20/0.99  
% 3.20/0.99  ------ General Options
% 3.20/0.99  
% 3.20/0.99  --fof                                   false
% 3.20/0.99  --time_out_real                         305.
% 3.20/0.99  --time_out_virtual                      -1.
% 3.20/0.99  --symbol_type_check                     false
% 3.20/0.99  --clausify_out                          false
% 3.20/0.99  --sig_cnt_out                           false
% 3.20/0.99  --trig_cnt_out                          false
% 3.20/0.99  --trig_cnt_out_tolerance                1.
% 3.20/0.99  --trig_cnt_out_sk_spl                   false
% 3.20/0.99  --abstr_cl_out                          false
% 3.20/0.99  
% 3.20/0.99  ------ Global Options
% 3.20/0.99  
% 3.20/0.99  --schedule                              default
% 3.20/0.99  --add_important_lit                     false
% 3.20/0.99  --prop_solver_per_cl                    1000
% 3.20/0.99  --min_unsat_core                        false
% 3.20/0.99  --soft_assumptions                      false
% 3.20/0.99  --soft_lemma_size                       3
% 3.20/0.99  --prop_impl_unit_size                   0
% 3.20/0.99  --prop_impl_unit                        []
% 3.20/0.99  --share_sel_clauses                     true
% 3.20/0.99  --reset_solvers                         false
% 3.20/0.99  --bc_imp_inh                            [conj_cone]
% 3.20/0.99  --conj_cone_tolerance                   3.
% 3.20/0.99  --extra_neg_conj                        none
% 3.20/0.99  --large_theory_mode                     true
% 3.20/0.99  --prolific_symb_bound                   200
% 3.20/0.99  --lt_threshold                          2000
% 3.20/0.99  --clause_weak_htbl                      true
% 3.20/0.99  --gc_record_bc_elim                     false
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing Options
% 3.20/0.99  
% 3.20/0.99  --preprocessing_flag                    true
% 3.20/0.99  --time_out_prep_mult                    0.1
% 3.20/0.99  --splitting_mode                        input
% 3.20/0.99  --splitting_grd                         true
% 3.20/0.99  --splitting_cvd                         false
% 3.20/0.99  --splitting_cvd_svl                     false
% 3.20/0.99  --splitting_nvd                         32
% 3.20/0.99  --sub_typing                            true
% 3.20/0.99  --prep_gs_sim                           true
% 3.20/0.99  --prep_unflatten                        true
% 3.20/0.99  --prep_res_sim                          true
% 3.20/0.99  --prep_upred                            true
% 3.20/0.99  --prep_sem_filter                       exhaustive
% 3.20/0.99  --prep_sem_filter_out                   false
% 3.20/0.99  --pred_elim                             true
% 3.20/0.99  --res_sim_input                         true
% 3.20/0.99  --eq_ax_congr_red                       true
% 3.20/0.99  --pure_diseq_elim                       true
% 3.20/0.99  --brand_transform                       false
% 3.20/0.99  --non_eq_to_eq                          false
% 3.20/0.99  --prep_def_merge                        true
% 3.20/0.99  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         false
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     num_symb
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       true
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     false
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   []
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_full_bw                           [BwDemod]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  ------ Parsing...
% 3.20/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.99  ------ Proving...
% 3.20/0.99  ------ Problem Properties 
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  clauses                                 34
% 3.20/0.99  conjectures                             8
% 3.20/0.99  EPR                                     8
% 3.20/0.99  Horn                                    33
% 3.20/0.99  unary                                   20
% 3.20/0.99  binary                                  6
% 3.20/0.99  lits                                    80
% 3.20/0.99  lits eq                                 21
% 3.20/0.99  fd_pure                                 0
% 3.20/0.99  fd_pseudo                               0
% 3.20/0.99  fd_cond                                 2
% 3.20/0.99  fd_pseudo_cond                          4
% 3.20/0.99  AC symbols                              0
% 3.20/0.99  
% 3.20/0.99  ------ Schedule dynamic 5 is on 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  Current options:
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options
% 3.20/0.99  
% 3.20/0.99  --out_options                           all
% 3.20/0.99  --tptp_safe_out                         true
% 3.20/0.99  --problem_path                          ""
% 3.20/0.99  --include_path                          ""
% 3.20/0.99  --clausifier                            res/vclausify_rel
% 3.20/0.99  --clausifier_options                    --mode clausify
% 3.20/0.99  --stdin                                 false
% 3.20/0.99  --stats_out                             all
% 3.20/0.99  
% 3.20/0.99  ------ General Options
% 3.20/0.99  
% 3.20/0.99  --fof                                   false
% 3.20/0.99  --time_out_real                         305.
% 3.20/0.99  --time_out_virtual                      -1.
% 3.20/0.99  --symbol_type_check                     false
% 3.20/0.99  --clausify_out                          false
% 3.20/0.99  --sig_cnt_out                           false
% 3.20/0.99  --trig_cnt_out                          false
% 3.20/0.99  --trig_cnt_out_tolerance                1.
% 3.20/0.99  --trig_cnt_out_sk_spl                   false
% 3.20/0.99  --abstr_cl_out                          false
% 3.20/0.99  
% 3.20/0.99  ------ Global Options
% 3.20/0.99  
% 3.20/0.99  --schedule                              default
% 3.20/0.99  --add_important_lit                     false
% 3.20/0.99  --prop_solver_per_cl                    1000
% 3.20/0.99  --min_unsat_core                        false
% 3.20/0.99  --soft_assumptions                      false
% 3.20/0.99  --soft_lemma_size                       3
% 3.20/0.99  --prop_impl_unit_size                   0
% 3.20/0.99  --prop_impl_unit                        []
% 3.20/0.99  --share_sel_clauses                     true
% 3.20/0.99  --reset_solvers                         false
% 3.20/0.99  --bc_imp_inh                            [conj_cone]
% 3.20/0.99  --conj_cone_tolerance                   3.
% 3.20/0.99  --extra_neg_conj                        none
% 3.20/0.99  --large_theory_mode                     true
% 3.20/0.99  --prolific_symb_bound                   200
% 3.20/0.99  --lt_threshold                          2000
% 3.20/0.99  --clause_weak_htbl                      true
% 3.20/0.99  --gc_record_bc_elim                     false
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing Options
% 3.20/0.99  
% 3.20/0.99  --preprocessing_flag                    true
% 3.20/0.99  --time_out_prep_mult                    0.1
% 3.20/0.99  --splitting_mode                        input
% 3.20/0.99  --splitting_grd                         true
% 3.20/0.99  --splitting_cvd                         false
% 3.20/0.99  --splitting_cvd_svl                     false
% 3.20/0.99  --splitting_nvd                         32
% 3.20/0.99  --sub_typing                            true
% 3.20/0.99  --prep_gs_sim                           true
% 3.20/0.99  --prep_unflatten                        true
% 3.20/0.99  --prep_res_sim                          true
% 3.20/0.99  --prep_upred                            true
% 3.20/0.99  --prep_sem_filter                       exhaustive
% 3.20/0.99  --prep_sem_filter_out                   false
% 3.20/0.99  --pred_elim                             true
% 3.20/0.99  --res_sim_input                         true
% 3.20/0.99  --eq_ax_congr_red                       true
% 3.20/0.99  --pure_diseq_elim                       true
% 3.20/0.99  --brand_transform                       false
% 3.20/0.99  --non_eq_to_eq                          false
% 3.20/0.99  --prep_def_merge                        true
% 3.20/0.99  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         false
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     none
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       false
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     false
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   []
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_full_bw                           [BwDemod]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ Proving...
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS status Theorem for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  fof(f5,axiom,(
% 3.20/0.99    k6_relat_1(k1_xboole_0) = k1_xboole_0),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f57,plain,(
% 3.20/0.99    k6_relat_1(k1_xboole_0) = k1_xboole_0),
% 3.20/0.99    inference(cnf_transformation,[],[f5])).
% 3.20/0.99  
% 3.20/0.99  fof(f16,axiom,(
% 3.20/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f73,plain,(
% 3.20/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f16])).
% 3.20/0.99  
% 3.20/0.99  fof(f90,plain,(
% 3.20/0.99    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.20/0.99    inference(definition_unfolding,[],[f57,f73])).
% 3.20/0.99  
% 3.20/0.99  fof(f19,conjecture,(
% 3.20/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f20,negated_conjecture,(
% 3.20/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.20/0.99    inference(negated_conjecture,[],[f19])).
% 3.20/0.99  
% 3.20/0.99  fof(f44,plain,(
% 3.20/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.20/0.99    inference(ennf_transformation,[],[f20])).
% 3.20/0.99  
% 3.20/0.99  fof(f45,plain,(
% 3.20/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.20/0.99    inference(flattening,[],[f44])).
% 3.20/0.99  
% 3.20/0.99  fof(f49,plain,(
% 3.20/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f48,plain,(
% 3.20/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f50,plain,(
% 3.20/0.99    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.20/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f49,f48])).
% 3.20/0.99  
% 3.20/0.99  fof(f80,plain,(
% 3.20/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f8,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f29,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f8])).
% 3.20/0.99  
% 3.20/0.99  fof(f61,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f29])).
% 3.20/0.99  
% 3.20/0.99  fof(f1,axiom,(
% 3.20/0.99    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f23,plain,(
% 3.20/0.99    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 3.20/0.99    inference(ennf_transformation,[],[f1])).
% 3.20/0.99  
% 3.20/0.99  fof(f51,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f23])).
% 3.20/0.99  
% 3.20/0.99  fof(f87,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0)) | ~v1_relat_1(X1)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f51,f73])).
% 3.20/0.99  
% 3.20/0.99  fof(f7,axiom,(
% 3.20/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f27,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.20/0.99    inference(ennf_transformation,[],[f7])).
% 3.20/0.99  
% 3.20/0.99  fof(f28,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.20/0.99    inference(flattening,[],[f27])).
% 3.20/0.99  
% 3.20/0.99  fof(f60,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f28])).
% 3.20/0.99  
% 3.20/0.99  fof(f93,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f60,f73])).
% 3.20/0.99  
% 3.20/0.99  fof(f4,axiom,(
% 3.20/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f55,plain,(
% 3.20/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f4])).
% 3.20/0.99  
% 3.20/0.99  fof(f89,plain,(
% 3.20/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.20/0.99    inference(definition_unfolding,[],[f55,f73])).
% 3.20/0.99  
% 3.20/0.99  fof(f77,plain,(
% 3.20/0.99    v1_funct_1(sK1)),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f12,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f34,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f12])).
% 3.20/0.99  
% 3.20/0.99  fof(f35,plain,(
% 3.20/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(flattening,[],[f34])).
% 3.20/0.99  
% 3.20/0.99  fof(f67,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f35])).
% 3.20/0.99  
% 3.20/0.99  fof(f79,plain,(
% 3.20/0.99    v3_funct_2(sK1,sK0,sK0)),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f6,axiom,(
% 3.20/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f58,plain,(
% 3.20/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f6])).
% 3.20/0.99  
% 3.20/0.99  fof(f92,plain,(
% 3.20/0.99    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.20/0.99    inference(definition_unfolding,[],[f58,f73])).
% 3.20/0.99  
% 3.20/0.99  fof(f85,plain,(
% 3.20/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f10,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f31,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f10])).
% 3.20/0.99  
% 3.20/0.99  fof(f63,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f31])).
% 3.20/0.99  
% 3.20/0.99  fof(f9,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f22,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.20/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.20/0.99  
% 3.20/0.99  fof(f30,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f22])).
% 3.20/0.99  
% 3.20/0.99  fof(f62,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f30])).
% 3.20/0.99  
% 3.20/0.99  fof(f13,axiom,(
% 3.20/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f36,plain,(
% 3.20/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.20/0.99    inference(ennf_transformation,[],[f13])).
% 3.20/0.99  
% 3.20/0.99  fof(f37,plain,(
% 3.20/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.20/0.99    inference(flattening,[],[f36])).
% 3.20/0.99  
% 3.20/0.99  fof(f47,plain,(
% 3.20/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.20/0.99    inference(nnf_transformation,[],[f37])).
% 3.20/0.99  
% 3.20/0.99  fof(f69,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f47])).
% 3.20/0.99  
% 3.20/0.99  fof(f68,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f35])).
% 3.20/0.99  
% 3.20/0.99  fof(f18,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f42,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.20/0.99    inference(ennf_transformation,[],[f18])).
% 3.20/0.99  
% 3.20/0.99  fof(f43,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.20/0.99    inference(flattening,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f76,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f43])).
% 3.20/0.99  
% 3.20/0.99  fof(f17,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f40,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.20/0.99    inference(ennf_transformation,[],[f17])).
% 3.20/0.99  
% 3.20/0.99  fof(f41,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.20/0.99    inference(flattening,[],[f40])).
% 3.20/0.99  
% 3.20/0.99  fof(f74,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f41])).
% 3.20/0.99  
% 3.20/0.99  fof(f78,plain,(
% 3.20/0.99    v1_funct_2(sK1,sK0,sK0)),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f81,plain,(
% 3.20/0.99    v1_funct_1(sK2)),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f82,plain,(
% 3.20/0.99    v1_funct_2(sK2,sK0,sK0)),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f84,plain,(
% 3.20/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f86,plain,(
% 3.20/0.99    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f15,axiom,(
% 3.20/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f38,plain,(
% 3.20/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.20/0.99    inference(ennf_transformation,[],[f15])).
% 3.20/0.99  
% 3.20/0.99  fof(f39,plain,(
% 3.20/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.20/0.99    inference(flattening,[],[f38])).
% 3.20/0.99  
% 3.20/0.99  fof(f72,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f39])).
% 3.20/0.99  
% 3.20/0.99  fof(f11,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f32,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.20/0.99    inference(ennf_transformation,[],[f11])).
% 3.20/0.99  
% 3.20/0.99  fof(f33,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(flattening,[],[f32])).
% 3.20/0.99  
% 3.20/0.99  fof(f46,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(nnf_transformation,[],[f33])).
% 3.20/0.99  
% 3.20/0.99  fof(f65,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f46])).
% 3.20/0.99  
% 3.20/0.99  fof(f94,plain,(
% 3.20/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(equality_resolution,[],[f65])).
% 3.20/0.99  
% 3.20/0.99  fof(f83,plain,(
% 3.20/0.99    v3_funct_2(sK2,sK0,sK0)),
% 3.20/0.99    inference(cnf_transformation,[],[f50])).
% 3.20/0.99  
% 3.20/0.99  fof(f3,axiom,(
% 3.20/0.99    ! [X0] : (v1_relat_1(X0) => ((k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f25,plain,(
% 3.20/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.20/0.99    inference(ennf_transformation,[],[f3])).
% 3.20/0.99  
% 3.20/0.99  fof(f26,plain,(
% 3.20/0.99    ! [X0] : (k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.20/0.99    inference(flattening,[],[f25])).
% 3.20/0.99  
% 3.20/0.99  fof(f54,plain,(
% 3.20/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f26])).
% 3.20/0.99  
% 3.20/0.99  fof(f56,plain,(
% 3.20/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f4])).
% 3.20/0.99  
% 3.20/0.99  fof(f88,plain,(
% 3.20/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.20/0.99    inference(definition_unfolding,[],[f56,f73])).
% 3.20/0.99  
% 3.20/0.99  fof(f2,axiom,(
% 3.20/0.99    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f24,plain,(
% 3.20/0.99    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 3.20/0.99    inference(ennf_transformation,[],[f2])).
% 3.20/0.99  
% 3.20/0.99  fof(f52,plain,(
% 3.20/0.99    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f24])).
% 3.20/0.99  
% 3.20/0.99  fof(f14,axiom,(
% 3.20/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f21,plain,(
% 3.20/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.20/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.20/0.99  
% 3.20/0.99  fof(f71,plain,(
% 3.20/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f21])).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6,plain,
% 3.20/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_31,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2297,plain,
% 3.20/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | v1_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2309,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.20/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4028,plain,
% 3.20/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2297,c_2309]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_0,plain,
% 3.20/0.99      ( ~ v1_relat_1(X0)
% 3.20/0.99      | k5_relat_1(X0,k6_partfun1(X1)) = k8_relat_1(X1,X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2316,plain,
% 3.20/0.99      ( k5_relat_1(X0,k6_partfun1(X1)) = k8_relat_1(X1,X0)
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4206,plain,
% 3.20/0.99      ( k5_relat_1(sK1,k6_partfun1(X0)) = k8_relat_1(X0,sK1) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4028,c_2316]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5261,plain,
% 3.20/0.99      ( k5_relat_1(sK1,k1_xboole_0) = k8_relat_1(k1_xboole_0,sK1) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_6,c_4206]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9,plain,
% 3.20/0.99      ( ~ v1_funct_1(X0)
% 3.20/0.99      | ~ v1_funct_1(X1)
% 3.20/0.99      | ~ v2_funct_1(X1)
% 3.20/0.99      | ~ v1_relat_1(X0)
% 3.20/0.99      | ~ v1_relat_1(X1)
% 3.20/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.20/0.99      | k2_funct_1(X1) = X0
% 3.20/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2310,plain,
% 3.20/0.99      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.20/0.99      | k2_funct_1(X0) = X1
% 3.20/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.20/0.99      | v1_funct_1(X1) != iProver_top
% 3.20/0.99      | v1_funct_1(X0) != iProver_top
% 3.20/0.99      | v2_funct_1(X0) != iProver_top
% 3.20/0.99      | v1_relat_1(X1) != iProver_top
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6587,plain,
% 3.20/0.99      ( k2_funct_1(sK1) = k1_xboole_0
% 3.20/0.99      | k1_relat_1(k1_xboole_0) != k2_relat_1(sK1)
% 3.20/0.99      | k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1)
% 3.20/0.99      | v1_funct_1(sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.20/0.99      | v2_funct_1(sK1) != iProver_top
% 3.20/0.99      | v1_relat_1(sK1) != iProver_top
% 3.20/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_5261,c_2310]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5,plain,
% 3.20/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2766,plain,
% 3.20/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6596,plain,
% 3.20/0.99      ( k2_funct_1(sK1) = k1_xboole_0
% 3.20/0.99      | k2_relat_1(sK1) != k1_xboole_0
% 3.20/0.99      | k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1)
% 3.20/0.99      | v1_funct_1(sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.20/0.99      | v2_funct_1(sK1) != iProver_top
% 3.20/0.99      | v1_relat_1(sK1) != iProver_top
% 3.20/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_6587,c_2766]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_34,negated_conjecture,
% 3.20/0.99      ( v1_funct_1(sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_16,plain,
% 3.20/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | v2_funct_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_32,negated_conjecture,
% 3.20/0.99      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_498,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | v2_funct_1(X0)
% 3.20/0.99      | sK1 != X0
% 3.20/0.99      | sK0 != X2
% 3.20/0.99      | sK0 != X1 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_499,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.99      | ~ v1_funct_1(sK1)
% 3.20/0.99      | v2_funct_1(sK1) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_498]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2553,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.99      | v1_relat_1(sK1) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8,plain,
% 3.20/0.99      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2311,plain,
% 3.20/0.99      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3480,plain,
% 3.20/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_6,c_2311]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3481,plain,
% 3.20/0.99      ( v1_relat_1(k1_xboole_0) ),
% 3.20/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3480]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6656,plain,
% 3.20/0.99      ( ~ v1_funct_1(sK1)
% 3.20/0.99      | ~ v1_funct_1(k1_xboole_0)
% 3.20/0.99      | ~ v2_funct_1(sK1)
% 3.20/0.99      | ~ v1_relat_1(sK1)
% 3.20/0.99      | ~ v1_relat_1(k1_xboole_0)
% 3.20/0.99      | k2_funct_1(sK1) = k1_xboole_0
% 3.20/0.99      | k2_relat_1(sK1) != k1_xboole_0
% 3.20/0.99      | k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1) ),
% 3.20/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6596]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_26,negated_conjecture,
% 3.20/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2301,plain,
% 3.20/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_12,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2308,plain,
% 3.20/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5616,plain,
% 3.20/0.99      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2297,c_2308]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_11,plain,
% 3.20/0.99      ( v5_relat_1(X0,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_19,plain,
% 3.20/0.99      ( ~ v2_funct_2(X0,X1)
% 3.20/0.99      | ~ v5_relat_1(X0,X1)
% 3.20/0.99      | ~ v1_relat_1(X0)
% 3.20/0.99      | k2_relat_1(X0) = X1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_363,plain,
% 3.20/0.99      ( ~ v2_funct_2(X0,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.20/0.99      | ~ v1_relat_1(X0)
% 3.20/0.99      | k2_relat_1(X0) = X1 ),
% 3.20/0.99      inference(resolution,[status(thm)],[c_11,c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_375,plain,
% 3.20/0.99      ( ~ v2_funct_2(X0,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.20/0.99      | k2_relat_1(X0) = X1 ),
% 3.20/0.99      inference(forward_subsumption_resolution,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_363,c_10]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2293,plain,
% 3.20/0.99      ( k2_relat_1(X0) = X1
% 3.20/0.99      | v2_funct_2(X0,X1) != iProver_top
% 3.20/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4189,plain,
% 3.20/0.99      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2297,c_2293]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_15,plain,
% 3.20/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.20/0.99      | v2_funct_2(X0,X2)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ v1_funct_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_509,plain,
% 3.20/0.99      ( v2_funct_2(X0,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | sK1 != X0
% 3.20/0.99      | sK0 != X1
% 3.20/0.99      | sK0 != X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_510,plain,
% 3.20/0.99      ( v2_funct_2(sK1,sK0)
% 3.20/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.99      | ~ v1_funct_1(sK1) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_509]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_512,plain,
% 3.20/0.99      ( v2_funct_2(sK1,sK0) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_510,c_34,c_31]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_589,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k2_relat_1(X0) = X2
% 3.20/0.99      | sK1 != X0
% 3.20/0.99      | sK0 != X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_375,c_512]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_590,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.20/0.99      | k2_relat_1(sK1) = sK0 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_589]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_592,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.99      | k2_relat_1(sK1) = sK0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_590]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4831,plain,
% 3.20/0.99      ( k2_relat_1(sK1) = sK0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4189,c_31,c_592]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5622,plain,
% 3.20/0.99      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_5616,c_4831]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_24,plain,
% 3.20/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.20/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.20/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.20/0.99      | ~ v1_funct_1(X2)
% 3.20/0.99      | ~ v1_funct_1(X3)
% 3.20/0.99      | ~ v2_funct_1(X2)
% 3.20/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.20/0.99      | k2_funct_1(X2) = X3
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_23,plain,
% 3.20/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.20/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.20/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.20/0.99      | ~ v1_funct_1(X2)
% 3.20/0.99      | ~ v1_funct_1(X3)
% 3.20/0.99      | v2_funct_1(X2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_186,plain,
% 3.20/0.99      ( ~ v1_funct_1(X3)
% 3.20/0.99      | ~ v1_funct_1(X2)
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.20/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.20/0.99      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.20/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.20/0.99      | k2_funct_1(X2) = X3
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_24,c_23]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_187,plain,
% 3.20/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.20/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.20/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.20/0.99      | ~ v1_funct_1(X2)
% 3.20/0.99      | ~ v1_funct_1(X3)
% 3.20/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.20/0.99      | k2_funct_1(X2) = X3
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1 ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_186]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2294,plain,
% 3.20/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.20/0.99      | k2_funct_1(X2) = X3
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.20/0.99      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.20/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.20/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.20/0.99      | v1_funct_1(X2) != iProver_top
% 3.20/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5768,plain,
% 3.20/0.99      ( k2_funct_1(sK1) = X0
% 3.20/0.99      | sK0 = k1_xboole_0
% 3.20/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.20/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.20/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.20/0.99      | v1_funct_1(X0) != iProver_top
% 3.20/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_5622,c_2294]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_35,plain,
% 3.20/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_33,negated_conjecture,
% 3.20/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_36,plain,
% 3.20/0.99      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_38,plain,
% 3.20/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5912,plain,
% 3.20/0.99      ( v1_funct_1(X0) != iProver_top
% 3.20/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.20/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.20/0.99      | sK0 = k1_xboole_0
% 3.20/0.99      | k2_funct_1(sK1) = X0
% 3.20/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_5768,c_35,c_36,c_38]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5913,plain,
% 3.20/0.99      ( k2_funct_1(sK1) = X0
% 3.20/0.99      | sK0 = k1_xboole_0
% 3.20/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.20/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.20/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_5912]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5924,plain,
% 3.20/0.99      ( k2_funct_1(sK1) = sK2
% 3.20/0.99      | sK0 = k1_xboole_0
% 3.20/0.99      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2301,c_5913]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_30,negated_conjecture,
% 3.20/0.99      ( v1_funct_1(sK2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_29,negated_conjecture,
% 3.20/0.99      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_27,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5925,plain,
% 3.20/0.99      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | k2_funct_1(sK1) = sK2
% 3.20/0.99      | sK0 = k1_xboole_0 ),
% 3.20/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5924]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5927,plain,
% 3.20/0.99      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_5924,c_39,c_40,c_42]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5928,plain,
% 3.20/0.99      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_5927]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_25,negated_conjecture,
% 3.20/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2302,plain,
% 3.20/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_21,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_528,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.20/0.99      | sK1 != X0
% 3.20/0.99      | sK0 != X1 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_529,plain,
% 3.20/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.20/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.99      | ~ v1_funct_1(sK1)
% 3.20/0.99      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_528]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_531,plain,
% 3.20/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_529,c_34,c_33,c_31]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2353,plain,
% 3.20/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_2302,c_531]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5931,plain,
% 3.20/0.99      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_5928,c_2353]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_42,plain,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_13,plain,
% 3.20/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2592,plain,
% 3.20/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2593,plain,
% 3.20/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_2592]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6016,plain,
% 3.20/0.99      ( sK0 = k1_xboole_0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_5931,c_42,c_2593]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2300,plain,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4188,plain,
% 3.20/0.99      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2300,c_2293]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_28,negated_conjecture,
% 3.20/0.99      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_487,plain,
% 3.20/0.99      ( v2_funct_2(X0,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | sK2 != X0
% 3.20/0.99      | sK0 != X1
% 3.20/0.99      | sK0 != X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_488,plain,
% 3.20/0.99      ( v2_funct_2(sK2,sK0)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.99      | ~ v1_funct_1(sK2) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_487]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_490,plain,
% 3.20/0.99      ( v2_funct_2(sK2,sK0) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_488,c_30,c_27]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_579,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k2_relat_1(X0) = X2
% 3.20/0.99      | sK2 != X0
% 3.20/0.99      | sK0 != X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_375,c_490]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_580,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.20/0.99      | k2_relat_1(sK2) = sK0 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_579]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_582,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.99      | k2_relat_1(sK2) = sK0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_580]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4542,plain,
% 3.20/0.99      ( k2_relat_1(sK2) = sK0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4188,c_27,c_582]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2,plain,
% 3.20/0.99      ( ~ v1_relat_1(X0)
% 3.20/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.20/0.99      | k1_xboole_0 = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2314,plain,
% 3.20/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4546,plain,
% 3.20/0.99      ( sK2 = k1_xboole_0
% 3.20/0.99      | sK0 != k1_xboole_0
% 3.20/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4542,c_2314]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2550,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.99      | v1_relat_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4557,plain,
% 3.20/0.99      ( ~ v1_relat_1(sK2) | sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.20/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4546]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5263,plain,
% 3.20/0.99      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4546,c_27,c_2550,c_4557]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5264,plain,
% 3.20/0.99      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_5263]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6025,plain,
% 3.20/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_6016,c_5264]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6069,plain,
% 3.20/0.99      ( sK2 = k1_xboole_0 ),
% 3.20/0.99      inference(equality_resolution_simp,[status(thm)],[c_6025]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2298,plain,
% 3.20/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6834,plain,
% 3.20/0.99      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_6069,c_2298]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6840,plain,
% 3.20/0.99      ( v1_funct_1(k1_xboole_0) ),
% 3.20/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6834]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7907,plain,
% 3.20/0.99      ( k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1)
% 3.20/0.99      | k2_relat_1(sK1) != k1_xboole_0
% 3.20/0.99      | k2_funct_1(sK1) = k1_xboole_0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_6596,c_34,c_31,c_499,c_2553,c_3481,c_6656,c_6840]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7908,plain,
% 3.20/0.99      ( k2_funct_1(sK1) = k1_xboole_0
% 3.20/0.99      | k2_relat_1(sK1) != k1_xboole_0
% 3.20/0.99      | k6_partfun1(k1_relat_1(sK1)) != k8_relat_1(k1_xboole_0,sK1) ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_7907]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4,plain,
% 3.20/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2706,plain,
% 3.20/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1,plain,
% 3.20/0.99      ( ~ v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2315,plain,
% 3.20/0.99      ( k8_relat_1(k2_relat_1(X0),X0) = X0
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3920,plain,
% 3.20/0.99      ( k8_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3480,c_2315]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3922,plain,
% 3.20/0.99      ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3920,c_2706]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4835,plain,
% 3.20/0.99      ( sK1 = k1_xboole_0
% 3.20/0.99      | sK0 != k1_xboole_0
% 3.20/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4831,c_2314]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2554,plain,
% 3.20/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.20/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_2553]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5380,plain,
% 3.20/0.99      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4835,c_38,c_2554]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5381,plain,
% 3.20/0.99      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_5380]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6024,plain,
% 3.20/0.99      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_6016,c_5381]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6090,plain,
% 3.20/0.99      ( sK1 = k1_xboole_0 ),
% 3.20/0.99      inference(equality_resolution_simp,[status(thm)],[c_6024]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7909,plain,
% 3.20/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 3.20/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.20/0.99      inference(light_normalisation,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_7908,c_6,c_2706,c_2766,c_3922,c_6090]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7910,plain,
% 3.20/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.20/0.99      inference(equality_resolution_simp,[status(thm)],[c_7909]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6030,plain,
% 3.20/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_6016,c_2353]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6073,plain,
% 3.20/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_6069,c_6030]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6092,plain,
% 3.20/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_6090,c_6073]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7913,plain,
% 3.20/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_7910,c_6092]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_20,plain,
% 3.20/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2305,plain,
% 3.20/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3800,plain,
% 3.20/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_6,c_2305]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2307,plain,
% 3.20/0.99      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5596,plain,
% 3.20/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3800,c_2307]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(contradiction,plain,
% 3.20/0.99      ( $false ),
% 3.20/0.99      inference(minisat,[status(thm)],[c_7913,c_5596]) ).
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  ------                               Statistics
% 3.20/0.99  
% 3.20/0.99  ------ General
% 3.20/0.99  
% 3.20/0.99  abstr_ref_over_cycles:                  0
% 3.20/0.99  abstr_ref_under_cycles:                 0
% 3.20/0.99  gc_basic_clause_elim:                   0
% 3.20/0.99  forced_gc_time:                         0
% 3.20/0.99  parsing_time:                           0.008
% 3.20/0.99  unif_index_cands_time:                  0.
% 3.20/0.99  unif_index_add_time:                    0.
% 3.20/0.99  orderings_time:                         0.
% 3.20/0.99  out_proof_time:                         0.013
% 3.20/0.99  total_time:                             0.26
% 3.20/0.99  num_of_symbols:                         55
% 3.20/0.99  num_of_terms:                           7491
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing
% 3.20/0.99  
% 3.20/0.99  num_of_splits:                          0
% 3.20/0.99  num_of_split_atoms:                     0
% 3.20/0.99  num_of_reused_defs:                     0
% 3.20/0.99  num_eq_ax_congr_red:                    18
% 3.20/0.99  num_of_sem_filtered_clauses:            1
% 3.20/0.99  num_of_subtypes:                        0
% 3.20/0.99  monotx_restored_types:                  0
% 3.20/0.99  sat_num_of_epr_types:                   0
% 3.20/0.99  sat_num_of_non_cyclic_types:            0
% 3.20/0.99  sat_guarded_non_collapsed_types:        0
% 3.20/0.99  num_pure_diseq_elim:                    0
% 3.20/0.99  simp_replaced_by:                       0
% 3.20/0.99  res_preprocessed:                       175
% 3.20/0.99  prep_upred:                             0
% 3.20/0.99  prep_unflattend:                        94
% 3.20/0.99  smt_new_axioms:                         0
% 3.20/0.99  pred_elim_cands:                        7
% 3.20/0.99  pred_elim:                              2
% 3.20/0.99  pred_elim_cl:                           0
% 3.20/0.99  pred_elim_cycles:                       9
% 3.20/0.99  merged_defs:                            0
% 3.20/0.99  merged_defs_ncl:                        0
% 3.20/0.99  bin_hyper_res:                          0
% 3.20/0.99  prep_cycles:                            4
% 3.20/0.99  pred_elim_time:                         0.026
% 3.20/0.99  splitting_time:                         0.
% 3.20/0.99  sem_filter_time:                        0.
% 3.20/0.99  monotx_time:                            0.
% 3.20/0.99  subtype_inf_time:                       0.
% 3.20/0.99  
% 3.20/0.99  ------ Problem properties
% 3.20/0.99  
% 3.20/0.99  clauses:                                34
% 3.20/0.99  conjectures:                            8
% 3.20/0.99  epr:                                    8
% 3.20/0.99  horn:                                   33
% 3.20/0.99  ground:                                 15
% 3.20/0.99  unary:                                  20
% 3.20/0.99  binary:                                 6
% 3.20/0.99  lits:                                   80
% 3.20/0.99  lits_eq:                                21
% 3.20/0.99  fd_pure:                                0
% 3.20/0.99  fd_pseudo:                              0
% 3.20/0.99  fd_cond:                                2
% 3.20/0.99  fd_pseudo_cond:                         4
% 3.20/0.99  ac_symbols:                             0
% 3.20/0.99  
% 3.20/0.99  ------ Propositional Solver
% 3.20/0.99  
% 3.20/0.99  prop_solver_calls:                      27
% 3.20/0.99  prop_fast_solver_calls:                 1468
% 3.20/0.99  smt_solver_calls:                       0
% 3.20/0.99  smt_fast_solver_calls:                  0
% 3.20/0.99  prop_num_of_clauses:                    2956
% 3.20/0.99  prop_preprocess_simplified:             9716
% 3.20/0.99  prop_fo_subsumed:                       60
% 3.20/0.99  prop_solver_time:                       0.
% 3.20/0.99  smt_solver_time:                        0.
% 3.20/0.99  smt_fast_solver_time:                   0.
% 3.20/1.00  prop_fast_solver_time:                  0.
% 3.20/1.00  prop_unsat_core_time:                   0.
% 3.20/1.00  
% 3.20/1.00  ------ QBF
% 3.20/1.00  
% 3.20/1.00  qbf_q_res:                              0
% 3.20/1.00  qbf_num_tautologies:                    0
% 3.20/1.00  qbf_prep_cycles:                        0
% 3.20/1.00  
% 3.20/1.00  ------ BMC1
% 3.20/1.00  
% 3.20/1.00  bmc1_current_bound:                     -1
% 3.20/1.00  bmc1_last_solved_bound:                 -1
% 3.20/1.00  bmc1_unsat_core_size:                   -1
% 3.20/1.00  bmc1_unsat_core_parents_size:           -1
% 3.20/1.00  bmc1_merge_next_fun:                    0
% 3.20/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.20/1.00  
% 3.20/1.00  ------ Instantiation
% 3.20/1.00  
% 3.20/1.00  inst_num_of_clauses:                    927
% 3.20/1.00  inst_num_in_passive:                    525
% 3.20/1.00  inst_num_in_active:                     389
% 3.20/1.00  inst_num_in_unprocessed:                13
% 3.20/1.00  inst_num_of_loops:                      390
% 3.20/1.00  inst_num_of_learning_restarts:          0
% 3.20/1.00  inst_num_moves_active_passive:          0
% 3.20/1.00  inst_lit_activity:                      0
% 3.20/1.00  inst_lit_activity_moves:                0
% 3.20/1.00  inst_num_tautologies:                   0
% 3.20/1.00  inst_num_prop_implied:                  0
% 3.20/1.00  inst_num_existing_simplified:           0
% 3.20/1.00  inst_num_eq_res_simplified:             0
% 3.20/1.00  inst_num_child_elim:                    0
% 3.20/1.00  inst_num_of_dismatching_blockings:      20
% 3.20/1.00  inst_num_of_non_proper_insts:           708
% 3.20/1.00  inst_num_of_duplicates:                 0
% 3.20/1.00  inst_inst_num_from_inst_to_res:         0
% 3.20/1.00  inst_dismatching_checking_time:         0.
% 3.20/1.00  
% 3.20/1.00  ------ Resolution
% 3.20/1.00  
% 3.20/1.00  res_num_of_clauses:                     0
% 3.20/1.00  res_num_in_passive:                     0
% 3.20/1.00  res_num_in_active:                      0
% 3.20/1.00  res_num_of_loops:                       179
% 3.20/1.00  res_forward_subset_subsumed:            38
% 3.20/1.00  res_backward_subset_subsumed:           0
% 3.20/1.00  res_forward_subsumed:                   0
% 3.20/1.00  res_backward_subsumed:                  0
% 3.20/1.00  res_forward_subsumption_resolution:     4
% 3.20/1.00  res_backward_subsumption_resolution:    0
% 3.20/1.00  res_clause_to_clause_subsumption:       200
% 3.20/1.00  res_orphan_elimination:                 0
% 3.20/1.00  res_tautology_del:                      40
% 3.20/1.00  res_num_eq_res_simplified:              0
% 3.20/1.00  res_num_sel_changes:                    0
% 3.20/1.00  res_moves_from_active_to_pass:          0
% 3.20/1.00  
% 3.20/1.00  ------ Superposition
% 3.20/1.00  
% 3.20/1.00  sup_time_total:                         0.
% 3.20/1.00  sup_time_generating:                    0.
% 3.20/1.00  sup_time_sim_full:                      0.
% 3.20/1.00  sup_time_sim_immed:                     0.
% 3.20/1.00  
% 3.20/1.00  sup_num_of_clauses:                     51
% 3.20/1.00  sup_num_in_active:                      39
% 3.20/1.00  sup_num_in_passive:                     12
% 3.20/1.00  sup_num_of_loops:                       77
% 3.20/1.00  sup_fw_superposition:                   50
% 3.20/1.00  sup_bw_superposition:                   12
% 3.20/1.00  sup_immediate_simplified:               48
% 3.20/1.00  sup_given_eliminated:                   0
% 3.20/1.00  comparisons_done:                       0
% 3.20/1.00  comparisons_avoided:                    3
% 3.20/1.00  
% 3.20/1.00  ------ Simplifications
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  sim_fw_subset_subsumed:                 7
% 3.20/1.00  sim_bw_subset_subsumed:                 4
% 3.20/1.00  sim_fw_subsumed:                        2
% 3.20/1.00  sim_bw_subsumed:                        0
% 3.20/1.00  sim_fw_subsumption_res:                 0
% 3.20/1.00  sim_bw_subsumption_res:                 0
% 3.20/1.00  sim_tautology_del:                      0
% 3.20/1.00  sim_eq_tautology_del:                   4
% 3.20/1.00  sim_eq_res_simp:                        5
% 3.20/1.00  sim_fw_demodulated:                     0
% 3.20/1.00  sim_bw_demodulated:                     53
% 3.20/1.00  sim_light_normalised:                   28
% 3.20/1.00  sim_joinable_taut:                      0
% 3.20/1.00  sim_joinable_simp:                      0
% 3.20/1.00  sim_ac_normalised:                      0
% 3.20/1.00  sim_smt_subsumption:                    0
% 3.20/1.00  
%------------------------------------------------------------------------------
