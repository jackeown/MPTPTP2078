%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:06 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_43)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0(X0))
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f49])).

fof(f60,plain,(
    ! [X0] : v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK3,X0,X0)
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
          ( ~ r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2))
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v3_funct_2(X2,sK1,sK1)
          & v1_funct_2(X2,sK1,sK1)
          & v1_funct_1(X2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK2,sK1,sK1)
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK3,sK1,sK1)
    & v1_funct_2(sK3,sK1,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f55,f54])).

fof(f95,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f71,f80])).

fof(f5,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f97,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f63,f80,f80])).

cnf(c_2,plain,
    ( v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1400,plain,
    ( v1_xboole_0(sK0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1946,plain,
    ( v1_xboole_0(sK0(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1402,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1944,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1402])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1401,plain,
    ( ~ v1_xboole_0(X0_52)
    | ~ v1_xboole_0(X1_52)
    | X1_52 = X0_52 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1945,plain,
    ( X0_52 = X1_52
    | v1_xboole_0(X1_52) != iProver_top
    | v1_xboole_0(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1401])).

cnf(c_3106,plain,
    ( k1_xboole_0 = X0_52
    | v1_xboole_0(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_1945])).

cnf(c_3571,plain,
    ( sK0(X0_54) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1946,c_3106])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1399,plain,
    ( m1_subset_1(sK0(X0_54),k1_zfmisc_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1947,plain,
    ( m1_subset_1(sK0(X0_54),k1_zfmisc_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1399])).

cnf(c_3643,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3571,c_1947])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1391,plain,
    ( r2_relset_1(X0_52,X1_52,X2_52,X2_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1954,plain,
    ( r2_relset_1(X0_52,X1_52,X2_52,X2_52) = iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_4700,plain,
    ( r2_relset_1(X0_52,X1_52,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3643,c_1954])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1382,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1963,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1378,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1967,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1378])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_405,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_19])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_417,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_405,c_7])).

cnf(c_1374,plain,
    ( ~ v2_funct_2(X0_52,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
    | k2_relat_1(X0_52) = X1_52 ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(c_1971,plain,
    ( k2_relat_1(X0_52) = X1_52
    | v2_funct_2(X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1374])).

cnf(c_5881,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_2(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_1971])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_36,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_527,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_528,plain,
    ( v2_funct_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_529,plain,
    ( v2_funct_2(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_5968,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5881,c_39,c_42,c_529])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1392,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k2_relset_1(X1_52,X2_52,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1953,plain,
    ( k2_relset_1(X0_52,X1_52,X2_52) = k2_relat_1(X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_3349,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1967,c_1953])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_24])).

cnf(c_214,plain,
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
    inference(renaming,[status(thm)],[c_213])).

cnf(c_1375,plain,
    ( ~ r2_relset_1(X0_52,X0_52,k1_partfun1(X0_52,X1_52,X1_52,X0_52,X2_52,X3_52),k6_partfun1(X0_52))
    | ~ v1_funct_2(X3_52,X1_52,X0_52)
    | ~ v1_funct_2(X2_52,X0_52,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ v1_funct_1(X2_52)
    | ~ v1_funct_1(X3_52)
    | k2_relset_1(X0_52,X1_52,X2_52) != X1_52
    | k2_funct_1(X2_52) = X3_52
    | k1_xboole_0 = X0_52
    | k1_xboole_0 = X1_52 ),
    inference(subtyping,[status(esa)],[c_214])).

cnf(c_1970,plain,
    ( k2_relset_1(X0_52,X1_52,X2_52) != X1_52
    | k2_funct_1(X2_52) = X3_52
    | k1_xboole_0 = X0_52
    | k1_xboole_0 = X1_52
    | r2_relset_1(X0_52,X0_52,k1_partfun1(X0_52,X1_52,X1_52,X0_52,X2_52,X3_52),k6_partfun1(X0_52)) != iProver_top
    | v1_funct_2(X3_52,X1_52,X0_52) != iProver_top
    | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top
    | v1_funct_1(X3_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_5221,plain,
    ( k2_funct_1(sK2) = X0_52
    | k2_relat_1(sK2) != sK1
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3349,c_1970])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5464,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0
    | k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5221,c_39,c_40,c_42])).

cnf(c_5465,plain,
    ( k2_funct_1(sK2) = X0_52
    | k2_relat_1(sK2) != sK1
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5464])).

cnf(c_5970,plain,
    ( k2_funct_1(sK2) = X0_52
    | sK1 != sK1
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5968,c_5465])).

cnf(c_5972,plain,
    ( k2_funct_1(sK2) = X0_52
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5970])).

cnf(c_7033,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1963,c_5972])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_7034,plain,
    ( ~ v1_funct_2(sK3,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7033])).

cnf(c_7036,plain,
    ( sK1 = k1_xboole_0
    | k2_funct_1(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7033,c_43,c_44,c_46])).

cnf(c_7037,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7036])).

cnf(c_29,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1383,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1962,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1383])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_546,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_547,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_549,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_38,c_37,c_35])).

cnf(c_1369,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_549])).

cnf(c_1975,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1962,c_1369])).

cnf(c_7038,plain,
    ( sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7037,c_1975])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2041,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_2042,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2041])).

cnf(c_7102,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7038,c_46,c_2042])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1394,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ v1_xboole_0(X1_52)
    | v1_xboole_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1951,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | v1_xboole_0(X1_52) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_2993,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_1951])).

cnf(c_7134,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7102,c_2993])).

cnf(c_123,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1408,plain,
    ( ~ v1_xboole_0(X0_52)
    | v1_xboole_0(X1_52)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_2560,plain,
    ( v1_xboole_0(X0_52)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_52 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_2561,plain,
    ( X0_52 != k1_xboole_0
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2560])).

cnf(c_2563,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_8616,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7134,c_46,c_123,c_2042,c_2563,c_2993,c_7038])).

cnf(c_8624,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8616,c_3106])).

cnf(c_7136,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7102,c_1975])).

cnf(c_9130,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8624,c_7136])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1389,plain,
    ( m1_subset_1(k6_partfun1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_52,X0_52))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1956,plain,
    ( m1_subset_1(k6_partfun1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_52,X0_52))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_2994,plain,
    ( v1_xboole_0(X0_52) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1956,c_1951])).

cnf(c_5312,plain,
    ( k6_partfun1(X0_52) = k1_xboole_0
    | v1_xboole_0(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2994,c_3106])).

cnf(c_5471,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1944,c_5312])).

cnf(c_6,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1396,plain,
    ( k2_funct_1(k6_partfun1(X0_52)) = k6_partfun1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_5590,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5471,c_1396])).

cnf(c_5591,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5590,c_5471])).

cnf(c_1381,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1964,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_2992,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1964,c_1951])).

cnf(c_7135,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7102,c_2992])).

cnf(c_2336,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_xboole_0(X0_52)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_2337,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_xboole_0(X0_52) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2336])).

cnf(c_2339,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2337])).

cnf(c_8745,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7135,c_46,c_123,c_2042,c_2339,c_2563,c_7038])).

cnf(c_8753,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8745,c_3106])).

cnf(c_9140,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9130,c_5591,c_8753])).

cnf(c_10557,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4700,c_9140])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.83/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.01  
% 3.83/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/1.01  
% 3.83/1.01  ------  iProver source info
% 3.83/1.01  
% 3.83/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.83/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/1.01  git: non_committed_changes: false
% 3.83/1.01  git: last_make_outside_of_git: false
% 3.83/1.01  
% 3.83/1.01  ------ 
% 3.83/1.01  
% 3.83/1.01  ------ Input Options
% 3.83/1.01  
% 3.83/1.01  --out_options                           all
% 3.83/1.01  --tptp_safe_out                         true
% 3.83/1.01  --problem_path                          ""
% 3.83/1.01  --include_path                          ""
% 3.83/1.01  --clausifier                            res/vclausify_rel
% 3.83/1.01  --clausifier_options                    ""
% 3.83/1.01  --stdin                                 false
% 3.83/1.01  --stats_out                             all
% 3.83/1.01  
% 3.83/1.01  ------ General Options
% 3.83/1.01  
% 3.83/1.01  --fof                                   false
% 3.83/1.01  --time_out_real                         305.
% 3.83/1.01  --time_out_virtual                      -1.
% 3.83/1.01  --symbol_type_check                     false
% 3.83/1.01  --clausify_out                          false
% 3.83/1.01  --sig_cnt_out                           false
% 3.83/1.01  --trig_cnt_out                          false
% 3.83/1.01  --trig_cnt_out_tolerance                1.
% 3.83/1.01  --trig_cnt_out_sk_spl                   false
% 3.83/1.01  --abstr_cl_out                          false
% 3.83/1.01  
% 3.83/1.01  ------ Global Options
% 3.83/1.01  
% 3.83/1.01  --schedule                              default
% 3.83/1.01  --add_important_lit                     false
% 3.83/1.01  --prop_solver_per_cl                    1000
% 3.83/1.01  --min_unsat_core                        false
% 3.83/1.01  --soft_assumptions                      false
% 3.83/1.01  --soft_lemma_size                       3
% 3.83/1.01  --prop_impl_unit_size                   0
% 3.83/1.01  --prop_impl_unit                        []
% 3.83/1.01  --share_sel_clauses                     true
% 3.83/1.01  --reset_solvers                         false
% 3.83/1.01  --bc_imp_inh                            [conj_cone]
% 3.83/1.01  --conj_cone_tolerance                   3.
% 3.83/1.01  --extra_neg_conj                        none
% 3.83/1.01  --large_theory_mode                     true
% 3.83/1.01  --prolific_symb_bound                   200
% 3.83/1.01  --lt_threshold                          2000
% 3.83/1.01  --clause_weak_htbl                      true
% 3.83/1.01  --gc_record_bc_elim                     false
% 3.83/1.01  
% 3.83/1.01  ------ Preprocessing Options
% 3.83/1.01  
% 3.83/1.01  --preprocessing_flag                    true
% 3.83/1.01  --time_out_prep_mult                    0.1
% 3.83/1.01  --splitting_mode                        input
% 3.83/1.01  --splitting_grd                         true
% 3.83/1.01  --splitting_cvd                         false
% 3.83/1.01  --splitting_cvd_svl                     false
% 3.83/1.01  --splitting_nvd                         32
% 3.83/1.01  --sub_typing                            true
% 3.83/1.01  --prep_gs_sim                           true
% 3.83/1.01  --prep_unflatten                        true
% 3.83/1.01  --prep_res_sim                          true
% 3.83/1.01  --prep_upred                            true
% 3.83/1.01  --prep_sem_filter                       exhaustive
% 3.83/1.01  --prep_sem_filter_out                   false
% 3.83/1.01  --pred_elim                             true
% 3.83/1.01  --res_sim_input                         true
% 3.83/1.01  --eq_ax_congr_red                       true
% 3.83/1.01  --pure_diseq_elim                       true
% 3.83/1.01  --brand_transform                       false
% 3.83/1.01  --non_eq_to_eq                          false
% 3.83/1.01  --prep_def_merge                        true
% 3.83/1.01  --prep_def_merge_prop_impl              false
% 3.83/1.01  --prep_def_merge_mbd                    true
% 3.83/1.01  --prep_def_merge_tr_red                 false
% 3.83/1.01  --prep_def_merge_tr_cl                  false
% 3.83/1.01  --smt_preprocessing                     true
% 3.83/1.01  --smt_ac_axioms                         fast
% 3.83/1.01  --preprocessed_out                      false
% 3.83/1.01  --preprocessed_stats                    false
% 3.83/1.01  
% 3.83/1.01  ------ Abstraction refinement Options
% 3.83/1.01  
% 3.83/1.01  --abstr_ref                             []
% 3.83/1.01  --abstr_ref_prep                        false
% 3.83/1.01  --abstr_ref_until_sat                   false
% 3.83/1.01  --abstr_ref_sig_restrict                funpre
% 3.83/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/1.01  --abstr_ref_under                       []
% 3.83/1.01  
% 3.83/1.01  ------ SAT Options
% 3.83/1.01  
% 3.83/1.01  --sat_mode                              false
% 3.83/1.01  --sat_fm_restart_options                ""
% 3.83/1.01  --sat_gr_def                            false
% 3.83/1.01  --sat_epr_types                         true
% 3.83/1.01  --sat_non_cyclic_types                  false
% 3.83/1.01  --sat_finite_models                     false
% 3.83/1.01  --sat_fm_lemmas                         false
% 3.83/1.01  --sat_fm_prep                           false
% 3.83/1.01  --sat_fm_uc_incr                        true
% 3.83/1.01  --sat_out_model                         small
% 3.83/1.01  --sat_out_clauses                       false
% 3.83/1.01  
% 3.83/1.01  ------ QBF Options
% 3.83/1.01  
% 3.83/1.01  --qbf_mode                              false
% 3.83/1.01  --qbf_elim_univ                         false
% 3.83/1.01  --qbf_dom_inst                          none
% 3.83/1.01  --qbf_dom_pre_inst                      false
% 3.83/1.01  --qbf_sk_in                             false
% 3.83/1.01  --qbf_pred_elim                         true
% 3.83/1.01  --qbf_split                             512
% 3.83/1.01  
% 3.83/1.01  ------ BMC1 Options
% 3.83/1.01  
% 3.83/1.01  --bmc1_incremental                      false
% 3.83/1.01  --bmc1_axioms                           reachable_all
% 3.83/1.01  --bmc1_min_bound                        0
% 3.83/1.01  --bmc1_max_bound                        -1
% 3.83/1.01  --bmc1_max_bound_default                -1
% 3.83/1.01  --bmc1_symbol_reachability              true
% 3.83/1.01  --bmc1_property_lemmas                  false
% 3.83/1.01  --bmc1_k_induction                      false
% 3.83/1.01  --bmc1_non_equiv_states                 false
% 3.83/1.01  --bmc1_deadlock                         false
% 3.83/1.01  --bmc1_ucm                              false
% 3.83/1.01  --bmc1_add_unsat_core                   none
% 3.83/1.01  --bmc1_unsat_core_children              false
% 3.83/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/1.01  --bmc1_out_stat                         full
% 3.83/1.01  --bmc1_ground_init                      false
% 3.83/1.01  --bmc1_pre_inst_next_state              false
% 3.83/1.01  --bmc1_pre_inst_state                   false
% 3.83/1.01  --bmc1_pre_inst_reach_state             false
% 3.83/1.01  --bmc1_out_unsat_core                   false
% 3.83/1.01  --bmc1_aig_witness_out                  false
% 3.83/1.01  --bmc1_verbose                          false
% 3.83/1.01  --bmc1_dump_clauses_tptp                false
% 3.83/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.83/1.01  --bmc1_dump_file                        -
% 3.83/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.83/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.83/1.01  --bmc1_ucm_extend_mode                  1
% 3.83/1.01  --bmc1_ucm_init_mode                    2
% 3.83/1.01  --bmc1_ucm_cone_mode                    none
% 3.83/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.83/1.01  --bmc1_ucm_relax_model                  4
% 3.83/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.83/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/1.01  --bmc1_ucm_layered_model                none
% 3.83/1.01  --bmc1_ucm_max_lemma_size               10
% 3.83/1.01  
% 3.83/1.01  ------ AIG Options
% 3.83/1.01  
% 3.83/1.01  --aig_mode                              false
% 3.83/1.01  
% 3.83/1.01  ------ Instantiation Options
% 3.83/1.01  
% 3.83/1.01  --instantiation_flag                    true
% 3.83/1.01  --inst_sos_flag                         true
% 3.83/1.01  --inst_sos_phase                        true
% 3.83/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/1.01  --inst_lit_sel_side                     num_symb
% 3.83/1.01  --inst_solver_per_active                1400
% 3.83/1.01  --inst_solver_calls_frac                1.
% 3.83/1.01  --inst_passive_queue_type               priority_queues
% 3.83/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/1.01  --inst_passive_queues_freq              [25;2]
% 3.83/1.01  --inst_dismatching                      true
% 3.83/1.01  --inst_eager_unprocessed_to_passive     true
% 3.83/1.01  --inst_prop_sim_given                   true
% 3.83/1.01  --inst_prop_sim_new                     false
% 3.83/1.01  --inst_subs_new                         false
% 3.83/1.01  --inst_eq_res_simp                      false
% 3.83/1.01  --inst_subs_given                       false
% 3.83/1.01  --inst_orphan_elimination               true
% 3.83/1.01  --inst_learning_loop_flag               true
% 3.83/1.01  --inst_learning_start                   3000
% 3.83/1.01  --inst_learning_factor                  2
% 3.83/1.01  --inst_start_prop_sim_after_learn       3
% 3.83/1.01  --inst_sel_renew                        solver
% 3.83/1.01  --inst_lit_activity_flag                true
% 3.83/1.01  --inst_restr_to_given                   false
% 3.83/1.01  --inst_activity_threshold               500
% 3.83/1.01  --inst_out_proof                        true
% 3.83/1.01  
% 3.83/1.01  ------ Resolution Options
% 3.83/1.01  
% 3.83/1.01  --resolution_flag                       true
% 3.83/1.01  --res_lit_sel                           adaptive
% 3.83/1.01  --res_lit_sel_side                      none
% 3.83/1.01  --res_ordering                          kbo
% 3.83/1.01  --res_to_prop_solver                    active
% 3.83/1.01  --res_prop_simpl_new                    false
% 3.83/1.01  --res_prop_simpl_given                  true
% 3.83/1.01  --res_passive_queue_type                priority_queues
% 3.83/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/1.01  --res_passive_queues_freq               [15;5]
% 3.83/1.01  --res_forward_subs                      full
% 3.83/1.01  --res_backward_subs                     full
% 3.83/1.01  --res_forward_subs_resolution           true
% 3.83/1.01  --res_backward_subs_resolution          true
% 3.83/1.01  --res_orphan_elimination                true
% 3.83/1.01  --res_time_limit                        2.
% 3.83/1.01  --res_out_proof                         true
% 3.83/1.01  
% 3.83/1.01  ------ Superposition Options
% 3.83/1.01  
% 3.83/1.01  --superposition_flag                    true
% 3.83/1.01  --sup_passive_queue_type                priority_queues
% 3.83/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.83/1.01  --demod_completeness_check              fast
% 3.83/1.01  --demod_use_ground                      true
% 3.83/1.01  --sup_to_prop_solver                    passive
% 3.83/1.01  --sup_prop_simpl_new                    true
% 3.83/1.01  --sup_prop_simpl_given                  true
% 3.83/1.01  --sup_fun_splitting                     true
% 3.83/1.01  --sup_smt_interval                      50000
% 3.83/1.01  
% 3.83/1.01  ------ Superposition Simplification Setup
% 3.83/1.01  
% 3.83/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/1.01  --sup_immed_triv                        [TrivRules]
% 3.83/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.01  --sup_immed_bw_main                     []
% 3.83/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.01  --sup_input_bw                          []
% 3.83/1.01  
% 3.83/1.01  ------ Combination Options
% 3.83/1.01  
% 3.83/1.01  --comb_res_mult                         3
% 3.83/1.01  --comb_sup_mult                         2
% 3.83/1.01  --comb_inst_mult                        10
% 3.83/1.01  
% 3.83/1.01  ------ Debug Options
% 3.83/1.01  
% 3.83/1.01  --dbg_backtrace                         false
% 3.83/1.01  --dbg_dump_prop_clauses                 false
% 3.83/1.01  --dbg_dump_prop_clauses_file            -
% 3.83/1.01  --dbg_out_stat                          false
% 3.83/1.01  ------ Parsing...
% 3.83/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/1.01  
% 3.83/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.83/1.01  
% 3.83/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/1.01  
% 3.83/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/1.01  ------ Proving...
% 3.83/1.01  ------ Problem Properties 
% 3.83/1.01  
% 3.83/1.01  
% 3.83/1.01  clauses                                 34
% 3.83/1.01  conjectures                             8
% 3.83/1.01  EPR                                     8
% 3.83/1.01  Horn                                    33
% 3.83/1.01  unary                                   17
% 3.83/1.01  binary                                  4
% 3.83/1.01  lits                                    82
% 3.83/1.01  lits eq                                 15
% 3.83/1.01  fd_pure                                 0
% 3.83/1.01  fd_pseudo                               0
% 3.83/1.01  fd_cond                                 0
% 3.83/1.01  fd_pseudo_cond                          4
% 3.83/1.01  AC symbols                              0
% 3.83/1.01  
% 3.83/1.01  ------ Schedule dynamic 5 is on 
% 3.83/1.01  
% 3.83/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.83/1.01  
% 3.83/1.01  
% 3.83/1.01  ------ 
% 3.83/1.01  Current options:
% 3.83/1.01  ------ 
% 3.83/1.01  
% 3.83/1.01  ------ Input Options
% 3.83/1.01  
% 3.83/1.01  --out_options                           all
% 3.83/1.01  --tptp_safe_out                         true
% 3.83/1.01  --problem_path                          ""
% 3.83/1.01  --include_path                          ""
% 3.83/1.01  --clausifier                            res/vclausify_rel
% 3.83/1.01  --clausifier_options                    ""
% 3.83/1.01  --stdin                                 false
% 3.83/1.01  --stats_out                             all
% 3.83/1.01  
% 3.83/1.01  ------ General Options
% 3.83/1.01  
% 3.83/1.01  --fof                                   false
% 3.83/1.01  --time_out_real                         305.
% 3.83/1.01  --time_out_virtual                      -1.
% 3.83/1.01  --symbol_type_check                     false
% 3.83/1.01  --clausify_out                          false
% 3.83/1.01  --sig_cnt_out                           false
% 3.83/1.01  --trig_cnt_out                          false
% 3.83/1.01  --trig_cnt_out_tolerance                1.
% 3.83/1.01  --trig_cnt_out_sk_spl                   false
% 3.83/1.01  --abstr_cl_out                          false
% 3.83/1.01  
% 3.83/1.01  ------ Global Options
% 3.83/1.01  
% 3.83/1.01  --schedule                              default
% 3.83/1.01  --add_important_lit                     false
% 3.83/1.01  --prop_solver_per_cl                    1000
% 3.83/1.01  --min_unsat_core                        false
% 3.83/1.01  --soft_assumptions                      false
% 3.83/1.01  --soft_lemma_size                       3
% 3.83/1.01  --prop_impl_unit_size                   0
% 3.83/1.01  --prop_impl_unit                        []
% 3.83/1.01  --share_sel_clauses                     true
% 3.83/1.01  --reset_solvers                         false
% 3.83/1.01  --bc_imp_inh                            [conj_cone]
% 3.83/1.01  --conj_cone_tolerance                   3.
% 3.83/1.01  --extra_neg_conj                        none
% 3.83/1.01  --large_theory_mode                     true
% 3.83/1.01  --prolific_symb_bound                   200
% 3.83/1.01  --lt_threshold                          2000
% 3.83/1.01  --clause_weak_htbl                      true
% 3.83/1.01  --gc_record_bc_elim                     false
% 3.83/1.01  
% 3.83/1.01  ------ Preprocessing Options
% 3.83/1.01  
% 3.83/1.01  --preprocessing_flag                    true
% 3.83/1.01  --time_out_prep_mult                    0.1
% 3.83/1.01  --splitting_mode                        input
% 3.83/1.01  --splitting_grd                         true
% 3.83/1.01  --splitting_cvd                         false
% 3.83/1.01  --splitting_cvd_svl                     false
% 3.83/1.01  --splitting_nvd                         32
% 3.83/1.01  --sub_typing                            true
% 3.83/1.01  --prep_gs_sim                           true
% 3.83/1.01  --prep_unflatten                        true
% 3.83/1.01  --prep_res_sim                          true
% 3.83/1.01  --prep_upred                            true
% 3.83/1.01  --prep_sem_filter                       exhaustive
% 3.83/1.01  --prep_sem_filter_out                   false
% 3.83/1.01  --pred_elim                             true
% 3.83/1.01  --res_sim_input                         true
% 3.83/1.01  --eq_ax_congr_red                       true
% 3.83/1.01  --pure_diseq_elim                       true
% 3.83/1.01  --brand_transform                       false
% 3.83/1.01  --non_eq_to_eq                          false
% 3.83/1.01  --prep_def_merge                        true
% 3.83/1.01  --prep_def_merge_prop_impl              false
% 3.83/1.01  --prep_def_merge_mbd                    true
% 3.83/1.01  --prep_def_merge_tr_red                 false
% 3.83/1.01  --prep_def_merge_tr_cl                  false
% 3.83/1.01  --smt_preprocessing                     true
% 3.83/1.01  --smt_ac_axioms                         fast
% 3.83/1.01  --preprocessed_out                      false
% 3.83/1.01  --preprocessed_stats                    false
% 3.83/1.01  
% 3.83/1.01  ------ Abstraction refinement Options
% 3.83/1.01  
% 3.83/1.01  --abstr_ref                             []
% 3.83/1.01  --abstr_ref_prep                        false
% 3.83/1.01  --abstr_ref_until_sat                   false
% 3.83/1.01  --abstr_ref_sig_restrict                funpre
% 3.83/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/1.01  --abstr_ref_under                       []
% 3.83/1.01  
% 3.83/1.01  ------ SAT Options
% 3.83/1.01  
% 3.83/1.01  --sat_mode                              false
% 3.83/1.01  --sat_fm_restart_options                ""
% 3.83/1.01  --sat_gr_def                            false
% 3.83/1.01  --sat_epr_types                         true
% 3.83/1.01  --sat_non_cyclic_types                  false
% 3.83/1.01  --sat_finite_models                     false
% 3.83/1.01  --sat_fm_lemmas                         false
% 3.83/1.01  --sat_fm_prep                           false
% 3.83/1.01  --sat_fm_uc_incr                        true
% 3.83/1.01  --sat_out_model                         small
% 3.83/1.01  --sat_out_clauses                       false
% 3.83/1.01  
% 3.83/1.01  ------ QBF Options
% 3.83/1.01  
% 3.83/1.01  --qbf_mode                              false
% 3.83/1.01  --qbf_elim_univ                         false
% 3.83/1.01  --qbf_dom_inst                          none
% 3.83/1.01  --qbf_dom_pre_inst                      false
% 3.83/1.01  --qbf_sk_in                             false
% 3.83/1.01  --qbf_pred_elim                         true
% 3.83/1.01  --qbf_split                             512
% 3.83/1.01  
% 3.83/1.01  ------ BMC1 Options
% 3.83/1.01  
% 3.83/1.01  --bmc1_incremental                      false
% 3.83/1.01  --bmc1_axioms                           reachable_all
% 3.83/1.01  --bmc1_min_bound                        0
% 3.83/1.01  --bmc1_max_bound                        -1
% 3.83/1.01  --bmc1_max_bound_default                -1
% 3.83/1.01  --bmc1_symbol_reachability              true
% 3.83/1.01  --bmc1_property_lemmas                  false
% 3.83/1.01  --bmc1_k_induction                      false
% 3.83/1.01  --bmc1_non_equiv_states                 false
% 3.83/1.01  --bmc1_deadlock                         false
% 3.83/1.01  --bmc1_ucm                              false
% 3.83/1.01  --bmc1_add_unsat_core                   none
% 3.83/1.01  --bmc1_unsat_core_children              false
% 3.83/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/1.01  --bmc1_out_stat                         full
% 3.83/1.01  --bmc1_ground_init                      false
% 3.83/1.01  --bmc1_pre_inst_next_state              false
% 3.83/1.01  --bmc1_pre_inst_state                   false
% 3.83/1.01  --bmc1_pre_inst_reach_state             false
% 3.83/1.01  --bmc1_out_unsat_core                   false
% 3.83/1.01  --bmc1_aig_witness_out                  false
% 3.83/1.01  --bmc1_verbose                          false
% 3.83/1.01  --bmc1_dump_clauses_tptp                false
% 3.83/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.83/1.01  --bmc1_dump_file                        -
% 3.83/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.83/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.83/1.01  --bmc1_ucm_extend_mode                  1
% 3.83/1.01  --bmc1_ucm_init_mode                    2
% 3.83/1.01  --bmc1_ucm_cone_mode                    none
% 3.83/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.83/1.01  --bmc1_ucm_relax_model                  4
% 3.83/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.83/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/1.01  --bmc1_ucm_layered_model                none
% 3.83/1.01  --bmc1_ucm_max_lemma_size               10
% 3.83/1.01  
% 3.83/1.01  ------ AIG Options
% 3.83/1.01  
% 3.83/1.01  --aig_mode                              false
% 3.83/1.01  
% 3.83/1.01  ------ Instantiation Options
% 3.83/1.01  
% 3.83/1.01  --instantiation_flag                    true
% 3.83/1.01  --inst_sos_flag                         true
% 3.83/1.01  --inst_sos_phase                        true
% 3.83/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/1.01  --inst_lit_sel_side                     none
% 3.83/1.01  --inst_solver_per_active                1400
% 3.83/1.01  --inst_solver_calls_frac                1.
% 3.83/1.01  --inst_passive_queue_type               priority_queues
% 3.83/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/1.01  --inst_passive_queues_freq              [25;2]
% 3.83/1.01  --inst_dismatching                      true
% 3.83/1.01  --inst_eager_unprocessed_to_passive     true
% 3.83/1.01  --inst_prop_sim_given                   true
% 3.83/1.01  --inst_prop_sim_new                     false
% 3.83/1.01  --inst_subs_new                         false
% 3.83/1.01  --inst_eq_res_simp                      false
% 3.83/1.01  --inst_subs_given                       false
% 3.83/1.01  --inst_orphan_elimination               true
% 3.83/1.01  --inst_learning_loop_flag               true
% 3.83/1.01  --inst_learning_start                   3000
% 3.83/1.01  --inst_learning_factor                  2
% 3.83/1.01  --inst_start_prop_sim_after_learn       3
% 3.83/1.01  --inst_sel_renew                        solver
% 3.83/1.01  --inst_lit_activity_flag                true
% 3.83/1.01  --inst_restr_to_given                   false
% 3.83/1.01  --inst_activity_threshold               500
% 3.83/1.01  --inst_out_proof                        true
% 3.83/1.01  
% 3.83/1.01  ------ Resolution Options
% 3.83/1.01  
% 3.83/1.01  --resolution_flag                       false
% 3.83/1.01  --res_lit_sel                           adaptive
% 3.83/1.01  --res_lit_sel_side                      none
% 3.83/1.01  --res_ordering                          kbo
% 3.83/1.01  --res_to_prop_solver                    active
% 3.83/1.01  --res_prop_simpl_new                    false
% 3.83/1.01  --res_prop_simpl_given                  true
% 3.83/1.01  --res_passive_queue_type                priority_queues
% 3.83/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/1.01  --res_passive_queues_freq               [15;5]
% 3.83/1.01  --res_forward_subs                      full
% 3.83/1.01  --res_backward_subs                     full
% 3.83/1.01  --res_forward_subs_resolution           true
% 3.83/1.01  --res_backward_subs_resolution          true
% 3.83/1.01  --res_orphan_elimination                true
% 3.83/1.01  --res_time_limit                        2.
% 3.83/1.01  --res_out_proof                         true
% 3.83/1.01  
% 3.83/1.01  ------ Superposition Options
% 3.83/1.01  
% 3.83/1.01  --superposition_flag                    true
% 3.83/1.01  --sup_passive_queue_type                priority_queues
% 3.83/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.83/1.01  --demod_completeness_check              fast
% 3.83/1.01  --demod_use_ground                      true
% 3.83/1.01  --sup_to_prop_solver                    passive
% 3.83/1.01  --sup_prop_simpl_new                    true
% 3.83/1.01  --sup_prop_simpl_given                  true
% 3.83/1.01  --sup_fun_splitting                     true
% 3.83/1.01  --sup_smt_interval                      50000
% 3.83/1.01  
% 3.83/1.01  ------ Superposition Simplification Setup
% 3.83/1.01  
% 3.83/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/1.01  --sup_immed_triv                        [TrivRules]
% 3.83/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.01  --sup_immed_bw_main                     []
% 3.83/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.01  --sup_input_bw                          []
% 3.83/1.01  
% 3.83/1.01  ------ Combination Options
% 3.83/1.01  
% 3.83/1.01  --comb_res_mult                         3
% 3.83/1.01  --comb_sup_mult                         2
% 3.83/1.01  --comb_inst_mult                        10
% 3.83/1.01  
% 3.83/1.01  ------ Debug Options
% 3.83/1.01  
% 3.83/1.01  --dbg_backtrace                         false
% 3.83/1.01  --dbg_dump_prop_clauses                 false
% 3.83/1.01  --dbg_dump_prop_clauses_file            -
% 3.83/1.01  --dbg_out_stat                          false
% 3.83/1.01  
% 3.83/1.01  
% 3.83/1.01  
% 3.83/1.01  
% 3.83/1.01  ------ Proving...
% 3.83/1.01  
% 3.83/1.01  
% 3.83/1.01  % SZS status Theorem for theBenchmark.p
% 3.83/1.01  
% 3.83/1.01   Resolution empty clause
% 3.83/1.01  
% 3.83/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/1.01  
% 3.83/1.01  fof(f3,axiom,(
% 3.83/1.01    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f49,plain,(
% 3.83/1.01    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 3.83/1.01    introduced(choice_axiom,[])).
% 3.83/1.01  
% 3.83/1.01  fof(f50,plain,(
% 3.83/1.01    ! [X0] : (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 3.83/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f49])).
% 3.83/1.01  
% 3.83/1.01  fof(f60,plain,(
% 3.83/1.01    ( ! [X0] : (v1_xboole_0(sK0(X0))) )),
% 3.83/1.01    inference(cnf_transformation,[],[f50])).
% 3.83/1.01  
% 3.83/1.01  fof(f1,axiom,(
% 3.83/1.01    v1_xboole_0(k1_xboole_0)),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f57,plain,(
% 3.83/1.01    v1_xboole_0(k1_xboole_0)),
% 3.83/1.01    inference(cnf_transformation,[],[f1])).
% 3.83/1.01  
% 3.83/1.01  fof(f2,axiom,(
% 3.83/1.01    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f24,plain,(
% 3.83/1.01    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.83/1.01    inference(ennf_transformation,[],[f2])).
% 3.83/1.01  
% 3.83/1.01  fof(f58,plain,(
% 3.83/1.01    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.83/1.01    inference(cnf_transformation,[],[f24])).
% 3.83/1.01  
% 3.83/1.01  fof(f59,plain,(
% 3.83/1.01    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 3.83/1.01    inference(cnf_transformation,[],[f50])).
% 3.83/1.01  
% 3.83/1.01  fof(f11,axiom,(
% 3.83/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f31,plain,(
% 3.83/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.83/1.01    inference(ennf_transformation,[],[f11])).
% 3.83/1.01  
% 3.83/1.01  fof(f32,plain,(
% 3.83/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.01    inference(flattening,[],[f31])).
% 3.83/1.01  
% 3.83/1.01  fof(f52,plain,(
% 3.83/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.01    inference(nnf_transformation,[],[f32])).
% 3.83/1.01  
% 3.83/1.01  fof(f70,plain,(
% 3.83/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.01    inference(cnf_transformation,[],[f52])).
% 3.83/1.01  
% 3.83/1.01  fof(f99,plain,(
% 3.83/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.01    inference(equality_resolution,[],[f70])).
% 3.83/1.01  
% 3.83/1.01  fof(f21,conjecture,(
% 3.83/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f22,negated_conjecture,(
% 3.83/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.83/1.01    inference(negated_conjecture,[],[f21])).
% 3.83/1.01  
% 3.83/1.01  fof(f47,plain,(
% 3.83/1.01    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.83/1.01    inference(ennf_transformation,[],[f22])).
% 3.83/1.01  
% 3.83/1.01  fof(f48,plain,(
% 3.83/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.83/1.01    inference(flattening,[],[f47])).
% 3.83/1.01  
% 3.83/1.01  fof(f55,plain,(
% 3.83/1.01    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK3,X0,X0) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 3.83/1.01    introduced(choice_axiom,[])).
% 3.83/1.01  
% 3.83/1.01  fof(f54,plain,(
% 3.83/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(X2,sK1,sK1) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.83/1.01    introduced(choice_axiom,[])).
% 3.83/1.01  
% 3.83/1.01  fof(f56,plain,(
% 3.83/1.01    (~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.83/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f55,f54])).
% 3.83/1.01  
% 3.83/1.01  fof(f95,plain,(
% 3.83/1.01    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))),
% 3.83/1.01    inference(cnf_transformation,[],[f56])).
% 3.83/1.01  
% 3.83/1.01  fof(f90,plain,(
% 3.83/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.83/1.01    inference(cnf_transformation,[],[f56])).
% 3.83/1.01  
% 3.83/1.01  fof(f7,axiom,(
% 3.83/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f23,plain,(
% 3.83/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.83/1.01    inference(pure_predicate_removal,[],[f7])).
% 3.83/1.01  
% 3.83/1.01  fof(f27,plain,(
% 3.83/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.01    inference(ennf_transformation,[],[f23])).
% 3.83/1.01  
% 3.83/1.01  fof(f65,plain,(
% 3.83/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.01    inference(cnf_transformation,[],[f27])).
% 3.83/1.01  
% 3.83/1.01  fof(f14,axiom,(
% 3.83/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f35,plain,(
% 3.83/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.83/1.01    inference(ennf_transformation,[],[f14])).
% 3.83/1.01  
% 3.83/1.01  fof(f36,plain,(
% 3.83/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.83/1.01    inference(flattening,[],[f35])).
% 3.83/1.01  
% 3.83/1.01  fof(f53,plain,(
% 3.83/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.83/1.01    inference(nnf_transformation,[],[f36])).
% 3.83/1.01  
% 3.83/1.01  fof(f75,plain,(
% 3.83/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.83/1.01    inference(cnf_transformation,[],[f53])).
% 3.83/1.01  
% 3.83/1.01  fof(f6,axiom,(
% 3.83/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f26,plain,(
% 3.83/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.01    inference(ennf_transformation,[],[f6])).
% 3.83/1.01  
% 3.83/1.01  fof(f64,plain,(
% 3.83/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.01    inference(cnf_transformation,[],[f26])).
% 3.83/1.01  
% 3.83/1.01  fof(f87,plain,(
% 3.83/1.01    v1_funct_1(sK2)),
% 3.83/1.01    inference(cnf_transformation,[],[f56])).
% 3.83/1.01  
% 3.83/1.01  fof(f13,axiom,(
% 3.83/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f33,plain,(
% 3.83/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.01    inference(ennf_transformation,[],[f13])).
% 3.83/1.01  
% 3.83/1.01  fof(f34,plain,(
% 3.83/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.01    inference(flattening,[],[f33])).
% 3.83/1.01  
% 3.83/1.01  fof(f74,plain,(
% 3.83/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.01    inference(cnf_transformation,[],[f34])).
% 3.83/1.01  
% 3.83/1.01  fof(f89,plain,(
% 3.83/1.01    v3_funct_2(sK2,sK1,sK1)),
% 3.83/1.01    inference(cnf_transformation,[],[f56])).
% 3.83/1.01  
% 3.83/1.01  fof(f10,axiom,(
% 3.83/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f30,plain,(
% 3.83/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.01    inference(ennf_transformation,[],[f10])).
% 3.83/1.01  
% 3.83/1.01  fof(f68,plain,(
% 3.83/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.01    inference(cnf_transformation,[],[f30])).
% 3.83/1.01  
% 3.83/1.01  fof(f19,axiom,(
% 3.83/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f43,plain,(
% 3.83/1.01    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.83/1.01    inference(ennf_transformation,[],[f19])).
% 3.83/1.01  
% 3.83/1.01  fof(f44,plain,(
% 3.83/1.01    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.83/1.01    inference(flattening,[],[f43])).
% 3.83/1.01  
% 3.83/1.01  fof(f83,plain,(
% 3.83/1.01    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.83/1.01    inference(cnf_transformation,[],[f44])).
% 3.83/1.01  
% 3.83/1.01  fof(f18,axiom,(
% 3.83/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f41,plain,(
% 3.83/1.01    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.83/1.01    inference(ennf_transformation,[],[f18])).
% 3.83/1.01  
% 3.83/1.01  fof(f42,plain,(
% 3.83/1.01    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.83/1.01    inference(flattening,[],[f41])).
% 3.83/1.01  
% 3.83/1.01  fof(f81,plain,(
% 3.83/1.01    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.83/1.01    inference(cnf_transformation,[],[f42])).
% 3.83/1.01  
% 3.83/1.01  fof(f88,plain,(
% 3.83/1.01    v1_funct_2(sK2,sK1,sK1)),
% 3.83/1.01    inference(cnf_transformation,[],[f56])).
% 3.83/1.01  
% 3.83/1.01  fof(f91,plain,(
% 3.83/1.01    v1_funct_1(sK3)),
% 3.83/1.01    inference(cnf_transformation,[],[f56])).
% 3.83/1.01  
% 3.83/1.01  fof(f92,plain,(
% 3.83/1.01    v1_funct_2(sK3,sK1,sK1)),
% 3.83/1.01    inference(cnf_transformation,[],[f56])).
% 3.83/1.01  
% 3.83/1.01  fof(f94,plain,(
% 3.83/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.83/1.01    inference(cnf_transformation,[],[f56])).
% 3.83/1.01  
% 3.83/1.01  fof(f96,plain,(
% 3.83/1.01    ~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))),
% 3.83/1.01    inference(cnf_transformation,[],[f56])).
% 3.83/1.01  
% 3.83/1.01  fof(f16,axiom,(
% 3.83/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f39,plain,(
% 3.83/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.83/1.01    inference(ennf_transformation,[],[f16])).
% 3.83/1.01  
% 3.83/1.01  fof(f40,plain,(
% 3.83/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.83/1.01    inference(flattening,[],[f39])).
% 3.83/1.01  
% 3.83/1.01  fof(f79,plain,(
% 3.83/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.83/1.01    inference(cnf_transformation,[],[f40])).
% 3.83/1.01  
% 3.83/1.01  fof(f8,axiom,(
% 3.83/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f28,plain,(
% 3.83/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.83/1.01    inference(ennf_transformation,[],[f8])).
% 3.83/1.01  
% 3.83/1.01  fof(f66,plain,(
% 3.83/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.83/1.01    inference(cnf_transformation,[],[f28])).
% 3.83/1.01  
% 3.83/1.01  fof(f12,axiom,(
% 3.83/1.01    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f71,plain,(
% 3.83/1.01    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.83/1.01    inference(cnf_transformation,[],[f12])).
% 3.83/1.01  
% 3.83/1.01  fof(f17,axiom,(
% 3.83/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f80,plain,(
% 3.83/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.83/1.01    inference(cnf_transformation,[],[f17])).
% 3.83/1.01  
% 3.83/1.01  fof(f98,plain,(
% 3.83/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.83/1.01    inference(definition_unfolding,[],[f71,f80])).
% 3.83/1.01  
% 3.83/1.01  fof(f5,axiom,(
% 3.83/1.01    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.01  
% 3.83/1.01  fof(f63,plain,(
% 3.83/1.01    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.83/1.01    inference(cnf_transformation,[],[f5])).
% 3.83/1.01  
% 3.83/1.01  fof(f97,plain,(
% 3.83/1.01    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.83/1.01    inference(definition_unfolding,[],[f63,f80,f80])).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2,plain,
% 3.83/1.01      ( v1_xboole_0(sK0(X0)) ),
% 3.83/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1400,plain,
% 3.83/1.01      ( v1_xboole_0(sK0(X0_54)) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1946,plain,
% 3.83/1.01      ( v1_xboole_0(sK0(X0_54)) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_0,plain,
% 3.83/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.83/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1402,plain,
% 3.83/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1944,plain,
% 3.83/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1402]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1,plain,
% 3.83/1.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.83/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1401,plain,
% 3.83/1.01      ( ~ v1_xboole_0(X0_52) | ~ v1_xboole_0(X1_52) | X1_52 = X0_52 ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1945,plain,
% 3.83/1.01      ( X0_52 = X1_52
% 3.83/1.01      | v1_xboole_0(X1_52) != iProver_top
% 3.83/1.01      | v1_xboole_0(X0_52) != iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1401]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_3106,plain,
% 3.83/1.01      ( k1_xboole_0 = X0_52 | v1_xboole_0(X0_52) != iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_1944,c_1945]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_3571,plain,
% 3.83/1.01      ( sK0(X0_54) = k1_xboole_0 ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_1946,c_3106]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_3,plain,
% 3.83/1.01      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 3.83/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1399,plain,
% 3.83/1.01      ( m1_subset_1(sK0(X0_54),k1_zfmisc_1(X0_54)) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1947,plain,
% 3.83/1.01      ( m1_subset_1(sK0(X0_54),k1_zfmisc_1(X0_54)) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1399]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_3643,plain,
% 3.83/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
% 3.83/1.01      inference(demodulation,[status(thm)],[c_3571,c_1947]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_12,plain,
% 3.83/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.83/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1391,plain,
% 3.83/1.01      ( r2_relset_1(X0_52,X1_52,X2_52,X2_52)
% 3.83/1.01      | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1954,plain,
% 3.83/1.01      ( r2_relset_1(X0_52,X1_52,X2_52,X2_52) = iProver_top
% 3.83/1.01      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_4700,plain,
% 3.83/1.01      ( r2_relset_1(X0_52,X1_52,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_3643,c_1954]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_30,negated_conjecture,
% 3.83/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 3.83/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1382,negated_conjecture,
% 3.83/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_30]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1963,plain,
% 3.83/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1382]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_35,negated_conjecture,
% 3.83/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.83/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1378,negated_conjecture,
% 3.83/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_35]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1967,plain,
% 3.83/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1378]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_8,plain,
% 3.83/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.83/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_19,plain,
% 3.83/1.01      ( ~ v2_funct_2(X0,X1)
% 3.83/1.01      | ~ v5_relat_1(X0,X1)
% 3.83/1.01      | ~ v1_relat_1(X0)
% 3.83/1.01      | k2_relat_1(X0) = X1 ),
% 3.83/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_405,plain,
% 3.83/1.01      ( ~ v2_funct_2(X0,X1)
% 3.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.83/1.01      | ~ v1_relat_1(X0)
% 3.83/1.01      | k2_relat_1(X0) = X1 ),
% 3.83/1.01      inference(resolution,[status(thm)],[c_8,c_19]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7,plain,
% 3.83/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.83/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_417,plain,
% 3.83/1.01      ( ~ v2_funct_2(X0,X1)
% 3.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.83/1.01      | k2_relat_1(X0) = X1 ),
% 3.83/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_405,c_7]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1374,plain,
% 3.83/1.01      ( ~ v2_funct_2(X0_52,X1_52)
% 3.83/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
% 3.83/1.01      | k2_relat_1(X0_52) = X1_52 ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_417]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1971,plain,
% 3.83/1.01      ( k2_relat_1(X0_52) = X1_52
% 3.83/1.01      | v2_funct_2(X0_52,X1_52) != iProver_top
% 3.83/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52))) != iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1374]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5881,plain,
% 3.83/1.01      ( k2_relat_1(sK2) = sK1 | v2_funct_2(sK2,sK1) != iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_1967,c_1971]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_38,negated_conjecture,
% 3.83/1.01      ( v1_funct_1(sK2) ),
% 3.83/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_39,plain,
% 3.83/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_42,plain,
% 3.83/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_15,plain,
% 3.83/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.83/1.01      | v2_funct_2(X0,X2)
% 3.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.01      | ~ v1_funct_1(X0) ),
% 3.83/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_36,negated_conjecture,
% 3.83/1.01      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.83/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_527,plain,
% 3.83/1.01      ( v2_funct_2(X0,X1)
% 3.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.83/1.01      | ~ v1_funct_1(X0)
% 3.83/1.01      | sK2 != X0
% 3.83/1.01      | sK1 != X1
% 3.83/1.01      | sK1 != X2 ),
% 3.83/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_528,plain,
% 3.83/1.01      ( v2_funct_2(sK2,sK1)
% 3.83/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.83/1.01      | ~ v1_funct_1(sK2) ),
% 3.83/1.01      inference(unflattening,[status(thm)],[c_527]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_529,plain,
% 3.83/1.01      ( v2_funct_2(sK2,sK1) = iProver_top
% 3.83/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.83/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5968,plain,
% 3.83/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.83/1.01      inference(global_propositional_subsumption,
% 3.83/1.01                [status(thm)],
% 3.83/1.01                [c_5881,c_39,c_42,c_529]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_11,plain,
% 3.83/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.83/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1392,plain,
% 3.83/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 3.83/1.01      | k2_relset_1(X1_52,X2_52,X0_52) = k2_relat_1(X0_52) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1953,plain,
% 3.83/1.01      ( k2_relset_1(X0_52,X1_52,X2_52) = k2_relat_1(X2_52)
% 3.83/1.01      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_3349,plain,
% 3.83/1.01      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_1967,c_1953]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_25,plain,
% 3.83/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.83/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.83/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.83/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.83/1.01      | ~ v2_funct_1(X2)
% 3.83/1.01      | ~ v1_funct_1(X2)
% 3.83/1.01      | ~ v1_funct_1(X3)
% 3.83/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.83/1.01      | k2_funct_1(X2) = X3
% 3.83/1.01      | k1_xboole_0 = X1
% 3.83/1.01      | k1_xboole_0 = X0 ),
% 3.83/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_24,plain,
% 3.83/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.83/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.83/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.83/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.83/1.01      | v2_funct_1(X2)
% 3.83/1.01      | ~ v1_funct_1(X2)
% 3.83/1.01      | ~ v1_funct_1(X3) ),
% 3.83/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_213,plain,
% 3.83/1.01      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.83/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.83/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.83/1.01      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.83/1.01      | ~ v1_funct_1(X2)
% 3.83/1.01      | ~ v1_funct_1(X3)
% 3.83/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.83/1.01      | k2_funct_1(X2) = X3
% 3.83/1.01      | k1_xboole_0 = X1
% 3.83/1.01      | k1_xboole_0 = X0 ),
% 3.83/1.01      inference(global_propositional_subsumption,[status(thm)],[c_25,c_24]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_214,plain,
% 3.83/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.83/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.83/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.83/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.83/1.01      | ~ v1_funct_1(X2)
% 3.83/1.01      | ~ v1_funct_1(X3)
% 3.83/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.83/1.01      | k2_funct_1(X2) = X3
% 3.83/1.01      | k1_xboole_0 = X0
% 3.83/1.01      | k1_xboole_0 = X1 ),
% 3.83/1.01      inference(renaming,[status(thm)],[c_213]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1375,plain,
% 3.83/1.01      ( ~ r2_relset_1(X0_52,X0_52,k1_partfun1(X0_52,X1_52,X1_52,X0_52,X2_52,X3_52),k6_partfun1(X0_52))
% 3.83/1.01      | ~ v1_funct_2(X3_52,X1_52,X0_52)
% 3.83/1.01      | ~ v1_funct_2(X2_52,X0_52,X1_52)
% 3.83/1.01      | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.83/1.01      | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 3.83/1.01      | ~ v1_funct_1(X2_52)
% 3.83/1.01      | ~ v1_funct_1(X3_52)
% 3.83/1.01      | k2_relset_1(X0_52,X1_52,X2_52) != X1_52
% 3.83/1.01      | k2_funct_1(X2_52) = X3_52
% 3.83/1.01      | k1_xboole_0 = X0_52
% 3.83/1.01      | k1_xboole_0 = X1_52 ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_214]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1970,plain,
% 3.83/1.01      ( k2_relset_1(X0_52,X1_52,X2_52) != X1_52
% 3.83/1.01      | k2_funct_1(X2_52) = X3_52
% 3.83/1.01      | k1_xboole_0 = X0_52
% 3.83/1.01      | k1_xboole_0 = X1_52
% 3.83/1.01      | r2_relset_1(X0_52,X0_52,k1_partfun1(X0_52,X1_52,X1_52,X0_52,X2_52,X3_52),k6_partfun1(X0_52)) != iProver_top
% 3.83/1.01      | v1_funct_2(X3_52,X1_52,X0_52) != iProver_top
% 3.83/1.01      | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
% 3.83/1.01      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.83/1.01      | m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
% 3.83/1.01      | v1_funct_1(X2_52) != iProver_top
% 3.83/1.01      | v1_funct_1(X3_52) != iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5221,plain,
% 3.83/1.01      ( k2_funct_1(sK2) = X0_52
% 3.83/1.01      | k2_relat_1(sK2) != sK1
% 3.83/1.01      | sK1 = k1_xboole_0
% 3.83/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.83/1.01      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.83/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.83/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.83/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.83/1.01      | v1_funct_1(X0_52) != iProver_top
% 3.83/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_3349,c_1970]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_37,negated_conjecture,
% 3.83/1.01      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.83/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_40,plain,
% 3.83/1.01      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5464,plain,
% 3.83/1.01      ( v1_funct_1(X0_52) != iProver_top
% 3.83/1.01      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.83/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.83/1.01      | sK1 = k1_xboole_0
% 3.83/1.01      | k2_relat_1(sK2) != sK1
% 3.83/1.01      | k2_funct_1(sK2) = X0_52
% 3.83/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.83/1.01      inference(global_propositional_subsumption,
% 3.83/1.01                [status(thm)],
% 3.83/1.01                [c_5221,c_39,c_40,c_42]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5465,plain,
% 3.83/1.01      ( k2_funct_1(sK2) = X0_52
% 3.83/1.01      | k2_relat_1(sK2) != sK1
% 3.83/1.01      | sK1 = k1_xboole_0
% 3.83/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.83/1.01      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.83/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.83/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 3.83/1.01      inference(renaming,[status(thm)],[c_5464]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5970,plain,
% 3.83/1.01      ( k2_funct_1(sK2) = X0_52
% 3.83/1.01      | sK1 != sK1
% 3.83/1.01      | sK1 = k1_xboole_0
% 3.83/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.83/1.01      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.83/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.83/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 3.83/1.01      inference(demodulation,[status(thm)],[c_5968,c_5465]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5972,plain,
% 3.83/1.01      ( k2_funct_1(sK2) = X0_52
% 3.83/1.01      | sK1 = k1_xboole_0
% 3.83/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.83/1.01      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.83/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.83/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 3.83/1.01      inference(equality_resolution_simp,[status(thm)],[c_5970]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7033,plain,
% 3.83/1.01      ( k2_funct_1(sK2) = sK3
% 3.83/1.01      | sK1 = k1_xboole_0
% 3.83/1.01      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.83/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.83/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_1963,c_5972]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_34,negated_conjecture,
% 3.83/1.01      ( v1_funct_1(sK3) ),
% 3.83/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_33,negated_conjecture,
% 3.83/1.01      ( v1_funct_2(sK3,sK1,sK1) ),
% 3.83/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_31,negated_conjecture,
% 3.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.83/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7034,plain,
% 3.83/1.01      ( ~ v1_funct_2(sK3,sK1,sK1)
% 3.83/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.83/1.01      | ~ v1_funct_1(sK3)
% 3.83/1.01      | k2_funct_1(sK2) = sK3
% 3.83/1.01      | sK1 = k1_xboole_0 ),
% 3.83/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_7033]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7036,plain,
% 3.83/1.01      ( sK1 = k1_xboole_0 | k2_funct_1(sK2) = sK3 ),
% 3.83/1.01      inference(global_propositional_subsumption,
% 3.83/1.01                [status(thm)],
% 3.83/1.01                [c_7033,c_43,c_44,c_46]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7037,plain,
% 3.83/1.01      ( k2_funct_1(sK2) = sK3 | sK1 = k1_xboole_0 ),
% 3.83/1.01      inference(renaming,[status(thm)],[c_7036]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_29,negated_conjecture,
% 3.83/1.01      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 3.83/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1383,negated_conjecture,
% 3.83/1.01      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_29]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1962,plain,
% 3.83/1.01      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1383]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_22,plain,
% 3.83/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.83/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.83/1.01      | ~ v1_funct_1(X0)
% 3.83/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.83/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_546,plain,
% 3.83/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.83/1.01      | ~ v1_funct_1(X0)
% 3.83/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.83/1.01      | sK2 != X0
% 3.83/1.01      | sK1 != X1 ),
% 3.83/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_547,plain,
% 3.83/1.01      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.83/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.83/1.01      | ~ v1_funct_1(sK2)
% 3.83/1.01      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.83/1.01      inference(unflattening,[status(thm)],[c_546]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_549,plain,
% 3.83/1.01      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.83/1.01      inference(global_propositional_subsumption,
% 3.83/1.01                [status(thm)],
% 3.83/1.01                [c_547,c_38,c_37,c_35]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1369,plain,
% 3.83/1.01      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_549]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1975,plain,
% 3.83/1.01      ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.83/1.01      inference(light_normalisation,[status(thm)],[c_1962,c_1369]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7038,plain,
% 3.83/1.01      ( sK1 = k1_xboole_0 | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_7037,c_1975]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_46,plain,
% 3.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2041,plain,
% 3.83/1.01      ( r2_relset_1(sK1,sK1,sK3,sK3)
% 3.83/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.83/1.01      inference(instantiation,[status(thm)],[c_1391]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2042,plain,
% 3.83/1.01      ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
% 3.83/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_2041]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7102,plain,
% 3.83/1.01      ( sK1 = k1_xboole_0 ),
% 3.83/1.01      inference(global_propositional_subsumption,
% 3.83/1.01                [status(thm)],
% 3.83/1.01                [c_7038,c_46,c_2042]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_9,plain,
% 3.83/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.01      | ~ v1_xboole_0(X1)
% 3.83/1.01      | v1_xboole_0(X0) ),
% 3.83/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1394,plain,
% 3.83/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 3.83/1.01      | ~ v1_xboole_0(X1_52)
% 3.83/1.01      | v1_xboole_0(X0_52) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1951,plain,
% 3.83/1.01      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 3.83/1.01      | v1_xboole_0(X1_52) != iProver_top
% 3.83/1.01      | v1_xboole_0(X0_52) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1394]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2993,plain,
% 3.83/1.01      ( v1_xboole_0(sK2) = iProver_top | v1_xboole_0(sK1) != iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_1967,c_1951]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7134,plain,
% 3.83/1.01      ( v1_xboole_0(sK2) = iProver_top
% 3.83/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.83/1.01      inference(demodulation,[status(thm)],[c_7102,c_2993]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_123,plain,
% 3.83/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1408,plain,
% 3.83/1.01      ( ~ v1_xboole_0(X0_52) | v1_xboole_0(X1_52) | X1_52 != X0_52 ),
% 3.83/1.01      theory(equality) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2560,plain,
% 3.83/1.01      ( v1_xboole_0(X0_52)
% 3.83/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 3.83/1.01      | X0_52 != k1_xboole_0 ),
% 3.83/1.01      inference(instantiation,[status(thm)],[c_1408]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2561,plain,
% 3.83/1.01      ( X0_52 != k1_xboole_0
% 3.83/1.01      | v1_xboole_0(X0_52) = iProver_top
% 3.83/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_2560]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2563,plain,
% 3.83/1.01      ( sK1 != k1_xboole_0
% 3.83/1.01      | v1_xboole_0(sK1) = iProver_top
% 3.83/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.83/1.01      inference(instantiation,[status(thm)],[c_2561]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_8616,plain,
% 3.83/1.01      ( v1_xboole_0(sK2) = iProver_top ),
% 3.83/1.01      inference(global_propositional_subsumption,
% 3.83/1.01                [status(thm)],
% 3.83/1.01                [c_7134,c_46,c_123,c_2042,c_2563,c_2993,c_7038]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_8624,plain,
% 3.83/1.01      ( sK2 = k1_xboole_0 ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_8616,c_3106]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7136,plain,
% 3.83/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.83/1.01      inference(demodulation,[status(thm)],[c_7102,c_1975]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_9130,plain,
% 3.83/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.83/1.01      inference(demodulation,[status(thm)],[c_8624,c_7136]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_14,plain,
% 3.83/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.83/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1389,plain,
% 3.83/1.01      ( m1_subset_1(k6_partfun1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_52,X0_52))) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1956,plain,
% 3.83/1.01      ( m1_subset_1(k6_partfun1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_52,X0_52))) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1389]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2994,plain,
% 3.83/1.01      ( v1_xboole_0(X0_52) != iProver_top
% 3.83/1.01      | v1_xboole_0(k6_partfun1(X0_52)) = iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_1956,c_1951]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5312,plain,
% 3.83/1.01      ( k6_partfun1(X0_52) = k1_xboole_0 | v1_xboole_0(X0_52) != iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_2994,c_3106]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5471,plain,
% 3.83/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_1944,c_5312]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_6,plain,
% 3.83/1.01      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.83/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1396,plain,
% 3.83/1.01      ( k2_funct_1(k6_partfun1(X0_52)) = k6_partfun1(X0_52) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5590,plain,
% 3.83/1.01      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_5471,c_1396]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_5591,plain,
% 3.83/1.01      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.83/1.01      inference(demodulation,[status(thm)],[c_5590,c_5471]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1381,negated_conjecture,
% 3.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.83/1.01      inference(subtyping,[status(esa)],[c_31]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_1964,plain,
% 3.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2992,plain,
% 3.83/1.01      ( v1_xboole_0(sK3) = iProver_top | v1_xboole_0(sK1) != iProver_top ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_1964,c_1951]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_7135,plain,
% 3.83/1.01      ( v1_xboole_0(sK3) = iProver_top
% 3.83/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.83/1.01      inference(demodulation,[status(thm)],[c_7102,c_2992]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2336,plain,
% 3.83/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.83/1.01      | ~ v1_xboole_0(X0_52)
% 3.83/1.01      | v1_xboole_0(sK3) ),
% 3.83/1.01      inference(instantiation,[status(thm)],[c_1394]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2337,plain,
% 3.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.83/1.01      | v1_xboole_0(X0_52) != iProver_top
% 3.83/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 3.83/1.01      inference(predicate_to_equality,[status(thm)],[c_2336]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_2339,plain,
% 3.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.83/1.01      | v1_xboole_0(sK3) = iProver_top
% 3.83/1.01      | v1_xboole_0(sK1) != iProver_top ),
% 3.83/1.01      inference(instantiation,[status(thm)],[c_2337]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_8745,plain,
% 3.83/1.01      ( v1_xboole_0(sK3) = iProver_top ),
% 3.83/1.01      inference(global_propositional_subsumption,
% 3.83/1.01                [status(thm)],
% 3.83/1.01                [c_7135,c_46,c_123,c_2042,c_2339,c_2563,c_7038]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_8753,plain,
% 3.83/1.01      ( sK3 = k1_xboole_0 ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_8745,c_3106]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_9140,plain,
% 3.83/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.83/1.01      inference(light_normalisation,[status(thm)],[c_9130,c_5591,c_8753]) ).
% 3.83/1.01  
% 3.83/1.01  cnf(c_10557,plain,
% 3.83/1.01      ( $false ),
% 3.83/1.01      inference(superposition,[status(thm)],[c_4700,c_9140]) ).
% 3.83/1.01  
% 3.83/1.01  
% 3.83/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/1.01  
% 3.83/1.01  ------                               Statistics
% 3.83/1.01  
% 3.83/1.01  ------ General
% 3.83/1.01  
% 3.83/1.01  abstr_ref_over_cycles:                  0
% 3.83/1.01  abstr_ref_under_cycles:                 0
% 3.83/1.01  gc_basic_clause_elim:                   0
% 3.83/1.01  forced_gc_time:                         0
% 3.83/1.01  parsing_time:                           0.021
% 3.83/1.01  unif_index_cands_time:                  0.
% 3.83/1.01  unif_index_add_time:                    0.
% 3.83/1.01  orderings_time:                         0.
% 3.83/1.01  out_proof_time:                         0.015
% 3.83/1.01  total_time:                             0.452
% 3.83/1.01  num_of_symbols:                         58
% 3.83/1.01  num_of_terms:                           14042
% 3.83/1.01  
% 3.83/1.01  ------ Preprocessing
% 3.83/1.01  
% 3.83/1.01  num_of_splits:                          0
% 3.83/1.01  num_of_split_atoms:                     0
% 3.83/1.01  num_of_reused_defs:                     0
% 3.83/1.01  num_eq_ax_congr_red:                    24
% 3.83/1.01  num_of_sem_filtered_clauses:            3
% 3.83/1.01  num_of_subtypes:                        3
% 3.83/1.01  monotx_restored_types:                  1
% 3.83/1.01  sat_num_of_epr_types:                   0
% 3.83/1.01  sat_num_of_non_cyclic_types:            0
% 3.83/1.01  sat_guarded_non_collapsed_types:        1
% 3.83/1.01  num_pure_diseq_elim:                    0
% 3.83/1.01  simp_replaced_by:                       0
% 3.83/1.01  res_preprocessed:                       172
% 3.83/1.01  prep_upred:                             0
% 3.83/1.01  prep_unflattend:                        66
% 3.83/1.01  smt_new_axioms:                         0
% 3.83/1.01  pred_elim_cands:                        7
% 3.83/1.01  pred_elim:                              2
% 3.83/1.01  pred_elim_cl:                           1
% 3.83/1.01  pred_elim_cycles:                       8
% 3.83/1.01  merged_defs:                            0
% 3.83/1.01  merged_defs_ncl:                        0
% 3.83/1.01  bin_hyper_res:                          0
% 3.83/1.01  prep_cycles:                            4
% 3.83/1.01  pred_elim_time:                         0.026
% 3.83/1.01  splitting_time:                         0.
% 3.83/1.01  sem_filter_time:                        0.
% 3.83/1.01  monotx_time:                            0.001
% 3.83/1.01  subtype_inf_time:                       0.002
% 3.83/1.01  
% 3.83/1.01  ------ Problem properties
% 3.83/1.01  
% 3.83/1.01  clauses:                                34
% 3.83/1.01  conjectures:                            8
% 3.83/1.01  epr:                                    8
% 3.83/1.01  horn:                                   33
% 3.83/1.01  ground:                                 13
% 3.83/1.01  unary:                                  17
% 3.83/1.01  binary:                                 4
% 3.83/1.01  lits:                                   82
% 3.83/1.01  lits_eq:                                15
% 3.83/1.01  fd_pure:                                0
% 3.83/1.01  fd_pseudo:                              0
% 3.83/1.01  fd_cond:                                0
% 3.83/1.01  fd_pseudo_cond:                         4
% 3.83/1.01  ac_symbols:                             0
% 3.83/1.01  
% 3.83/1.01  ------ Propositional Solver
% 3.83/1.01  
% 3.83/1.01  prop_solver_calls:                      32
% 3.83/1.01  prop_fast_solver_calls:                 1594
% 3.83/1.01  smt_solver_calls:                       0
% 3.83/1.01  smt_fast_solver_calls:                  0
% 3.83/1.01  prop_num_of_clauses:                    4617
% 3.83/1.01  prop_preprocess_simplified:             10553
% 3.83/1.01  prop_fo_subsumed:                       82
% 3.83/1.01  prop_solver_time:                       0.
% 3.83/1.01  smt_solver_time:                        0.
% 3.83/1.01  smt_fast_solver_time:                   0.
% 3.83/1.01  prop_fast_solver_time:                  0.
% 3.83/1.01  prop_unsat_core_time:                   0.
% 3.83/1.01  
% 3.83/1.01  ------ QBF
% 3.83/1.01  
% 3.83/1.01  qbf_q_res:                              0
% 3.83/1.01  qbf_num_tautologies:                    0
% 3.83/1.01  qbf_prep_cycles:                        0
% 3.83/1.01  
% 3.83/1.01  ------ BMC1
% 3.83/1.01  
% 3.83/1.01  bmc1_current_bound:                     -1
% 3.83/1.01  bmc1_last_solved_bound:                 -1
% 3.83/1.01  bmc1_unsat_core_size:                   -1
% 3.83/1.01  bmc1_unsat_core_parents_size:           -1
% 3.83/1.01  bmc1_merge_next_fun:                    0
% 3.83/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.83/1.01  
% 3.83/1.01  ------ Instantiation
% 3.83/1.01  
% 3.83/1.01  inst_num_of_clauses:                    1300
% 3.83/1.01  inst_num_in_passive:                    448
% 3.83/1.01  inst_num_in_active:                     527
% 3.83/1.01  inst_num_in_unprocessed:                325
% 3.83/1.01  inst_num_of_loops:                      720
% 3.83/1.01  inst_num_of_learning_restarts:          0
% 3.83/1.01  inst_num_moves_active_passive:          188
% 3.83/1.01  inst_lit_activity:                      0
% 3.83/1.01  inst_lit_activity_moves:                0
% 3.83/1.01  inst_num_tautologies:                   0
% 3.83/1.01  inst_num_prop_implied:                  0
% 3.83/1.01  inst_num_existing_simplified:           0
% 3.83/1.01  inst_num_eq_res_simplified:             0
% 3.83/1.01  inst_num_child_elim:                    0
% 3.83/1.01  inst_num_of_dismatching_blockings:      905
% 3.83/1.01  inst_num_of_non_proper_insts:           1946
% 3.83/1.01  inst_num_of_duplicates:                 0
% 3.83/1.01  inst_inst_num_from_inst_to_res:         0
% 3.83/1.01  inst_dismatching_checking_time:         0.
% 3.83/1.01  
% 3.83/1.01  ------ Resolution
% 3.83/1.01  
% 3.83/1.01  res_num_of_clauses:                     0
% 3.83/1.01  res_num_in_passive:                     0
% 3.83/1.01  res_num_in_active:                      0
% 3.83/1.01  res_num_of_loops:                       176
% 3.83/1.01  res_forward_subset_subsumed:            56
% 3.83/1.01  res_backward_subset_subsumed:           0
% 3.83/1.01  res_forward_subsumed:                   0
% 3.83/1.01  res_backward_subsumed:                  0
% 3.83/1.01  res_forward_subsumption_resolution:     4
% 3.83/1.01  res_backward_subsumption_resolution:    0
% 3.83/1.01  res_clause_to_clause_subsumption:       497
% 3.83/1.01  res_orphan_elimination:                 0
% 3.83/1.01  res_tautology_del:                      75
% 3.83/1.01  res_num_eq_res_simplified:              0
% 3.83/1.01  res_num_sel_changes:                    0
% 3.83/1.01  res_moves_from_active_to_pass:          0
% 3.83/1.01  
% 3.83/1.01  ------ Superposition
% 3.83/1.01  
% 3.83/1.01  sup_time_total:                         0.
% 3.83/1.01  sup_time_generating:                    0.
% 3.83/1.01  sup_time_sim_full:                      0.
% 3.83/1.01  sup_time_sim_immed:                     0.
% 3.83/1.01  
% 3.83/1.01  sup_num_of_clauses:                     117
% 3.83/1.01  sup_num_in_active:                      70
% 3.83/1.01  sup_num_in_passive:                     47
% 3.83/1.01  sup_num_of_loops:                       142
% 3.83/1.01  sup_fw_superposition:                   108
% 3.83/1.01  sup_bw_superposition:                   120
% 3.83/1.01  sup_immediate_simplified:               88
% 3.83/1.01  sup_given_eliminated:                   2
% 3.83/1.01  comparisons_done:                       0
% 3.83/1.01  comparisons_avoided:                    3
% 3.83/1.01  
% 3.83/1.01  ------ Simplifications
% 3.83/1.01  
% 3.83/1.01  
% 3.83/1.01  sim_fw_subset_subsumed:                 20
% 3.83/1.01  sim_bw_subset_subsumed:                 7
% 3.83/1.01  sim_fw_subsumed:                        21
% 3.83/1.01  sim_bw_subsumed:                        4
% 3.83/1.01  sim_fw_subsumption_res:                 0
% 3.83/1.01  sim_bw_subsumption_res:                 0
% 3.83/1.01  sim_tautology_del:                      5
% 3.83/1.01  sim_eq_tautology_del:                   39
% 3.83/1.01  sim_eq_res_simp:                        4
% 3.83/1.01  sim_fw_demodulated:                     24
% 3.83/1.01  sim_bw_demodulated:                     71
% 3.83/1.01  sim_light_normalised:                   59
% 3.83/1.01  sim_joinable_taut:                      0
% 3.83/1.01  sim_joinable_simp:                      0
% 3.83/1.01  sim_ac_normalised:                      0
% 3.83/1.01  sim_smt_subsumption:                    0
% 3.83/1.01  
%------------------------------------------------------------------------------
