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
% DateTime   : Thu Dec  3 12:07:08 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_38)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f19])).

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
    inference(flattening,[],[f43])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f48,f47])).

fof(f82,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f41])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f39])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f54,f70,f70])).

cnf(c_24,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1231,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1733,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1231])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1227,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1737,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_348,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_15])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_360,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_348,c_5])).

cnf(c_1223,plain,
    ( ~ v2_funct_2(X0_51,X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | k2_relat_1(X0_51) = X1_51 ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_1741,plain,
    ( k2_relat_1(X0_51) = X1_51
    | v2_funct_2(X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1223])).

cnf(c_5098,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1741])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_436,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_30])).

cnf(c_437,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_438,plain,
    ( v2_funct_2(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_5208,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5098,c_33,c_36,c_438])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1239,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | k2_relset_1(X1_51,X2_51,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1725,plain,
    ( k2_relset_1(X0_51,X1_51,X2_51) = k2_relat_1(X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1239])).

cnf(c_2964,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1737,c_1725])).

cnf(c_22,plain,
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
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_179,plain,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_21])).

cnf(c_180,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_1224,plain,
    ( ~ r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51))
    | ~ v1_funct_2(X3_51,X1_51,X0_51)
    | ~ v1_funct_2(X2_51,X0_51,X1_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
    | ~ v1_funct_1(X2_51)
    | ~ v1_funct_1(X3_51)
    | k2_relset_1(X0_51,X1_51,X2_51) != X1_51
    | k2_funct_1(X2_51) = X3_51
    | k1_xboole_0 = X1_51
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_180])).

cnf(c_1740,plain,
    ( k2_relset_1(X0_51,X1_51,X2_51) != X1_51
    | k2_funct_1(X2_51) = X3_51
    | k1_xboole_0 = X1_51
    | k1_xboole_0 = X0_51
    | r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51)) != iProver_top
    | v1_funct_2(X3_51,X1_51,X0_51) != iProver_top
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1224])).

cnf(c_4078,plain,
    ( k2_funct_1(sK1) = X0_51
    | k2_relat_1(sK1) != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2964,c_1740])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4768,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_relat_1(sK1) != sK0
    | k2_funct_1(sK1) = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4078,c_33,c_34,c_36])).

cnf(c_4769,plain,
    ( k2_funct_1(sK1) = X0_51
    | k2_relat_1(sK1) != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4768])).

cnf(c_5210,plain,
    ( k2_funct_1(sK1) = X0_51
    | sK0 != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5208,c_4769])).

cnf(c_5212,plain,
    ( k2_funct_1(sK1) = X0_51
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5210])).

cnf(c_5566,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_5212])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5567,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5566])).

cnf(c_5569,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5566,c_37,c_38,c_40])).

cnf(c_5570,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5569])).

cnf(c_23,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1232,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1732,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_455,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_456,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_458,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_32,c_31,c_29])).

cnf(c_1218,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_1745,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1732,c_1218])).

cnf(c_5571,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5570,c_1745])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1238,plain,
    ( r2_relset_1(X0_51,X1_51,X2_51,X2_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1806,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_1807,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1806])).

cnf(c_5642,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5571,c_40,c_1807])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1244,plain,
    ( ~ v1_relat_1(X0_51)
    | k2_relat_1(X0_51) != k1_xboole_0
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1721,plain,
    ( k2_relat_1(X0_51) != k1_xboole_0
    | k1_xboole_0 = X0_51
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_5216,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5208,c_1721])).

cnf(c_1241,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1723,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1241])).

cnf(c_2412,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1723])).

cnf(c_5535,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5216,c_2412])).

cnf(c_5536,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5535])).

cnf(c_5646,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5642,c_5536])).

cnf(c_5693,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5646])).

cnf(c_1230,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1734,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_5097,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1741])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_425,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_426,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_427,plain,
    ( v2_funct_2(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_5197,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5097,c_37,c_40,c_427])).

cnf(c_5205,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5197,c_1721])).

cnf(c_2411,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1723])).

cnf(c_5312,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5205,c_2411])).

cnf(c_5313,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5312])).

cnf(c_5649,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5642,c_5313])).

cnf(c_5677,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5649])).

cnf(c_5664,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5642,c_1745])).

cnf(c_5685,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5677,c_5664])).

cnf(c_5695,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5693,c_5685])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1246,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1719,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1234,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1730,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1234])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1240,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_xboole_0(X2_51)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1724,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_xboole_0(X2_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_2746,plain,
    ( v1_xboole_0(X0_51) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1724])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1245,plain,
    ( ~ v1_xboole_0(X0_51)
    | ~ v1_xboole_0(X1_51)
    | X1_51 = X0_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1720,plain,
    ( X0_51 = X1_51
    | v1_xboole_0(X1_51) != iProver_top
    | v1_xboole_0(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_4184,plain,
    ( k6_partfun1(X0_51) = X1_51
    | v1_xboole_0(X0_51) != iProver_top
    | v1_xboole_0(X1_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_2746,c_1720])).

cnf(c_4192,plain,
    ( k6_partfun1(k1_xboole_0) = X0_51
    | v1_xboole_0(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_4184])).

cnf(c_4438,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1719,c_4192])).

cnf(c_4,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1242,plain,
    ( k2_funct_1(k6_partfun1(X0_51)) = k6_partfun1(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_4782,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4438,c_1242])).

cnf(c_4783,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4782,c_4438])).

cnf(c_5706,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5695,c_4783])).

cnf(c_1726,plain,
    ( r2_relset_1(X0_51,X1_51,X2_51,X2_51) = iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_2970,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1726])).

cnf(c_4776,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4438,c_2970])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5706,c_4776])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:26:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.43/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.04  
% 3.43/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.43/1.04  
% 3.43/1.04  ------  iProver source info
% 3.43/1.04  
% 3.43/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.43/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.43/1.04  git: non_committed_changes: false
% 3.43/1.04  git: last_make_outside_of_git: false
% 3.43/1.04  
% 3.43/1.04  ------ 
% 3.43/1.04  
% 3.43/1.04  ------ Input Options
% 3.43/1.04  
% 3.43/1.04  --out_options                           all
% 3.43/1.04  --tptp_safe_out                         true
% 3.43/1.04  --problem_path                          ""
% 3.43/1.04  --include_path                          ""
% 3.43/1.04  --clausifier                            res/vclausify_rel
% 3.43/1.04  --clausifier_options                    ""
% 3.43/1.04  --stdin                                 false
% 3.43/1.04  --stats_out                             all
% 3.43/1.04  
% 3.43/1.04  ------ General Options
% 3.43/1.04  
% 3.43/1.04  --fof                                   false
% 3.43/1.04  --time_out_real                         305.
% 3.43/1.04  --time_out_virtual                      -1.
% 3.43/1.04  --symbol_type_check                     false
% 3.43/1.04  --clausify_out                          false
% 3.43/1.04  --sig_cnt_out                           false
% 3.43/1.04  --trig_cnt_out                          false
% 3.43/1.04  --trig_cnt_out_tolerance                1.
% 3.43/1.04  --trig_cnt_out_sk_spl                   false
% 3.43/1.04  --abstr_cl_out                          false
% 3.43/1.04  
% 3.43/1.04  ------ Global Options
% 3.43/1.04  
% 3.43/1.04  --schedule                              default
% 3.43/1.04  --add_important_lit                     false
% 3.43/1.04  --prop_solver_per_cl                    1000
% 3.43/1.04  --min_unsat_core                        false
% 3.43/1.04  --soft_assumptions                      false
% 3.43/1.04  --soft_lemma_size                       3
% 3.43/1.04  --prop_impl_unit_size                   0
% 3.43/1.04  --prop_impl_unit                        []
% 3.43/1.04  --share_sel_clauses                     true
% 3.43/1.04  --reset_solvers                         false
% 3.43/1.04  --bc_imp_inh                            [conj_cone]
% 3.43/1.04  --conj_cone_tolerance                   3.
% 3.43/1.04  --extra_neg_conj                        none
% 3.43/1.04  --large_theory_mode                     true
% 3.43/1.04  --prolific_symb_bound                   200
% 3.43/1.04  --lt_threshold                          2000
% 3.43/1.04  --clause_weak_htbl                      true
% 3.43/1.04  --gc_record_bc_elim                     false
% 3.43/1.04  
% 3.43/1.04  ------ Preprocessing Options
% 3.43/1.04  
% 3.43/1.04  --preprocessing_flag                    true
% 3.43/1.04  --time_out_prep_mult                    0.1
% 3.43/1.04  --splitting_mode                        input
% 3.43/1.04  --splitting_grd                         true
% 3.43/1.04  --splitting_cvd                         false
% 3.43/1.04  --splitting_cvd_svl                     false
% 3.43/1.04  --splitting_nvd                         32
% 3.43/1.04  --sub_typing                            true
% 3.43/1.04  --prep_gs_sim                           true
% 3.43/1.04  --prep_unflatten                        true
% 3.43/1.04  --prep_res_sim                          true
% 3.43/1.04  --prep_upred                            true
% 3.43/1.04  --prep_sem_filter                       exhaustive
% 3.43/1.04  --prep_sem_filter_out                   false
% 3.43/1.04  --pred_elim                             true
% 3.43/1.04  --res_sim_input                         true
% 3.43/1.04  --eq_ax_congr_red                       true
% 3.43/1.04  --pure_diseq_elim                       true
% 3.43/1.04  --brand_transform                       false
% 3.43/1.04  --non_eq_to_eq                          false
% 3.43/1.04  --prep_def_merge                        true
% 3.43/1.04  --prep_def_merge_prop_impl              false
% 3.43/1.04  --prep_def_merge_mbd                    true
% 3.43/1.04  --prep_def_merge_tr_red                 false
% 3.43/1.04  --prep_def_merge_tr_cl                  false
% 3.43/1.04  --smt_preprocessing                     true
% 3.43/1.04  --smt_ac_axioms                         fast
% 3.43/1.04  --preprocessed_out                      false
% 3.43/1.04  --preprocessed_stats                    false
% 3.43/1.04  
% 3.43/1.04  ------ Abstraction refinement Options
% 3.43/1.04  
% 3.43/1.04  --abstr_ref                             []
% 3.43/1.04  --abstr_ref_prep                        false
% 3.43/1.04  --abstr_ref_until_sat                   false
% 3.43/1.04  --abstr_ref_sig_restrict                funpre
% 3.43/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.04  --abstr_ref_under                       []
% 3.43/1.04  
% 3.43/1.04  ------ SAT Options
% 3.43/1.04  
% 3.43/1.04  --sat_mode                              false
% 3.43/1.04  --sat_fm_restart_options                ""
% 3.43/1.04  --sat_gr_def                            false
% 3.43/1.04  --sat_epr_types                         true
% 3.43/1.04  --sat_non_cyclic_types                  false
% 3.43/1.04  --sat_finite_models                     false
% 3.43/1.04  --sat_fm_lemmas                         false
% 3.43/1.04  --sat_fm_prep                           false
% 3.43/1.04  --sat_fm_uc_incr                        true
% 3.43/1.04  --sat_out_model                         small
% 3.43/1.04  --sat_out_clauses                       false
% 3.43/1.04  
% 3.43/1.04  ------ QBF Options
% 3.43/1.04  
% 3.43/1.04  --qbf_mode                              false
% 3.43/1.04  --qbf_elim_univ                         false
% 3.43/1.04  --qbf_dom_inst                          none
% 3.43/1.04  --qbf_dom_pre_inst                      false
% 3.43/1.04  --qbf_sk_in                             false
% 3.43/1.04  --qbf_pred_elim                         true
% 3.43/1.04  --qbf_split                             512
% 3.43/1.04  
% 3.43/1.04  ------ BMC1 Options
% 3.43/1.04  
% 3.43/1.04  --bmc1_incremental                      false
% 3.43/1.04  --bmc1_axioms                           reachable_all
% 3.43/1.04  --bmc1_min_bound                        0
% 3.43/1.04  --bmc1_max_bound                        -1
% 3.43/1.04  --bmc1_max_bound_default                -1
% 3.43/1.04  --bmc1_symbol_reachability              true
% 3.43/1.04  --bmc1_property_lemmas                  false
% 3.43/1.04  --bmc1_k_induction                      false
% 3.43/1.04  --bmc1_non_equiv_states                 false
% 3.43/1.04  --bmc1_deadlock                         false
% 3.43/1.04  --bmc1_ucm                              false
% 3.43/1.04  --bmc1_add_unsat_core                   none
% 3.43/1.04  --bmc1_unsat_core_children              false
% 3.43/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.04  --bmc1_out_stat                         full
% 3.43/1.04  --bmc1_ground_init                      false
% 3.43/1.04  --bmc1_pre_inst_next_state              false
% 3.43/1.04  --bmc1_pre_inst_state                   false
% 3.43/1.04  --bmc1_pre_inst_reach_state             false
% 3.43/1.04  --bmc1_out_unsat_core                   false
% 3.43/1.04  --bmc1_aig_witness_out                  false
% 3.43/1.04  --bmc1_verbose                          false
% 3.43/1.04  --bmc1_dump_clauses_tptp                false
% 3.43/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.04  --bmc1_dump_file                        -
% 3.43/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.04  --bmc1_ucm_extend_mode                  1
% 3.43/1.04  --bmc1_ucm_init_mode                    2
% 3.43/1.04  --bmc1_ucm_cone_mode                    none
% 3.43/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.04  --bmc1_ucm_relax_model                  4
% 3.43/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.04  --bmc1_ucm_layered_model                none
% 3.43/1.04  --bmc1_ucm_max_lemma_size               10
% 3.43/1.04  
% 3.43/1.04  ------ AIG Options
% 3.43/1.04  
% 3.43/1.04  --aig_mode                              false
% 3.43/1.04  
% 3.43/1.04  ------ Instantiation Options
% 3.43/1.04  
% 3.43/1.04  --instantiation_flag                    true
% 3.43/1.04  --inst_sos_flag                         true
% 3.43/1.04  --inst_sos_phase                        true
% 3.43/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.04  --inst_lit_sel_side                     num_symb
% 3.43/1.04  --inst_solver_per_active                1400
% 3.43/1.04  --inst_solver_calls_frac                1.
% 3.43/1.04  --inst_passive_queue_type               priority_queues
% 3.43/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.04  --inst_passive_queues_freq              [25;2]
% 3.43/1.04  --inst_dismatching                      true
% 3.43/1.04  --inst_eager_unprocessed_to_passive     true
% 3.43/1.04  --inst_prop_sim_given                   true
% 3.43/1.04  --inst_prop_sim_new                     false
% 3.43/1.04  --inst_subs_new                         false
% 3.43/1.04  --inst_eq_res_simp                      false
% 3.43/1.04  --inst_subs_given                       false
% 3.43/1.04  --inst_orphan_elimination               true
% 3.43/1.04  --inst_learning_loop_flag               true
% 3.43/1.04  --inst_learning_start                   3000
% 3.43/1.04  --inst_learning_factor                  2
% 3.43/1.04  --inst_start_prop_sim_after_learn       3
% 3.43/1.04  --inst_sel_renew                        solver
% 3.43/1.04  --inst_lit_activity_flag                true
% 3.43/1.04  --inst_restr_to_given                   false
% 3.43/1.04  --inst_activity_threshold               500
% 3.43/1.04  --inst_out_proof                        true
% 3.43/1.04  
% 3.43/1.04  ------ Resolution Options
% 3.43/1.04  
% 3.43/1.04  --resolution_flag                       true
% 3.43/1.04  --res_lit_sel                           adaptive
% 3.43/1.04  --res_lit_sel_side                      none
% 3.43/1.04  --res_ordering                          kbo
% 3.43/1.04  --res_to_prop_solver                    active
% 3.43/1.04  --res_prop_simpl_new                    false
% 3.43/1.04  --res_prop_simpl_given                  true
% 3.43/1.04  --res_passive_queue_type                priority_queues
% 3.43/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.04  --res_passive_queues_freq               [15;5]
% 3.43/1.04  --res_forward_subs                      full
% 3.43/1.04  --res_backward_subs                     full
% 3.43/1.04  --res_forward_subs_resolution           true
% 3.43/1.04  --res_backward_subs_resolution          true
% 3.43/1.04  --res_orphan_elimination                true
% 3.43/1.04  --res_time_limit                        2.
% 3.43/1.04  --res_out_proof                         true
% 3.43/1.04  
% 3.43/1.04  ------ Superposition Options
% 3.43/1.04  
% 3.43/1.04  --superposition_flag                    true
% 3.43/1.04  --sup_passive_queue_type                priority_queues
% 3.43/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.04  --demod_completeness_check              fast
% 3.43/1.04  --demod_use_ground                      true
% 3.43/1.04  --sup_to_prop_solver                    passive
% 3.43/1.04  --sup_prop_simpl_new                    true
% 3.43/1.04  --sup_prop_simpl_given                  true
% 3.43/1.04  --sup_fun_splitting                     true
% 3.43/1.04  --sup_smt_interval                      50000
% 3.43/1.04  
% 3.43/1.04  ------ Superposition Simplification Setup
% 3.43/1.04  
% 3.43/1.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.43/1.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.43/1.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.43/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.43/1.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.43/1.04  --sup_immed_triv                        [TrivRules]
% 3.43/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.04  --sup_immed_bw_main                     []
% 3.43/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.43/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.04  --sup_input_bw                          []
% 3.43/1.04  
% 3.43/1.04  ------ Combination Options
% 3.43/1.04  
% 3.43/1.04  --comb_res_mult                         3
% 3.43/1.04  --comb_sup_mult                         2
% 3.43/1.04  --comb_inst_mult                        10
% 3.43/1.04  
% 3.43/1.04  ------ Debug Options
% 3.43/1.04  
% 3.43/1.04  --dbg_backtrace                         false
% 3.43/1.04  --dbg_dump_prop_clauses                 false
% 3.43/1.04  --dbg_dump_prop_clauses_file            -
% 3.43/1.04  --dbg_out_stat                          false
% 3.43/1.04  ------ Parsing...
% 3.43/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.43/1.04  
% 3.43/1.04  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.43/1.04  
% 3.43/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.43/1.04  
% 3.43/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.43/1.04  ------ Proving...
% 3.43/1.04  ------ Problem Properties 
% 3.43/1.04  
% 3.43/1.04  
% 3.43/1.04  clauses                                 29
% 3.43/1.04  conjectures                             8
% 3.43/1.04  EPR                                     8
% 3.43/1.04  Horn                                    28
% 3.43/1.04  unary                                   15
% 3.43/1.04  binary                                  4
% 3.43/1.04  lits                                    71
% 3.43/1.04  lits eq                                 15
% 3.43/1.04  fd_pure                                 0
% 3.43/1.04  fd_pseudo                               0
% 3.43/1.04  fd_cond                                 2
% 3.43/1.04  fd_pseudo_cond                          4
% 3.43/1.04  AC symbols                              0
% 3.43/1.04  
% 3.43/1.04  ------ Schedule dynamic 5 is on 
% 3.43/1.04  
% 3.43/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.43/1.04  
% 3.43/1.04  
% 3.43/1.04  ------ 
% 3.43/1.04  Current options:
% 3.43/1.04  ------ 
% 3.43/1.04  
% 3.43/1.04  ------ Input Options
% 3.43/1.04  
% 3.43/1.04  --out_options                           all
% 3.43/1.04  --tptp_safe_out                         true
% 3.43/1.04  --problem_path                          ""
% 3.43/1.04  --include_path                          ""
% 3.43/1.04  --clausifier                            res/vclausify_rel
% 3.43/1.04  --clausifier_options                    ""
% 3.43/1.04  --stdin                                 false
% 3.43/1.04  --stats_out                             all
% 3.43/1.04  
% 3.43/1.04  ------ General Options
% 3.43/1.04  
% 3.43/1.04  --fof                                   false
% 3.43/1.04  --time_out_real                         305.
% 3.43/1.04  --time_out_virtual                      -1.
% 3.43/1.04  --symbol_type_check                     false
% 3.43/1.04  --clausify_out                          false
% 3.43/1.04  --sig_cnt_out                           false
% 3.43/1.04  --trig_cnt_out                          false
% 3.43/1.04  --trig_cnt_out_tolerance                1.
% 3.43/1.04  --trig_cnt_out_sk_spl                   false
% 3.43/1.04  --abstr_cl_out                          false
% 3.43/1.04  
% 3.43/1.04  ------ Global Options
% 3.43/1.04  
% 3.43/1.04  --schedule                              default
% 3.43/1.04  --add_important_lit                     false
% 3.43/1.04  --prop_solver_per_cl                    1000
% 3.43/1.04  --min_unsat_core                        false
% 3.43/1.04  --soft_assumptions                      false
% 3.43/1.04  --soft_lemma_size                       3
% 3.43/1.04  --prop_impl_unit_size                   0
% 3.43/1.04  --prop_impl_unit                        []
% 3.43/1.04  --share_sel_clauses                     true
% 3.43/1.04  --reset_solvers                         false
% 3.43/1.04  --bc_imp_inh                            [conj_cone]
% 3.43/1.04  --conj_cone_tolerance                   3.
% 3.43/1.04  --extra_neg_conj                        none
% 3.43/1.04  --large_theory_mode                     true
% 3.43/1.04  --prolific_symb_bound                   200
% 3.43/1.04  --lt_threshold                          2000
% 3.43/1.04  --clause_weak_htbl                      true
% 3.43/1.04  --gc_record_bc_elim                     false
% 3.43/1.04  
% 3.43/1.04  ------ Preprocessing Options
% 3.43/1.04  
% 3.43/1.04  --preprocessing_flag                    true
% 3.43/1.04  --time_out_prep_mult                    0.1
% 3.43/1.04  --splitting_mode                        input
% 3.43/1.04  --splitting_grd                         true
% 3.43/1.04  --splitting_cvd                         false
% 3.43/1.04  --splitting_cvd_svl                     false
% 3.43/1.04  --splitting_nvd                         32
% 3.43/1.04  --sub_typing                            true
% 3.43/1.04  --prep_gs_sim                           true
% 3.43/1.04  --prep_unflatten                        true
% 3.43/1.04  --prep_res_sim                          true
% 3.43/1.04  --prep_upred                            true
% 3.43/1.04  --prep_sem_filter                       exhaustive
% 3.43/1.04  --prep_sem_filter_out                   false
% 3.43/1.04  --pred_elim                             true
% 3.43/1.04  --res_sim_input                         true
% 3.43/1.04  --eq_ax_congr_red                       true
% 3.43/1.04  --pure_diseq_elim                       true
% 3.43/1.04  --brand_transform                       false
% 3.43/1.04  --non_eq_to_eq                          false
% 3.43/1.04  --prep_def_merge                        true
% 3.43/1.04  --prep_def_merge_prop_impl              false
% 3.43/1.04  --prep_def_merge_mbd                    true
% 3.43/1.04  --prep_def_merge_tr_red                 false
% 3.43/1.04  --prep_def_merge_tr_cl                  false
% 3.43/1.04  --smt_preprocessing                     true
% 3.43/1.04  --smt_ac_axioms                         fast
% 3.43/1.04  --preprocessed_out                      false
% 3.43/1.04  --preprocessed_stats                    false
% 3.43/1.04  
% 3.43/1.04  ------ Abstraction refinement Options
% 3.43/1.04  
% 3.43/1.04  --abstr_ref                             []
% 3.43/1.04  --abstr_ref_prep                        false
% 3.43/1.04  --abstr_ref_until_sat                   false
% 3.43/1.04  --abstr_ref_sig_restrict                funpre
% 3.43/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.04  --abstr_ref_under                       []
% 3.43/1.04  
% 3.43/1.04  ------ SAT Options
% 3.43/1.04  
% 3.43/1.04  --sat_mode                              false
% 3.43/1.04  --sat_fm_restart_options                ""
% 3.43/1.04  --sat_gr_def                            false
% 3.43/1.04  --sat_epr_types                         true
% 3.43/1.04  --sat_non_cyclic_types                  false
% 3.43/1.04  --sat_finite_models                     false
% 3.43/1.04  --sat_fm_lemmas                         false
% 3.43/1.04  --sat_fm_prep                           false
% 3.43/1.04  --sat_fm_uc_incr                        true
% 3.43/1.04  --sat_out_model                         small
% 3.43/1.04  --sat_out_clauses                       false
% 3.43/1.04  
% 3.43/1.04  ------ QBF Options
% 3.43/1.04  
% 3.43/1.04  --qbf_mode                              false
% 3.43/1.04  --qbf_elim_univ                         false
% 3.43/1.04  --qbf_dom_inst                          none
% 3.43/1.04  --qbf_dom_pre_inst                      false
% 3.43/1.04  --qbf_sk_in                             false
% 3.43/1.04  --qbf_pred_elim                         true
% 3.43/1.04  --qbf_split                             512
% 3.43/1.04  
% 3.43/1.04  ------ BMC1 Options
% 3.43/1.04  
% 3.43/1.04  --bmc1_incremental                      false
% 3.43/1.04  --bmc1_axioms                           reachable_all
% 3.43/1.04  --bmc1_min_bound                        0
% 3.43/1.04  --bmc1_max_bound                        -1
% 3.43/1.04  --bmc1_max_bound_default                -1
% 3.43/1.04  --bmc1_symbol_reachability              true
% 3.43/1.04  --bmc1_property_lemmas                  false
% 3.43/1.04  --bmc1_k_induction                      false
% 3.43/1.04  --bmc1_non_equiv_states                 false
% 3.43/1.04  --bmc1_deadlock                         false
% 3.43/1.04  --bmc1_ucm                              false
% 3.43/1.04  --bmc1_add_unsat_core                   none
% 3.43/1.04  --bmc1_unsat_core_children              false
% 3.43/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.04  --bmc1_out_stat                         full
% 3.43/1.04  --bmc1_ground_init                      false
% 3.43/1.04  --bmc1_pre_inst_next_state              false
% 3.43/1.04  --bmc1_pre_inst_state                   false
% 3.43/1.04  --bmc1_pre_inst_reach_state             false
% 3.43/1.04  --bmc1_out_unsat_core                   false
% 3.43/1.04  --bmc1_aig_witness_out                  false
% 3.43/1.04  --bmc1_verbose                          false
% 3.43/1.04  --bmc1_dump_clauses_tptp                false
% 3.43/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.04  --bmc1_dump_file                        -
% 3.43/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.04  --bmc1_ucm_extend_mode                  1
% 3.43/1.04  --bmc1_ucm_init_mode                    2
% 3.43/1.04  --bmc1_ucm_cone_mode                    none
% 3.43/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.04  --bmc1_ucm_relax_model                  4
% 3.43/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.04  --bmc1_ucm_layered_model                none
% 3.43/1.04  --bmc1_ucm_max_lemma_size               10
% 3.43/1.04  
% 3.43/1.04  ------ AIG Options
% 3.43/1.04  
% 3.43/1.04  --aig_mode                              false
% 3.43/1.04  
% 3.43/1.04  ------ Instantiation Options
% 3.43/1.04  
% 3.43/1.04  --instantiation_flag                    true
% 3.43/1.04  --inst_sos_flag                         true
% 3.43/1.04  --inst_sos_phase                        true
% 3.43/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.04  --inst_lit_sel_side                     none
% 3.43/1.04  --inst_solver_per_active                1400
% 3.43/1.04  --inst_solver_calls_frac                1.
% 3.43/1.04  --inst_passive_queue_type               priority_queues
% 3.43/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.04  --inst_passive_queues_freq              [25;2]
% 3.43/1.04  --inst_dismatching                      true
% 3.43/1.04  --inst_eager_unprocessed_to_passive     true
% 3.43/1.04  --inst_prop_sim_given                   true
% 3.43/1.04  --inst_prop_sim_new                     false
% 3.43/1.04  --inst_subs_new                         false
% 3.43/1.04  --inst_eq_res_simp                      false
% 3.43/1.04  --inst_subs_given                       false
% 3.43/1.04  --inst_orphan_elimination               true
% 3.43/1.04  --inst_learning_loop_flag               true
% 3.43/1.04  --inst_learning_start                   3000
% 3.43/1.04  --inst_learning_factor                  2
% 3.43/1.04  --inst_start_prop_sim_after_learn       3
% 3.43/1.04  --inst_sel_renew                        solver
% 3.43/1.04  --inst_lit_activity_flag                true
% 3.43/1.04  --inst_restr_to_given                   false
% 3.43/1.04  --inst_activity_threshold               500
% 3.43/1.04  --inst_out_proof                        true
% 3.43/1.04  
% 3.43/1.04  ------ Resolution Options
% 3.43/1.04  
% 3.43/1.04  --resolution_flag                       false
% 3.43/1.04  --res_lit_sel                           adaptive
% 3.43/1.04  --res_lit_sel_side                      none
% 3.43/1.04  --res_ordering                          kbo
% 3.43/1.04  --res_to_prop_solver                    active
% 3.43/1.04  --res_prop_simpl_new                    false
% 3.43/1.04  --res_prop_simpl_given                  true
% 3.43/1.04  --res_passive_queue_type                priority_queues
% 3.43/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.04  --res_passive_queues_freq               [15;5]
% 3.43/1.04  --res_forward_subs                      full
% 3.43/1.04  --res_backward_subs                     full
% 3.43/1.04  --res_forward_subs_resolution           true
% 3.43/1.04  --res_backward_subs_resolution          true
% 3.43/1.04  --res_orphan_elimination                true
% 3.43/1.04  --res_time_limit                        2.
% 3.43/1.04  --res_out_proof                         true
% 3.43/1.04  
% 3.43/1.04  ------ Superposition Options
% 3.43/1.04  
% 3.43/1.04  --superposition_flag                    true
% 3.43/1.04  --sup_passive_queue_type                priority_queues
% 3.43/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.04  --demod_completeness_check              fast
% 3.43/1.04  --demod_use_ground                      true
% 3.43/1.04  --sup_to_prop_solver                    passive
% 3.43/1.04  --sup_prop_simpl_new                    true
% 3.43/1.04  --sup_prop_simpl_given                  true
% 3.43/1.04  --sup_fun_splitting                     true
% 3.43/1.04  --sup_smt_interval                      50000
% 3.43/1.04  
% 3.43/1.04  ------ Superposition Simplification Setup
% 3.43/1.04  
% 3.43/1.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.43/1.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.43/1.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.43/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.43/1.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.43/1.04  --sup_immed_triv                        [TrivRules]
% 3.43/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.04  --sup_immed_bw_main                     []
% 3.43/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.43/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.04  --sup_input_bw                          []
% 3.43/1.04  
% 3.43/1.04  ------ Combination Options
% 3.43/1.04  
% 3.43/1.04  --comb_res_mult                         3
% 3.43/1.04  --comb_sup_mult                         2
% 3.43/1.04  --comb_inst_mult                        10
% 3.43/1.04  
% 3.43/1.04  ------ Debug Options
% 3.43/1.04  
% 3.43/1.04  --dbg_backtrace                         false
% 3.43/1.04  --dbg_dump_prop_clauses                 false
% 3.43/1.04  --dbg_dump_prop_clauses_file            -
% 3.43/1.04  --dbg_out_stat                          false
% 3.43/1.04  
% 3.43/1.04  
% 3.43/1.04  
% 3.43/1.04  
% 3.43/1.04  ------ Proving...
% 3.43/1.04  
% 3.43/1.04  
% 3.43/1.04  % SZS status Theorem for theBenchmark.p
% 3.43/1.04  
% 3.43/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.43/1.04  
% 3.43/1.04  fof(f18,conjecture,(
% 3.43/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f19,negated_conjecture,(
% 3.43/1.04    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.43/1.04    inference(negated_conjecture,[],[f18])).
% 3.43/1.04  
% 3.43/1.04  fof(f43,plain,(
% 3.43/1.04    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.43/1.04    inference(ennf_transformation,[],[f19])).
% 3.43/1.04  
% 3.43/1.04  fof(f44,plain,(
% 3.43/1.04    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.43/1.04    inference(flattening,[],[f43])).
% 3.43/1.04  
% 3.43/1.04  fof(f48,plain,(
% 3.43/1.04    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.43/1.04    introduced(choice_axiom,[])).
% 3.43/1.04  
% 3.43/1.04  fof(f47,plain,(
% 3.43/1.04    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.43/1.04    introduced(choice_axiom,[])).
% 3.43/1.04  
% 3.43/1.04  fof(f49,plain,(
% 3.43/1.04    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.43/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f48,f47])).
% 3.43/1.04  
% 3.43/1.04  fof(f82,plain,(
% 3.43/1.04    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f77,plain,(
% 3.43/1.04    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f6,axiom,(
% 3.43/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f21,plain,(
% 3.43/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.43/1.04    inference(pure_predicate_removal,[],[f6])).
% 3.43/1.04  
% 3.43/1.04  fof(f26,plain,(
% 3.43/1.04    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.04    inference(ennf_transformation,[],[f21])).
% 3.43/1.04  
% 3.43/1.04  fof(f56,plain,(
% 3.43/1.04    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.43/1.04    inference(cnf_transformation,[],[f26])).
% 3.43/1.04  
% 3.43/1.04  fof(f11,axiom,(
% 3.43/1.04    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f33,plain,(
% 3.43/1.04    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.43/1.04    inference(ennf_transformation,[],[f11])).
% 3.43/1.04  
% 3.43/1.04  fof(f34,plain,(
% 3.43/1.04    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.43/1.04    inference(flattening,[],[f33])).
% 3.43/1.04  
% 3.43/1.04  fof(f46,plain,(
% 3.43/1.04    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.43/1.04    inference(nnf_transformation,[],[f34])).
% 3.43/1.04  
% 3.43/1.04  fof(f64,plain,(
% 3.43/1.04    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.43/1.04    inference(cnf_transformation,[],[f46])).
% 3.43/1.04  
% 3.43/1.04  fof(f5,axiom,(
% 3.43/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f25,plain,(
% 3.43/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.04    inference(ennf_transformation,[],[f5])).
% 3.43/1.04  
% 3.43/1.04  fof(f55,plain,(
% 3.43/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.43/1.04    inference(cnf_transformation,[],[f25])).
% 3.43/1.04  
% 3.43/1.04  fof(f74,plain,(
% 3.43/1.04    v1_funct_1(sK1)),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f10,axiom,(
% 3.43/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f31,plain,(
% 3.43/1.04    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.04    inference(ennf_transformation,[],[f10])).
% 3.43/1.04  
% 3.43/1.04  fof(f32,plain,(
% 3.43/1.04    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.04    inference(flattening,[],[f31])).
% 3.43/1.04  
% 3.43/1.04  fof(f63,plain,(
% 3.43/1.04    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.43/1.04    inference(cnf_transformation,[],[f32])).
% 3.43/1.04  
% 3.43/1.04  fof(f76,plain,(
% 3.43/1.04    v3_funct_2(sK1,sK0,sK0)),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f8,axiom,(
% 3.43/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f28,plain,(
% 3.43/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.04    inference(ennf_transformation,[],[f8])).
% 3.43/1.04  
% 3.43/1.04  fof(f58,plain,(
% 3.43/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.43/1.04    inference(cnf_transformation,[],[f28])).
% 3.43/1.04  
% 3.43/1.04  fof(f17,axiom,(
% 3.43/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f41,plain,(
% 3.43/1.04    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.43/1.04    inference(ennf_transformation,[],[f17])).
% 3.43/1.04  
% 3.43/1.04  fof(f42,plain,(
% 3.43/1.04    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.43/1.04    inference(flattening,[],[f41])).
% 3.43/1.04  
% 3.43/1.04  fof(f73,plain,(
% 3.43/1.04    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.43/1.04    inference(cnf_transformation,[],[f42])).
% 3.43/1.04  
% 3.43/1.04  fof(f16,axiom,(
% 3.43/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f39,plain,(
% 3.43/1.04    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.43/1.04    inference(ennf_transformation,[],[f16])).
% 3.43/1.04  
% 3.43/1.04  fof(f40,plain,(
% 3.43/1.04    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.43/1.04    inference(flattening,[],[f39])).
% 3.43/1.04  
% 3.43/1.04  fof(f71,plain,(
% 3.43/1.04    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.43/1.04    inference(cnf_transformation,[],[f40])).
% 3.43/1.04  
% 3.43/1.04  fof(f75,plain,(
% 3.43/1.04    v1_funct_2(sK1,sK0,sK0)),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f78,plain,(
% 3.43/1.04    v1_funct_1(sK2)),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f79,plain,(
% 3.43/1.04    v1_funct_2(sK2,sK0,sK0)),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f81,plain,(
% 3.43/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f83,plain,(
% 3.43/1.04    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f14,axiom,(
% 3.43/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f37,plain,(
% 3.43/1.04    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.43/1.04    inference(ennf_transformation,[],[f14])).
% 3.43/1.04  
% 3.43/1.04  fof(f38,plain,(
% 3.43/1.04    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.43/1.04    inference(flattening,[],[f37])).
% 3.43/1.04  
% 3.43/1.04  fof(f69,plain,(
% 3.43/1.04    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.43/1.04    inference(cnf_transformation,[],[f38])).
% 3.43/1.04  
% 3.43/1.04  fof(f9,axiom,(
% 3.43/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f29,plain,(
% 3.43/1.04    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.43/1.04    inference(ennf_transformation,[],[f9])).
% 3.43/1.04  
% 3.43/1.04  fof(f30,plain,(
% 3.43/1.04    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.04    inference(flattening,[],[f29])).
% 3.43/1.04  
% 3.43/1.04  fof(f45,plain,(
% 3.43/1.04    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.04    inference(nnf_transformation,[],[f30])).
% 3.43/1.04  
% 3.43/1.04  fof(f60,plain,(
% 3.43/1.04    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.43/1.04    inference(cnf_transformation,[],[f45])).
% 3.43/1.04  
% 3.43/1.04  fof(f85,plain,(
% 3.43/1.04    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.43/1.04    inference(equality_resolution,[],[f60])).
% 3.43/1.04  
% 3.43/1.04  fof(f3,axiom,(
% 3.43/1.04    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f23,plain,(
% 3.43/1.04    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.43/1.04    inference(ennf_transformation,[],[f3])).
% 3.43/1.04  
% 3.43/1.04  fof(f24,plain,(
% 3.43/1.04    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.43/1.04    inference(flattening,[],[f23])).
% 3.43/1.04  
% 3.43/1.04  fof(f53,plain,(
% 3.43/1.04    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.43/1.04    inference(cnf_transformation,[],[f24])).
% 3.43/1.04  
% 3.43/1.04  fof(f80,plain,(
% 3.43/1.04    v3_funct_2(sK2,sK0,sK0)),
% 3.43/1.04    inference(cnf_transformation,[],[f49])).
% 3.43/1.04  
% 3.43/1.04  fof(f1,axiom,(
% 3.43/1.04    v1_xboole_0(k1_xboole_0)),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f50,plain,(
% 3.43/1.04    v1_xboole_0(k1_xboole_0)),
% 3.43/1.04    inference(cnf_transformation,[],[f1])).
% 3.43/1.04  
% 3.43/1.04  fof(f13,axiom,(
% 3.43/1.04    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f20,plain,(
% 3.43/1.04    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.43/1.04    inference(pure_predicate_removal,[],[f13])).
% 3.43/1.04  
% 3.43/1.04  fof(f68,plain,(
% 3.43/1.04    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.43/1.04    inference(cnf_transformation,[],[f20])).
% 3.43/1.04  
% 3.43/1.04  fof(f7,axiom,(
% 3.43/1.04    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f27,plain,(
% 3.43/1.04    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.43/1.04    inference(ennf_transformation,[],[f7])).
% 3.43/1.04  
% 3.43/1.04  fof(f57,plain,(
% 3.43/1.04    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.43/1.04    inference(cnf_transformation,[],[f27])).
% 3.43/1.04  
% 3.43/1.04  fof(f2,axiom,(
% 3.43/1.04    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f22,plain,(
% 3.43/1.04    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.43/1.04    inference(ennf_transformation,[],[f2])).
% 3.43/1.04  
% 3.43/1.04  fof(f51,plain,(
% 3.43/1.04    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.43/1.04    inference(cnf_transformation,[],[f22])).
% 3.43/1.04  
% 3.43/1.04  fof(f4,axiom,(
% 3.43/1.04    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f54,plain,(
% 3.43/1.04    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.43/1.04    inference(cnf_transformation,[],[f4])).
% 3.43/1.04  
% 3.43/1.04  fof(f15,axiom,(
% 3.43/1.04    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.43/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.04  
% 3.43/1.04  fof(f70,plain,(
% 3.43/1.04    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.43/1.04    inference(cnf_transformation,[],[f15])).
% 3.43/1.04  
% 3.43/1.04  fof(f84,plain,(
% 3.43/1.04    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.43/1.04    inference(definition_unfolding,[],[f54,f70,f70])).
% 3.43/1.04  
% 3.43/1.04  cnf(c_24,negated_conjecture,
% 3.43/1.04      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.43/1.04      inference(cnf_transformation,[],[f82]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_1231,negated_conjecture,
% 3.43/1.04      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.43/1.04      inference(subtyping,[status(esa)],[c_24]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_1733,plain,
% 3.43/1.04      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.43/1.04      inference(predicate_to_equality,[status(thm)],[c_1231]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_29,negated_conjecture,
% 3.43/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.43/1.04      inference(cnf_transformation,[],[f77]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_1227,negated_conjecture,
% 3.43/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.43/1.04      inference(subtyping,[status(esa)],[c_29]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_1737,plain,
% 3.43/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.43/1.04      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_6,plain,
% 3.43/1.04      ( v5_relat_1(X0,X1)
% 3.43/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.43/1.04      inference(cnf_transformation,[],[f56]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_15,plain,
% 3.43/1.04      ( ~ v2_funct_2(X0,X1)
% 3.43/1.04      | ~ v5_relat_1(X0,X1)
% 3.43/1.04      | ~ v1_relat_1(X0)
% 3.43/1.04      | k2_relat_1(X0) = X1 ),
% 3.43/1.04      inference(cnf_transformation,[],[f64]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_348,plain,
% 3.43/1.04      ( ~ v2_funct_2(X0,X1)
% 3.43/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.43/1.04      | ~ v1_relat_1(X0)
% 3.43/1.04      | k2_relat_1(X0) = X1 ),
% 3.43/1.04      inference(resolution,[status(thm)],[c_6,c_15]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_5,plain,
% 3.43/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.04      | v1_relat_1(X0) ),
% 3.43/1.04      inference(cnf_transformation,[],[f55]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_360,plain,
% 3.43/1.04      ( ~ v2_funct_2(X0,X1)
% 3.43/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.43/1.04      | k2_relat_1(X0) = X1 ),
% 3.43/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_348,c_5]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_1223,plain,
% 3.43/1.04      ( ~ v2_funct_2(X0_51,X1_51)
% 3.43/1.04      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 3.43/1.04      | k2_relat_1(X0_51) = X1_51 ),
% 3.43/1.04      inference(subtyping,[status(esa)],[c_360]) ).
% 3.43/1.04  
% 3.43/1.04  cnf(c_1741,plain,
% 3.43/1.04      ( k2_relat_1(X0_51) = X1_51
% 3.43/1.05      | v2_funct_2(X0_51,X1_51) != iProver_top
% 3.43/1.05      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51))) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1223]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5098,plain,
% 3.43/1.05      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1737,c_1741]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_32,negated_conjecture,
% 3.43/1.05      ( v1_funct_1(sK1) ),
% 3.43/1.05      inference(cnf_transformation,[],[f74]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_33,plain,
% 3.43/1.05      ( v1_funct_1(sK1) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_36,plain,
% 3.43/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_11,plain,
% 3.43/1.05      ( ~ v3_funct_2(X0,X1,X2)
% 3.43/1.05      | v2_funct_2(X0,X2)
% 3.43/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.05      | ~ v1_funct_1(X0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f63]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_30,negated_conjecture,
% 3.43/1.05      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f76]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_436,plain,
% 3.43/1.05      ( v2_funct_2(X0,X1)
% 3.43/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.43/1.05      | ~ v1_funct_1(X0)
% 3.43/1.05      | sK1 != X0
% 3.43/1.05      | sK0 != X1
% 3.43/1.05      | sK0 != X2 ),
% 3.43/1.05      inference(resolution_lifted,[status(thm)],[c_11,c_30]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_437,plain,
% 3.43/1.05      ( v2_funct_2(sK1,sK0)
% 3.43/1.05      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.43/1.05      | ~ v1_funct_1(sK1) ),
% 3.43/1.05      inference(unflattening,[status(thm)],[c_436]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_438,plain,
% 3.43/1.05      ( v2_funct_2(sK1,sK0) = iProver_top
% 3.43/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.43/1.05      | v1_funct_1(sK1) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5208,plain,
% 3.43/1.05      ( k2_relat_1(sK1) = sK0 ),
% 3.43/1.05      inference(global_propositional_subsumption,
% 3.43/1.05                [status(thm)],
% 3.43/1.05                [c_5098,c_33,c_36,c_438]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_8,plain,
% 3.43/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.05      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f58]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1239,plain,
% 3.43/1.05      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 3.43/1.05      | k2_relset_1(X1_51,X2_51,X0_51) = k2_relat_1(X0_51) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_8]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1725,plain,
% 3.43/1.05      ( k2_relset_1(X0_51,X1_51,X2_51) = k2_relat_1(X2_51)
% 3.43/1.05      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1239]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_2964,plain,
% 3.43/1.05      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1737,c_1725]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_22,plain,
% 3.43/1.05      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.43/1.05      | ~ v1_funct_2(X3,X1,X0)
% 3.43/1.05      | ~ v1_funct_2(X2,X0,X1)
% 3.43/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.43/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.43/1.05      | ~ v2_funct_1(X2)
% 3.43/1.05      | ~ v1_funct_1(X2)
% 3.43/1.05      | ~ v1_funct_1(X3)
% 3.43/1.05      | k2_relset_1(X0,X1,X2) != X1
% 3.43/1.05      | k2_funct_1(X2) = X3
% 3.43/1.05      | k1_xboole_0 = X0
% 3.43/1.05      | k1_xboole_0 = X1 ),
% 3.43/1.05      inference(cnf_transformation,[],[f73]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_21,plain,
% 3.43/1.05      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.43/1.05      | ~ v1_funct_2(X3,X1,X0)
% 3.43/1.05      | ~ v1_funct_2(X2,X0,X1)
% 3.43/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.43/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.43/1.05      | v2_funct_1(X2)
% 3.43/1.05      | ~ v1_funct_1(X2)
% 3.43/1.05      | ~ v1_funct_1(X3) ),
% 3.43/1.05      inference(cnf_transformation,[],[f71]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_179,plain,
% 3.43/1.05      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.43/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.43/1.05      | ~ v1_funct_2(X2,X0,X1)
% 3.43/1.05      | ~ v1_funct_2(X3,X1,X0)
% 3.43/1.05      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.43/1.05      | ~ v1_funct_1(X2)
% 3.43/1.05      | ~ v1_funct_1(X3)
% 3.43/1.05      | k2_relset_1(X0,X1,X2) != X1
% 3.43/1.05      | k2_funct_1(X2) = X3
% 3.43/1.05      | k1_xboole_0 = X0
% 3.43/1.05      | k1_xboole_0 = X1 ),
% 3.43/1.05      inference(global_propositional_subsumption,
% 3.43/1.05                [status(thm)],
% 3.43/1.05                [c_22,c_21]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_180,plain,
% 3.43/1.05      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.43/1.05      | ~ v1_funct_2(X3,X1,X0)
% 3.43/1.05      | ~ v1_funct_2(X2,X0,X1)
% 3.43/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.43/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.43/1.05      | ~ v1_funct_1(X2)
% 3.43/1.05      | ~ v1_funct_1(X3)
% 3.43/1.05      | k2_relset_1(X0,X1,X2) != X1
% 3.43/1.05      | k2_funct_1(X2) = X3
% 3.43/1.05      | k1_xboole_0 = X1
% 3.43/1.05      | k1_xboole_0 = X0 ),
% 3.43/1.05      inference(renaming,[status(thm)],[c_179]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1224,plain,
% 3.43/1.05      ( ~ r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51))
% 3.43/1.05      | ~ v1_funct_2(X3_51,X1_51,X0_51)
% 3.43/1.05      | ~ v1_funct_2(X2_51,X0_51,X1_51)
% 3.43/1.05      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.43/1.05      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 3.43/1.05      | ~ v1_funct_1(X2_51)
% 3.43/1.05      | ~ v1_funct_1(X3_51)
% 3.43/1.05      | k2_relset_1(X0_51,X1_51,X2_51) != X1_51
% 3.43/1.05      | k2_funct_1(X2_51) = X3_51
% 3.43/1.05      | k1_xboole_0 = X1_51
% 3.43/1.05      | k1_xboole_0 = X0_51 ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_180]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1740,plain,
% 3.43/1.05      ( k2_relset_1(X0_51,X1_51,X2_51) != X1_51
% 3.43/1.05      | k2_funct_1(X2_51) = X3_51
% 3.43/1.05      | k1_xboole_0 = X1_51
% 3.43/1.05      | k1_xboole_0 = X0_51
% 3.43/1.05      | r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51)) != iProver_top
% 3.43/1.05      | v1_funct_2(X3_51,X1_51,X0_51) != iProver_top
% 3.43/1.05      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 3.43/1.05      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.43/1.05      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
% 3.43/1.05      | v1_funct_1(X2_51) != iProver_top
% 3.43/1.05      | v1_funct_1(X3_51) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1224]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4078,plain,
% 3.43/1.05      ( k2_funct_1(sK1) = X0_51
% 3.43/1.05      | k2_relat_1(sK1) != sK0
% 3.43/1.05      | sK0 = k1_xboole_0
% 3.43/1.05      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.43/1.05      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.43/1.05      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.43/1.05      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.43/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.43/1.05      | v1_funct_1(X0_51) != iProver_top
% 3.43/1.05      | v1_funct_1(sK1) != iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_2964,c_1740]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_31,negated_conjecture,
% 3.43/1.05      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f75]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_34,plain,
% 3.43/1.05      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4768,plain,
% 3.43/1.05      ( v1_funct_1(X0_51) != iProver_top
% 3.43/1.05      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.43/1.05      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.43/1.05      | sK0 = k1_xboole_0
% 3.43/1.05      | k2_relat_1(sK1) != sK0
% 3.43/1.05      | k2_funct_1(sK1) = X0_51
% 3.43/1.05      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.43/1.05      inference(global_propositional_subsumption,
% 3.43/1.05                [status(thm)],
% 3.43/1.05                [c_4078,c_33,c_34,c_36]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4769,plain,
% 3.43/1.05      ( k2_funct_1(sK1) = X0_51
% 3.43/1.05      | k2_relat_1(sK1) != sK0
% 3.43/1.05      | sK0 = k1_xboole_0
% 3.43/1.05      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.43/1.05      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.43/1.05      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.43/1.05      | v1_funct_1(X0_51) != iProver_top ),
% 3.43/1.05      inference(renaming,[status(thm)],[c_4768]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5210,plain,
% 3.43/1.05      ( k2_funct_1(sK1) = X0_51
% 3.43/1.05      | sK0 != sK0
% 3.43/1.05      | sK0 = k1_xboole_0
% 3.43/1.05      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.43/1.05      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.43/1.05      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.43/1.05      | v1_funct_1(X0_51) != iProver_top ),
% 3.43/1.05      inference(demodulation,[status(thm)],[c_5208,c_4769]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5212,plain,
% 3.43/1.05      ( k2_funct_1(sK1) = X0_51
% 3.43/1.05      | sK0 = k1_xboole_0
% 3.43/1.05      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.43/1.05      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.43/1.05      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.43/1.05      | v1_funct_1(X0_51) != iProver_top ),
% 3.43/1.05      inference(equality_resolution_simp,[status(thm)],[c_5210]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5566,plain,
% 3.43/1.05      ( k2_funct_1(sK1) = sK2
% 3.43/1.05      | sK0 = k1_xboole_0
% 3.43/1.05      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.43/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.43/1.05      | v1_funct_1(sK2) != iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1733,c_5212]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_28,negated_conjecture,
% 3.43/1.05      ( v1_funct_1(sK2) ),
% 3.43/1.05      inference(cnf_transformation,[],[f78]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_27,negated_conjecture,
% 3.43/1.05      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f79]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_25,negated_conjecture,
% 3.43/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.43/1.05      inference(cnf_transformation,[],[f81]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5567,plain,
% 3.43/1.05      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.43/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.43/1.05      | ~ v1_funct_1(sK2)
% 3.43/1.05      | k2_funct_1(sK1) = sK2
% 3.43/1.05      | sK0 = k1_xboole_0 ),
% 3.43/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_5566]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5569,plain,
% 3.43/1.05      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.43/1.05      inference(global_propositional_subsumption,
% 3.43/1.05                [status(thm)],
% 3.43/1.05                [c_5566,c_37,c_38,c_40]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5570,plain,
% 3.43/1.05      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.43/1.05      inference(renaming,[status(thm)],[c_5569]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_23,negated_conjecture,
% 3.43/1.05      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.43/1.05      inference(cnf_transformation,[],[f83]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1232,negated_conjecture,
% 3.43/1.05      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_23]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1732,plain,
% 3.43/1.05      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_19,plain,
% 3.43/1.05      ( ~ v1_funct_2(X0,X1,X1)
% 3.43/1.05      | ~ v3_funct_2(X0,X1,X1)
% 3.43/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.43/1.05      | ~ v1_funct_1(X0)
% 3.43/1.05      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f69]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_455,plain,
% 3.43/1.05      ( ~ v1_funct_2(X0,X1,X1)
% 3.43/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.43/1.05      | ~ v1_funct_1(X0)
% 3.43/1.05      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.43/1.05      | sK1 != X0
% 3.43/1.05      | sK0 != X1 ),
% 3.43/1.05      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_456,plain,
% 3.43/1.05      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.43/1.05      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.43/1.05      | ~ v1_funct_1(sK1)
% 3.43/1.05      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.43/1.05      inference(unflattening,[status(thm)],[c_455]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_458,plain,
% 3.43/1.05      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.43/1.05      inference(global_propositional_subsumption,
% 3.43/1.05                [status(thm)],
% 3.43/1.05                [c_456,c_32,c_31,c_29]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1218,plain,
% 3.43/1.05      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_458]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1745,plain,
% 3.43/1.05      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.43/1.05      inference(light_normalisation,[status(thm)],[c_1732,c_1218]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5571,plain,
% 3.43/1.05      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_5570,c_1745]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_40,plain,
% 3.43/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_9,plain,
% 3.43/1.05      ( r2_relset_1(X0,X1,X2,X2)
% 3.43/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.43/1.05      inference(cnf_transformation,[],[f85]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1238,plain,
% 3.43/1.05      ( r2_relset_1(X0_51,X1_51,X2_51,X2_51)
% 3.43/1.05      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_9]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1806,plain,
% 3.43/1.05      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.43/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.43/1.05      inference(instantiation,[status(thm)],[c_1238]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1807,plain,
% 3.43/1.05      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.43/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1806]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5642,plain,
% 3.43/1.05      ( sK0 = k1_xboole_0 ),
% 3.43/1.05      inference(global_propositional_subsumption,
% 3.43/1.05                [status(thm)],
% 3.43/1.05                [c_5571,c_40,c_1807]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_2,plain,
% 3.43/1.05      ( ~ v1_relat_1(X0)
% 3.43/1.05      | k2_relat_1(X0) != k1_xboole_0
% 3.43/1.05      | k1_xboole_0 = X0 ),
% 3.43/1.05      inference(cnf_transformation,[],[f53]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1244,plain,
% 3.43/1.05      ( ~ v1_relat_1(X0_51)
% 3.43/1.05      | k2_relat_1(X0_51) != k1_xboole_0
% 3.43/1.05      | k1_xboole_0 = X0_51 ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_2]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1721,plain,
% 3.43/1.05      ( k2_relat_1(X0_51) != k1_xboole_0
% 3.43/1.05      | k1_xboole_0 = X0_51
% 3.43/1.05      | v1_relat_1(X0_51) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1244]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5216,plain,
% 3.43/1.05      ( sK1 = k1_xboole_0
% 3.43/1.05      | sK0 != k1_xboole_0
% 3.43/1.05      | v1_relat_1(sK1) != iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_5208,c_1721]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1241,plain,
% 3.43/1.05      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 3.43/1.05      | v1_relat_1(X0_51) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_5]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1723,plain,
% 3.43/1.05      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 3.43/1.05      | v1_relat_1(X0_51) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1241]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_2412,plain,
% 3.43/1.05      ( v1_relat_1(sK1) = iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1737,c_1723]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5535,plain,
% 3.43/1.05      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.43/1.05      inference(global_propositional_subsumption,
% 3.43/1.05                [status(thm)],
% 3.43/1.05                [c_5216,c_2412]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5536,plain,
% 3.43/1.05      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.43/1.05      inference(renaming,[status(thm)],[c_5535]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5646,plain,
% 3.43/1.05      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.43/1.05      inference(demodulation,[status(thm)],[c_5642,c_5536]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5693,plain,
% 3.43/1.05      ( sK1 = k1_xboole_0 ),
% 3.43/1.05      inference(equality_resolution_simp,[status(thm)],[c_5646]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1230,negated_conjecture,
% 3.43/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_25]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1734,plain,
% 3.43/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5097,plain,
% 3.43/1.05      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1734,c_1741]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_37,plain,
% 3.43/1.05      ( v1_funct_1(sK2) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_26,negated_conjecture,
% 3.43/1.05      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f80]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_425,plain,
% 3.43/1.05      ( v2_funct_2(X0,X1)
% 3.43/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.43/1.05      | ~ v1_funct_1(X0)
% 3.43/1.05      | sK2 != X0
% 3.43/1.05      | sK0 != X1
% 3.43/1.05      | sK0 != X2 ),
% 3.43/1.05      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_426,plain,
% 3.43/1.05      ( v2_funct_2(sK2,sK0)
% 3.43/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.43/1.05      | ~ v1_funct_1(sK2) ),
% 3.43/1.05      inference(unflattening,[status(thm)],[c_425]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_427,plain,
% 3.43/1.05      ( v2_funct_2(sK2,sK0) = iProver_top
% 3.43/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.43/1.05      | v1_funct_1(sK2) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5197,plain,
% 3.43/1.05      ( k2_relat_1(sK2) = sK0 ),
% 3.43/1.05      inference(global_propositional_subsumption,
% 3.43/1.05                [status(thm)],
% 3.43/1.05                [c_5097,c_37,c_40,c_427]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5205,plain,
% 3.43/1.05      ( sK2 = k1_xboole_0
% 3.43/1.05      | sK0 != k1_xboole_0
% 3.43/1.05      | v1_relat_1(sK2) != iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_5197,c_1721]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_2411,plain,
% 3.43/1.05      ( v1_relat_1(sK2) = iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1734,c_1723]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5312,plain,
% 3.43/1.05      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.43/1.05      inference(global_propositional_subsumption,
% 3.43/1.05                [status(thm)],
% 3.43/1.05                [c_5205,c_2411]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5313,plain,
% 3.43/1.05      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.43/1.05      inference(renaming,[status(thm)],[c_5312]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5649,plain,
% 3.43/1.05      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.43/1.05      inference(demodulation,[status(thm)],[c_5642,c_5313]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5677,plain,
% 3.43/1.05      ( sK2 = k1_xboole_0 ),
% 3.43/1.05      inference(equality_resolution_simp,[status(thm)],[c_5649]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5664,plain,
% 3.43/1.05      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.43/1.05      inference(demodulation,[status(thm)],[c_5642,c_1745]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5685,plain,
% 3.43/1.05      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 3.43/1.05      inference(demodulation,[status(thm)],[c_5677,c_5664]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5695,plain,
% 3.43/1.05      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.43/1.05      inference(demodulation,[status(thm)],[c_5693,c_5685]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_0,plain,
% 3.43/1.05      ( v1_xboole_0(k1_xboole_0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f50]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1246,plain,
% 3.43/1.05      ( v1_xboole_0(k1_xboole_0) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_0]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1719,plain,
% 3.43/1.05      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1246]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_18,plain,
% 3.43/1.05      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.43/1.05      inference(cnf_transformation,[],[f68]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1234,plain,
% 3.43/1.05      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_18]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1730,plain,
% 3.43/1.05      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1234]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_7,plain,
% 3.43/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.05      | ~ v1_xboole_0(X2)
% 3.43/1.05      | v1_xboole_0(X0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f57]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1240,plain,
% 3.43/1.05      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 3.43/1.05      | ~ v1_xboole_0(X2_51)
% 3.43/1.05      | v1_xboole_0(X0_51) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_7]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1724,plain,
% 3.43/1.05      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 3.43/1.05      | v1_xboole_0(X2_51) != iProver_top
% 3.43/1.05      | v1_xboole_0(X0_51) = iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_2746,plain,
% 3.43/1.05      ( v1_xboole_0(X0_51) != iProver_top
% 3.43/1.05      | v1_xboole_0(k6_partfun1(X0_51)) = iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1730,c_1724]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1,plain,
% 3.43/1.05      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.43/1.05      inference(cnf_transformation,[],[f51]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1245,plain,
% 3.43/1.05      ( ~ v1_xboole_0(X0_51) | ~ v1_xboole_0(X1_51) | X1_51 = X0_51 ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_1]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1720,plain,
% 3.43/1.05      ( X0_51 = X1_51
% 3.43/1.05      | v1_xboole_0(X1_51) != iProver_top
% 3.43/1.05      | v1_xboole_0(X0_51) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4184,plain,
% 3.43/1.05      ( k6_partfun1(X0_51) = X1_51
% 3.43/1.05      | v1_xboole_0(X0_51) != iProver_top
% 3.43/1.05      | v1_xboole_0(X1_51) != iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_2746,c_1720]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4192,plain,
% 3.43/1.05      ( k6_partfun1(k1_xboole_0) = X0_51
% 3.43/1.05      | v1_xboole_0(X0_51) != iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1719,c_4184]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4438,plain,
% 3.43/1.05      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1719,c_4192]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4,plain,
% 3.43/1.05      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.43/1.05      inference(cnf_transformation,[],[f84]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1242,plain,
% 3.43/1.05      ( k2_funct_1(k6_partfun1(X0_51)) = k6_partfun1(X0_51) ),
% 3.43/1.05      inference(subtyping,[status(esa)],[c_4]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4782,plain,
% 3.43/1.05      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_4438,c_1242]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4783,plain,
% 3.43/1.05      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.43/1.05      inference(demodulation,[status(thm)],[c_4782,c_4438]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_5706,plain,
% 3.43/1.05      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.43/1.05      inference(light_normalisation,[status(thm)],[c_5695,c_4783]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_1726,plain,
% 3.43/1.05      ( r2_relset_1(X0_51,X1_51,X2_51,X2_51) = iProver_top
% 3.43/1.05      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.43/1.05      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_2970,plain,
% 3.43/1.05      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_1730,c_1726]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(c_4776,plain,
% 3.43/1.05      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.43/1.05      inference(superposition,[status(thm)],[c_4438,c_2970]) ).
% 3.43/1.05  
% 3.43/1.05  cnf(contradiction,plain,
% 3.43/1.05      ( $false ),
% 3.43/1.05      inference(minisat,[status(thm)],[c_5706,c_4776]) ).
% 3.43/1.05  
% 3.43/1.05  
% 3.43/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.43/1.05  
% 3.43/1.05  ------                               Statistics
% 3.43/1.05  
% 3.43/1.05  ------ General
% 3.43/1.05  
% 3.43/1.05  abstr_ref_over_cycles:                  0
% 3.43/1.05  abstr_ref_under_cycles:                 0
% 3.43/1.05  gc_basic_clause_elim:                   0
% 3.43/1.05  forced_gc_time:                         0
% 3.43/1.05  parsing_time:                           0.012
% 3.43/1.05  unif_index_cands_time:                  0.
% 3.43/1.05  unif_index_add_time:                    0.
% 3.43/1.05  orderings_time:                         0.
% 3.43/1.05  out_proof_time:                         0.013
% 3.43/1.05  total_time:                             0.233
% 3.43/1.05  num_of_symbols:                         57
% 3.43/1.05  num_of_terms:                           7055
% 3.43/1.05  
% 3.43/1.05  ------ Preprocessing
% 3.43/1.05  
% 3.43/1.05  num_of_splits:                          0
% 3.43/1.05  num_of_split_atoms:                     0
% 3.43/1.05  num_of_reused_defs:                     0
% 3.43/1.05  num_eq_ax_congr_red:                    21
% 3.43/1.05  num_of_sem_filtered_clauses:            3
% 3.43/1.05  num_of_subtypes:                        3
% 3.43/1.05  monotx_restored_types:                  1
% 3.43/1.05  sat_num_of_epr_types:                   0
% 3.43/1.05  sat_num_of_non_cyclic_types:            0
% 3.43/1.05  sat_guarded_non_collapsed_types:        1
% 3.43/1.05  num_pure_diseq_elim:                    0
% 3.43/1.05  simp_replaced_by:                       0
% 3.43/1.05  res_preprocessed:                       152
% 3.43/1.05  prep_upred:                             0
% 3.43/1.05  prep_unflattend:                        66
% 3.43/1.05  smt_new_axioms:                         0
% 3.43/1.05  pred_elim_cands:                        7
% 3.43/1.05  pred_elim:                              2
% 3.43/1.05  pred_elim_cl:                           1
% 3.43/1.05  pred_elim_cycles:                       8
% 3.43/1.05  merged_defs:                            0
% 3.43/1.05  merged_defs_ncl:                        0
% 3.43/1.05  bin_hyper_res:                          0
% 3.43/1.05  prep_cycles:                            4
% 3.43/1.05  pred_elim_time:                         0.014
% 3.43/1.05  splitting_time:                         0.
% 3.43/1.05  sem_filter_time:                        0.
% 3.43/1.05  monotx_time:                            0.
% 3.43/1.05  subtype_inf_time:                       0.001
% 3.43/1.05  
% 3.43/1.05  ------ Problem properties
% 3.43/1.05  
% 3.43/1.05  clauses:                                29
% 3.43/1.05  conjectures:                            8
% 3.43/1.05  epr:                                    8
% 3.43/1.05  horn:                                   28
% 3.43/1.05  ground:                                 13
% 3.43/1.05  unary:                                  15
% 3.43/1.05  binary:                                 4
% 3.43/1.05  lits:                                   71
% 3.43/1.05  lits_eq:                                15
% 3.43/1.05  fd_pure:                                0
% 3.43/1.05  fd_pseudo:                              0
% 3.43/1.05  fd_cond:                                2
% 3.43/1.05  fd_pseudo_cond:                         4
% 3.43/1.05  ac_symbols:                             0
% 3.43/1.05  
% 3.43/1.05  ------ Propositional Solver
% 3.43/1.05  
% 3.43/1.05  prop_solver_calls:                      28
% 3.43/1.05  prop_fast_solver_calls:                 1236
% 3.43/1.05  smt_solver_calls:                       0
% 3.43/1.05  smt_fast_solver_calls:                  0
% 3.43/1.05  prop_num_of_clauses:                    2244
% 3.43/1.05  prop_preprocess_simplified:             7503
% 3.43/1.05  prop_fo_subsumed:                       34
% 3.43/1.05  prop_solver_time:                       0.
% 3.43/1.05  smt_solver_time:                        0.
% 3.43/1.05  smt_fast_solver_time:                   0.
% 3.43/1.05  prop_fast_solver_time:                  0.
% 3.43/1.05  prop_unsat_core_time:                   0.
% 3.43/1.05  
% 3.43/1.05  ------ QBF
% 3.43/1.05  
% 3.43/1.05  qbf_q_res:                              0
% 3.43/1.05  qbf_num_tautologies:                    0
% 3.43/1.05  qbf_prep_cycles:                        0
% 3.43/1.05  
% 3.43/1.05  ------ BMC1
% 3.43/1.05  
% 3.43/1.05  bmc1_current_bound:                     -1
% 3.43/1.05  bmc1_last_solved_bound:                 -1
% 3.43/1.05  bmc1_unsat_core_size:                   -1
% 3.43/1.05  bmc1_unsat_core_parents_size:           -1
% 3.43/1.05  bmc1_merge_next_fun:                    0
% 3.43/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.43/1.05  
% 3.43/1.05  ------ Instantiation
% 3.43/1.05  
% 3.43/1.05  inst_num_of_clauses:                    661
% 3.43/1.05  inst_num_in_passive:                    153
% 3.43/1.05  inst_num_in_active:                     343
% 3.43/1.05  inst_num_in_unprocessed:                165
% 3.43/1.05  inst_num_of_loops:                      360
% 3.43/1.05  inst_num_of_learning_restarts:          0
% 3.43/1.05  inst_num_moves_active_passive:          13
% 3.43/1.05  inst_lit_activity:                      0
% 3.43/1.05  inst_lit_activity_moves:                0
% 3.43/1.05  inst_num_tautologies:                   0
% 3.43/1.05  inst_num_prop_implied:                  0
% 3.43/1.05  inst_num_existing_simplified:           0
% 3.43/1.05  inst_num_eq_res_simplified:             0
% 3.43/1.05  inst_num_child_elim:                    0
% 3.43/1.05  inst_num_of_dismatching_blockings:      328
% 3.43/1.05  inst_num_of_non_proper_insts:           959
% 3.43/1.05  inst_num_of_duplicates:                 0
% 3.43/1.05  inst_inst_num_from_inst_to_res:         0
% 3.43/1.05  inst_dismatching_checking_time:         0.
% 3.43/1.05  
% 3.43/1.05  ------ Resolution
% 3.43/1.05  
% 3.43/1.05  res_num_of_clauses:                     0
% 3.43/1.05  res_num_in_passive:                     0
% 3.43/1.05  res_num_in_active:                      0
% 3.43/1.05  res_num_of_loops:                       156
% 3.43/1.05  res_forward_subset_subsumed:            35
% 3.43/1.05  res_backward_subset_subsumed:           0
% 3.43/1.05  res_forward_subsumed:                   0
% 3.43/1.05  res_backward_subsumed:                  0
% 3.43/1.05  res_forward_subsumption_resolution:     4
% 3.43/1.05  res_backward_subsumption_resolution:    0
% 3.43/1.05  res_clause_to_clause_subsumption:       230
% 3.43/1.05  res_orphan_elimination:                 0
% 3.43/1.05  res_tautology_del:                      69
% 3.43/1.05  res_num_eq_res_simplified:              0
% 3.43/1.05  res_num_sel_changes:                    0
% 3.43/1.05  res_moves_from_active_to_pass:          0
% 3.43/1.05  
% 3.43/1.05  ------ Superposition
% 3.43/1.05  
% 3.43/1.05  sup_time_total:                         0.
% 3.43/1.05  sup_time_generating:                    0.
% 3.43/1.05  sup_time_sim_full:                      0.
% 3.43/1.05  sup_time_sim_immed:                     0.
% 3.43/1.05  
% 3.43/1.05  sup_num_of_clauses:                     60
% 3.43/1.05  sup_num_in_active:                      34
% 3.43/1.05  sup_num_in_passive:                     26
% 3.43/1.05  sup_num_of_loops:                       70
% 3.43/1.05  sup_fw_superposition:                   40
% 3.43/1.05  sup_bw_superposition:                   27
% 3.43/1.05  sup_immediate_simplified:               41
% 3.43/1.05  sup_given_eliminated:                   1
% 3.43/1.05  comparisons_done:                       0
% 3.43/1.05  comparisons_avoided:                    3
% 3.43/1.05  
% 3.43/1.05  ------ Simplifications
% 3.43/1.05  
% 3.43/1.05  
% 3.43/1.05  sim_fw_subset_subsumed:                 2
% 3.43/1.05  sim_bw_subset_subsumed:                 4
% 3.43/1.05  sim_fw_subsumed:                        0
% 3.43/1.05  sim_bw_subsumed:                        1
% 3.43/1.05  sim_fw_subsumption_res:                 0
% 3.43/1.05  sim_bw_subsumption_res:                 0
% 3.43/1.05  sim_tautology_del:                      4
% 3.43/1.05  sim_eq_tautology_del:                   6
% 3.43/1.05  sim_eq_res_simp:                        4
% 3.43/1.05  sim_fw_demodulated:                     4
% 3.43/1.05  sim_bw_demodulated:                     61
% 3.43/1.05  sim_light_normalised:                   8
% 3.43/1.05  sim_joinable_taut:                      0
% 3.43/1.05  sim_joinable_simp:                      0
% 3.43/1.05  sim_ac_normalised:                      0
% 3.43/1.05  sim_smt_subsumption:                    0
% 3.43/1.05  
%------------------------------------------------------------------------------
