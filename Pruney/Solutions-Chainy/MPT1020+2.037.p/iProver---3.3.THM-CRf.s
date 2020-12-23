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
% DateTime   : Thu Dec  3 12:07:12 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
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

fof(f42,plain,(
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
    inference(flattening,[],[f42])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f47,f46])).

fof(f82,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f40,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(cnf_transformation,[],[f41])).

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

fof(f38,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f80,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f54,f70])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f56,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f86,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
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

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1732,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2312,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1732])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1728,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2316,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1728])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1739,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | k2_relset_1(X1_51,X2_51,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2305,plain,
    ( k2_relset_1(X0_51,X1_51,X2_51) = k2_relat_1(X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1739])).

cnf(c_4021,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2316,c_2305])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_178,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_22])).

cnf(c_179,plain,
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
    inference(renaming,[status(thm)],[c_178])).

cnf(c_1725,plain,
    ( ~ r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51))
    | ~ v1_funct_2(X3_51,X1_51,X0_51)
    | ~ v1_funct_2(X2_51,X0_51,X1_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
    | ~ v1_funct_1(X2_51)
    | ~ v1_funct_1(X3_51)
    | k2_relset_1(X0_51,X1_51,X2_51) != X1_51
    | k2_funct_1(X2_51) = X3_51
    | k1_xboole_0 = X0_51
    | k1_xboole_0 = X1_51 ),
    inference(subtyping,[status(esa)],[c_179])).

cnf(c_2319,plain,
    ( k2_relset_1(X0_51,X1_51,X2_51) != X1_51
    | k2_funct_1(X2_51) = X3_51
    | k1_xboole_0 = X0_51
    | k1_xboole_0 = X1_51
    | r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51)) != iProver_top
    | v1_funct_2(X3_51,X1_51,X0_51) != iProver_top
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1725])).

cnf(c_5073,plain,
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
    inference(superposition,[status(thm)],[c_4021,c_2319])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_494,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_495,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_348,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_18])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_360,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_348,c_9])).

cnf(c_1724,plain,
    ( ~ v2_funct_2(X0_51,X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | k2_relat_1(X0_51) = X1_51 ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_2579,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_2581,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_2579])).

cnf(c_7303,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5073,c_33,c_34,c_35,c_30,c_37,c_495,c_2581])).

cnf(c_7304,plain,
    ( k2_funct_1(sK1) = X0_51
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_7303])).

cnf(c_7315,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_7304])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7316,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7315])).

cnf(c_7478,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7315,c_38,c_39,c_41])).

cnf(c_7479,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7478])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1733,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2311,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1733])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_513,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_514,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_516,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_33,c_32,c_30])).

cnf(c_1717,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_516])).

cnf(c_2362,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2311,c_1717])).

cnf(c_7482,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7479,c_2362])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1738,plain,
    ( r2_relset_1(X0_51,X1_51,X2_51,X2_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2584,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_2585,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2584])).

cnf(c_7485,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7482,c_41,c_2585])).

cnf(c_1731,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2313,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1731])).

cnf(c_2320,plain,
    ( k2_relat_1(X0_51) = X1_51
    | v2_funct_2(X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1724])).

cnf(c_5205,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_2320])).

cnf(c_27,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_472,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_473,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_2574,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_2576,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_2574])).

cnf(c_5566,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5205,c_29,c_26,c_473,c_2576])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1747,plain,
    ( ~ v1_relat_1(X0_51)
    | k2_relat_1(X0_51) != k1_xboole_0
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2298,plain,
    ( k2_relat_1(X0_51) != k1_xboole_0
    | k1_xboole_0 = X0_51
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1747])).

cnf(c_5586,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5566,c_2298])).

cnf(c_1740,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2550,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_2551,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2550])).

cnf(c_5991,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5586,c_41,c_2551])).

cnf(c_5992,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5991])).

cnf(c_7493,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7485,c_5992])).

cnf(c_7587,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7493])).

cnf(c_1729,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2315,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1729])).

cnf(c_8389,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7587,c_2315])).

cnf(c_5,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1744,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1742,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2302,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1742])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1745,plain,
    ( ~ v1_relat_1(X0_51)
    | k5_relat_1(X0_51,k6_partfun1(k2_relat_1(X0_51))) = X0_51 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2300,plain,
    ( k5_relat_1(X0_51,k6_partfun1(k2_relat_1(X0_51))) = X0_51
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1745])).

cnf(c_3171,plain,
    ( k5_relat_1(k6_partfun1(X0_51),k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51) ),
    inference(superposition,[status(thm)],[c_2302,c_2300])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1741,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | ~ v2_funct_1(X1_51)
    | ~ v1_relat_1(X1_51)
    | ~ v1_relat_1(X0_51)
    | k5_relat_1(X0_51,X1_51) != k6_partfun1(k2_relat_1(X1_51))
    | k2_funct_1(X1_51) = X0_51
    | k1_relat_1(X1_51) != k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2303,plain,
    ( k5_relat_1(X0_51,X1_51) != k6_partfun1(k2_relat_1(X1_51))
    | k2_funct_1(X1_51) = X0_51
    | k1_relat_1(X1_51) != k2_relat_1(X0_51)
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1741])).

cnf(c_3898,plain,
    ( k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51)
    | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51))))) != k6_partfun1(X0_51)
    | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
    | v2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
    | v1_relat_1(k6_partfun1(X0_51)) != iProver_top
    | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3171,c_2303])).

cnf(c_1801,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1742])).

cnf(c_6715,plain,
    ( v2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
    | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
    | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51))))) != k6_partfun1(X0_51)
    | k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51)
    | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3898,c_1801])).

cnf(c_6716,plain,
    ( k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51)
    | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51))))) != k6_partfun1(X0_51)
    | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
    | v2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
    | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6715])).

cnf(c_6,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1743,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2301,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1743])).

cnf(c_6728,plain,
    ( k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51)
    | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51))))) != k6_partfun1(X0_51)
    | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6716,c_2302,c_2301])).

cnf(c_6732,plain,
    ( k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0)))) = k6_partfun1(k1_xboole_0)
    | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0))))) != k6_partfun1(k1_xboole_0)
    | k1_relat_1(k6_partfun1(k2_relat_1(k1_xboole_0))) != k2_relat_1(k6_partfun1(k1_xboole_0))
    | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0)))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_6728])).

cnf(c_1,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1748,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1749,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_6733,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6732,c_1744,c_1748,c_1749])).

cnf(c_6734,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6733])).

cnf(c_8395,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8389,c_6734])).

cnf(c_5206,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_2320])).

cnf(c_5598,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5206,c_33,c_30,c_495,c_2581])).

cnf(c_5618,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5598,c_2298])).

cnf(c_2553,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_2554,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2553])).

cnf(c_5996,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5618,c_37,c_2554])).

cnf(c_5997,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5996])).

cnf(c_7492,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7485,c_5997])).

cnf(c_7615,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7492])).

cnf(c_7508,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7485,c_2362])).

cnf(c_7596,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7587,c_7508])).

cnf(c_7617,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7615,c_7596])).

cnf(c_8425,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8395,c_7617])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1736,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2308,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1736])).

cnf(c_3269,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_2308])).

cnf(c_2306,plain,
    ( r2_relset_1(X0_51,X1_51,X2_51,X2_51) = iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1738])).

cnf(c_4128,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3269,c_2306])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8425,c_4128])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 20:44:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.53/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/0.98  
% 3.53/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.98  
% 3.53/0.98  ------  iProver source info
% 3.53/0.98  
% 3.53/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.98  git: non_committed_changes: false
% 3.53/0.98  git: last_make_outside_of_git: false
% 3.53/0.98  
% 3.53/0.98  ------ 
% 3.53/0.98  
% 3.53/0.98  ------ Input Options
% 3.53/0.98  
% 3.53/0.98  --out_options                           all
% 3.53/0.98  --tptp_safe_out                         true
% 3.53/0.98  --problem_path                          ""
% 3.53/0.98  --include_path                          ""
% 3.53/0.98  --clausifier                            res/vclausify_rel
% 3.53/0.98  --clausifier_options                    --mode clausify
% 3.53/0.98  --stdin                                 false
% 3.53/0.98  --stats_out                             all
% 3.53/0.98  
% 3.53/0.98  ------ General Options
% 3.53/0.98  
% 3.53/0.98  --fof                                   false
% 3.53/0.98  --time_out_real                         305.
% 3.53/0.98  --time_out_virtual                      -1.
% 3.53/0.98  --symbol_type_check                     false
% 3.53/0.98  --clausify_out                          false
% 3.53/0.98  --sig_cnt_out                           false
% 3.53/0.98  --trig_cnt_out                          false
% 3.53/0.98  --trig_cnt_out_tolerance                1.
% 3.53/0.98  --trig_cnt_out_sk_spl                   false
% 3.53/0.98  --abstr_cl_out                          false
% 3.53/0.98  
% 3.53/0.98  ------ Global Options
% 3.53/0.98  
% 3.53/0.98  --schedule                              default
% 3.53/0.98  --add_important_lit                     false
% 3.53/0.98  --prop_solver_per_cl                    1000
% 3.53/0.98  --min_unsat_core                        false
% 3.53/0.98  --soft_assumptions                      false
% 3.53/0.98  --soft_lemma_size                       3
% 3.53/0.98  --prop_impl_unit_size                   0
% 3.53/0.98  --prop_impl_unit                        []
% 3.53/0.98  --share_sel_clauses                     true
% 3.53/0.98  --reset_solvers                         false
% 3.53/0.98  --bc_imp_inh                            [conj_cone]
% 3.53/0.98  --conj_cone_tolerance                   3.
% 3.53/0.98  --extra_neg_conj                        none
% 3.53/0.98  --large_theory_mode                     true
% 3.53/0.98  --prolific_symb_bound                   200
% 3.53/0.98  --lt_threshold                          2000
% 3.53/0.98  --clause_weak_htbl                      true
% 3.53/0.98  --gc_record_bc_elim                     false
% 3.53/0.98  
% 3.53/0.98  ------ Preprocessing Options
% 3.53/0.98  
% 3.53/0.98  --preprocessing_flag                    true
% 3.53/0.98  --time_out_prep_mult                    0.1
% 3.53/0.98  --splitting_mode                        input
% 3.53/0.98  --splitting_grd                         true
% 3.53/0.98  --splitting_cvd                         false
% 3.53/0.98  --splitting_cvd_svl                     false
% 3.53/0.98  --splitting_nvd                         32
% 3.53/0.98  --sub_typing                            true
% 3.53/0.98  --prep_gs_sim                           true
% 3.53/0.98  --prep_unflatten                        true
% 3.53/0.98  --prep_res_sim                          true
% 3.53/0.98  --prep_upred                            true
% 3.53/0.98  --prep_sem_filter                       exhaustive
% 3.53/0.98  --prep_sem_filter_out                   false
% 3.53/0.98  --pred_elim                             true
% 3.53/0.98  --res_sim_input                         true
% 3.53/0.98  --eq_ax_congr_red                       true
% 3.53/0.98  --pure_diseq_elim                       true
% 3.53/0.98  --brand_transform                       false
% 3.53/0.98  --non_eq_to_eq                          false
% 3.53/0.98  --prep_def_merge                        true
% 3.53/0.98  --prep_def_merge_prop_impl              false
% 3.53/0.98  --prep_def_merge_mbd                    true
% 3.53/0.98  --prep_def_merge_tr_red                 false
% 3.53/0.98  --prep_def_merge_tr_cl                  false
% 3.53/0.98  --smt_preprocessing                     true
% 3.53/0.98  --smt_ac_axioms                         fast
% 3.53/0.98  --preprocessed_out                      false
% 3.53/0.98  --preprocessed_stats                    false
% 3.53/0.98  
% 3.53/0.98  ------ Abstraction refinement Options
% 3.53/0.98  
% 3.53/0.98  --abstr_ref                             []
% 3.53/0.98  --abstr_ref_prep                        false
% 3.53/0.98  --abstr_ref_until_sat                   false
% 3.53/0.98  --abstr_ref_sig_restrict                funpre
% 3.53/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.98  --abstr_ref_under                       []
% 3.53/0.98  
% 3.53/0.98  ------ SAT Options
% 3.53/0.98  
% 3.53/0.98  --sat_mode                              false
% 3.53/0.98  --sat_fm_restart_options                ""
% 3.53/0.98  --sat_gr_def                            false
% 3.53/0.98  --sat_epr_types                         true
% 3.53/0.98  --sat_non_cyclic_types                  false
% 3.53/0.98  --sat_finite_models                     false
% 3.53/0.98  --sat_fm_lemmas                         false
% 3.53/0.98  --sat_fm_prep                           false
% 3.53/0.98  --sat_fm_uc_incr                        true
% 3.53/0.98  --sat_out_model                         small
% 3.53/0.98  --sat_out_clauses                       false
% 3.53/0.98  
% 3.53/0.98  ------ QBF Options
% 3.53/0.98  
% 3.53/0.98  --qbf_mode                              false
% 3.53/0.98  --qbf_elim_univ                         false
% 3.53/0.98  --qbf_dom_inst                          none
% 3.53/0.98  --qbf_dom_pre_inst                      false
% 3.53/0.98  --qbf_sk_in                             false
% 3.53/0.98  --qbf_pred_elim                         true
% 3.53/0.98  --qbf_split                             512
% 3.53/0.98  
% 3.53/0.98  ------ BMC1 Options
% 3.53/0.98  
% 3.53/0.98  --bmc1_incremental                      false
% 3.53/0.98  --bmc1_axioms                           reachable_all
% 3.53/0.98  --bmc1_min_bound                        0
% 3.53/0.98  --bmc1_max_bound                        -1
% 3.53/0.98  --bmc1_max_bound_default                -1
% 3.53/0.98  --bmc1_symbol_reachability              true
% 3.53/0.98  --bmc1_property_lemmas                  false
% 3.53/0.98  --bmc1_k_induction                      false
% 3.53/0.98  --bmc1_non_equiv_states                 false
% 3.53/0.98  --bmc1_deadlock                         false
% 3.53/0.98  --bmc1_ucm                              false
% 3.53/0.98  --bmc1_add_unsat_core                   none
% 3.53/0.98  --bmc1_unsat_core_children              false
% 3.53/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.98  --bmc1_out_stat                         full
% 3.53/0.98  --bmc1_ground_init                      false
% 3.53/0.98  --bmc1_pre_inst_next_state              false
% 3.53/0.98  --bmc1_pre_inst_state                   false
% 3.53/0.98  --bmc1_pre_inst_reach_state             false
% 3.53/0.98  --bmc1_out_unsat_core                   false
% 3.53/0.98  --bmc1_aig_witness_out                  false
% 3.53/0.98  --bmc1_verbose                          false
% 3.53/0.98  --bmc1_dump_clauses_tptp                false
% 3.53/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.98  --bmc1_dump_file                        -
% 3.53/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.98  --bmc1_ucm_extend_mode                  1
% 3.53/0.98  --bmc1_ucm_init_mode                    2
% 3.53/0.98  --bmc1_ucm_cone_mode                    none
% 3.53/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.98  --bmc1_ucm_relax_model                  4
% 3.53/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.98  --bmc1_ucm_layered_model                none
% 3.53/0.98  --bmc1_ucm_max_lemma_size               10
% 3.53/0.98  
% 3.53/0.98  ------ AIG Options
% 3.53/0.98  
% 3.53/0.98  --aig_mode                              false
% 3.53/0.98  
% 3.53/0.98  ------ Instantiation Options
% 3.53/0.98  
% 3.53/0.98  --instantiation_flag                    true
% 3.53/0.98  --inst_sos_flag                         false
% 3.53/0.98  --inst_sos_phase                        true
% 3.53/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.98  --inst_lit_sel_side                     num_symb
% 3.53/0.98  --inst_solver_per_active                1400
% 3.53/0.98  --inst_solver_calls_frac                1.
% 3.53/0.98  --inst_passive_queue_type               priority_queues
% 3.53/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.98  --inst_passive_queues_freq              [25;2]
% 3.53/0.98  --inst_dismatching                      true
% 3.53/0.98  --inst_eager_unprocessed_to_passive     true
% 3.53/0.98  --inst_prop_sim_given                   true
% 3.53/0.98  --inst_prop_sim_new                     false
% 3.53/0.98  --inst_subs_new                         false
% 3.53/0.98  --inst_eq_res_simp                      false
% 3.53/0.98  --inst_subs_given                       false
% 3.53/0.98  --inst_orphan_elimination               true
% 3.53/0.98  --inst_learning_loop_flag               true
% 3.53/0.98  --inst_learning_start                   3000
% 3.53/0.98  --inst_learning_factor                  2
% 3.53/0.98  --inst_start_prop_sim_after_learn       3
% 3.53/0.98  --inst_sel_renew                        solver
% 3.53/0.98  --inst_lit_activity_flag                true
% 3.53/0.98  --inst_restr_to_given                   false
% 3.53/0.98  --inst_activity_threshold               500
% 3.53/0.98  --inst_out_proof                        true
% 3.53/0.98  
% 3.53/0.98  ------ Resolution Options
% 3.53/0.98  
% 3.53/0.98  --resolution_flag                       true
% 3.53/0.98  --res_lit_sel                           adaptive
% 3.53/0.98  --res_lit_sel_side                      none
% 3.53/0.98  --res_ordering                          kbo
% 3.53/0.98  --res_to_prop_solver                    active
% 3.53/0.98  --res_prop_simpl_new                    false
% 3.53/0.98  --res_prop_simpl_given                  true
% 3.53/0.98  --res_passive_queue_type                priority_queues
% 3.53/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.98  --res_passive_queues_freq               [15;5]
% 3.53/0.98  --res_forward_subs                      full
% 3.53/0.98  --res_backward_subs                     full
% 3.53/0.98  --res_forward_subs_resolution           true
% 3.53/0.98  --res_backward_subs_resolution          true
% 3.53/0.98  --res_orphan_elimination                true
% 3.53/0.98  --res_time_limit                        2.
% 3.53/0.98  --res_out_proof                         true
% 3.53/0.98  
% 3.53/0.98  ------ Superposition Options
% 3.53/0.98  
% 3.53/0.98  --superposition_flag                    true
% 3.53/0.98  --sup_passive_queue_type                priority_queues
% 3.53/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.98  --demod_completeness_check              fast
% 3.53/0.98  --demod_use_ground                      true
% 3.53/0.98  --sup_to_prop_solver                    passive
% 3.53/0.98  --sup_prop_simpl_new                    true
% 3.53/0.98  --sup_prop_simpl_given                  true
% 3.53/0.98  --sup_fun_splitting                     false
% 3.53/0.98  --sup_smt_interval                      50000
% 3.53/0.98  
% 3.53/0.98  ------ Superposition Simplification Setup
% 3.53/0.98  
% 3.53/0.98  --sup_indices_passive                   []
% 3.53/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.98  --sup_full_bw                           [BwDemod]
% 3.53/0.98  --sup_immed_triv                        [TrivRules]
% 3.53/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.98  --sup_immed_bw_main                     []
% 3.53/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.98  
% 3.53/0.98  ------ Combination Options
% 3.53/0.98  
% 3.53/0.98  --comb_res_mult                         3
% 3.53/0.98  --comb_sup_mult                         2
% 3.53/0.98  --comb_inst_mult                        10
% 3.53/0.98  
% 3.53/0.98  ------ Debug Options
% 3.53/0.98  
% 3.53/0.98  --dbg_backtrace                         false
% 3.53/0.98  --dbg_dump_prop_clauses                 false
% 3.53/0.98  --dbg_dump_prop_clauses_file            -
% 3.53/0.98  --dbg_out_stat                          false
% 3.53/0.98  ------ Parsing...
% 3.53/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.98  
% 3.53/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.53/0.98  
% 3.53/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.98  
% 3.53/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.98  ------ Proving...
% 3.53/0.98  ------ Problem Properties 
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  clauses                                 33
% 3.53/0.98  conjectures                             8
% 3.53/0.98  EPR                                     8
% 3.53/0.98  Horn                                    32
% 3.53/0.98  unary                                   20
% 3.53/0.98  binary                                  5
% 3.53/0.98  lits                                    78
% 3.53/0.98  lits eq                                 20
% 3.53/0.98  fd_pure                                 0
% 3.53/0.98  fd_pseudo                               0
% 3.53/0.98  fd_cond                                 2
% 3.53/0.98  fd_pseudo_cond                          4
% 3.53/0.98  AC symbols                              0
% 3.53/0.98  
% 3.53/0.98  ------ Schedule dynamic 5 is on 
% 3.53/0.98  
% 3.53/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  ------ 
% 3.53/0.98  Current options:
% 3.53/0.98  ------ 
% 3.53/0.98  
% 3.53/0.98  ------ Input Options
% 3.53/0.98  
% 3.53/0.98  --out_options                           all
% 3.53/0.98  --tptp_safe_out                         true
% 3.53/0.98  --problem_path                          ""
% 3.53/0.98  --include_path                          ""
% 3.53/0.98  --clausifier                            res/vclausify_rel
% 3.53/0.98  --clausifier_options                    --mode clausify
% 3.53/0.98  --stdin                                 false
% 3.53/0.98  --stats_out                             all
% 3.53/0.98  
% 3.53/0.98  ------ General Options
% 3.53/0.98  
% 3.53/0.98  --fof                                   false
% 3.53/0.98  --time_out_real                         305.
% 3.53/0.98  --time_out_virtual                      -1.
% 3.53/0.98  --symbol_type_check                     false
% 3.53/0.98  --clausify_out                          false
% 3.53/0.98  --sig_cnt_out                           false
% 3.53/0.98  --trig_cnt_out                          false
% 3.53/0.98  --trig_cnt_out_tolerance                1.
% 3.53/0.98  --trig_cnt_out_sk_spl                   false
% 3.53/0.98  --abstr_cl_out                          false
% 3.53/0.98  
% 3.53/0.98  ------ Global Options
% 3.53/0.98  
% 3.53/0.98  --schedule                              default
% 3.53/0.98  --add_important_lit                     false
% 3.53/0.98  --prop_solver_per_cl                    1000
% 3.53/0.98  --min_unsat_core                        false
% 3.53/0.98  --soft_assumptions                      false
% 3.53/0.98  --soft_lemma_size                       3
% 3.53/0.98  --prop_impl_unit_size                   0
% 3.53/0.98  --prop_impl_unit                        []
% 3.53/0.98  --share_sel_clauses                     true
% 3.53/0.98  --reset_solvers                         false
% 3.53/0.98  --bc_imp_inh                            [conj_cone]
% 3.53/0.98  --conj_cone_tolerance                   3.
% 3.53/0.98  --extra_neg_conj                        none
% 3.53/0.98  --large_theory_mode                     true
% 3.53/0.98  --prolific_symb_bound                   200
% 3.53/0.98  --lt_threshold                          2000
% 3.53/0.98  --clause_weak_htbl                      true
% 3.53/0.98  --gc_record_bc_elim                     false
% 3.53/0.98  
% 3.53/0.98  ------ Preprocessing Options
% 3.53/0.98  
% 3.53/0.98  --preprocessing_flag                    true
% 3.53/0.98  --time_out_prep_mult                    0.1
% 3.53/0.98  --splitting_mode                        input
% 3.53/0.98  --splitting_grd                         true
% 3.53/0.98  --splitting_cvd                         false
% 3.53/0.98  --splitting_cvd_svl                     false
% 3.53/0.98  --splitting_nvd                         32
% 3.53/0.98  --sub_typing                            true
% 3.53/0.98  --prep_gs_sim                           true
% 3.53/0.98  --prep_unflatten                        true
% 3.53/0.98  --prep_res_sim                          true
% 3.53/0.98  --prep_upred                            true
% 3.53/0.98  --prep_sem_filter                       exhaustive
% 3.53/0.98  --prep_sem_filter_out                   false
% 3.53/0.98  --pred_elim                             true
% 3.53/0.98  --res_sim_input                         true
% 3.53/0.98  --eq_ax_congr_red                       true
% 3.53/0.98  --pure_diseq_elim                       true
% 3.53/0.98  --brand_transform                       false
% 3.53/0.98  --non_eq_to_eq                          false
% 3.53/0.98  --prep_def_merge                        true
% 3.53/0.98  --prep_def_merge_prop_impl              false
% 3.53/0.98  --prep_def_merge_mbd                    true
% 3.53/0.98  --prep_def_merge_tr_red                 false
% 3.53/0.98  --prep_def_merge_tr_cl                  false
% 3.53/0.98  --smt_preprocessing                     true
% 3.53/0.98  --smt_ac_axioms                         fast
% 3.53/0.98  --preprocessed_out                      false
% 3.53/0.98  --preprocessed_stats                    false
% 3.53/0.98  
% 3.53/0.98  ------ Abstraction refinement Options
% 3.53/0.98  
% 3.53/0.98  --abstr_ref                             []
% 3.53/0.98  --abstr_ref_prep                        false
% 3.53/0.98  --abstr_ref_until_sat                   false
% 3.53/0.98  --abstr_ref_sig_restrict                funpre
% 3.53/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.98  --abstr_ref_under                       []
% 3.53/0.98  
% 3.53/0.98  ------ SAT Options
% 3.53/0.98  
% 3.53/0.98  --sat_mode                              false
% 3.53/0.98  --sat_fm_restart_options                ""
% 3.53/0.98  --sat_gr_def                            false
% 3.53/0.98  --sat_epr_types                         true
% 3.53/0.98  --sat_non_cyclic_types                  false
% 3.53/0.98  --sat_finite_models                     false
% 3.53/0.98  --sat_fm_lemmas                         false
% 3.53/0.98  --sat_fm_prep                           false
% 3.53/0.98  --sat_fm_uc_incr                        true
% 3.53/0.98  --sat_out_model                         small
% 3.53/0.98  --sat_out_clauses                       false
% 3.53/0.98  
% 3.53/0.98  ------ QBF Options
% 3.53/0.98  
% 3.53/0.98  --qbf_mode                              false
% 3.53/0.98  --qbf_elim_univ                         false
% 3.53/0.98  --qbf_dom_inst                          none
% 3.53/0.98  --qbf_dom_pre_inst                      false
% 3.53/0.98  --qbf_sk_in                             false
% 3.53/0.98  --qbf_pred_elim                         true
% 3.53/0.98  --qbf_split                             512
% 3.53/0.98  
% 3.53/0.98  ------ BMC1 Options
% 3.53/0.98  
% 3.53/0.98  --bmc1_incremental                      false
% 3.53/0.98  --bmc1_axioms                           reachable_all
% 3.53/0.98  --bmc1_min_bound                        0
% 3.53/0.98  --bmc1_max_bound                        -1
% 3.53/0.98  --bmc1_max_bound_default                -1
% 3.53/0.98  --bmc1_symbol_reachability              true
% 3.53/0.98  --bmc1_property_lemmas                  false
% 3.53/0.98  --bmc1_k_induction                      false
% 3.53/0.98  --bmc1_non_equiv_states                 false
% 3.53/0.98  --bmc1_deadlock                         false
% 3.53/0.98  --bmc1_ucm                              false
% 3.53/0.98  --bmc1_add_unsat_core                   none
% 3.53/0.98  --bmc1_unsat_core_children              false
% 3.53/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.98  --bmc1_out_stat                         full
% 3.53/0.98  --bmc1_ground_init                      false
% 3.53/0.98  --bmc1_pre_inst_next_state              false
% 3.53/0.98  --bmc1_pre_inst_state                   false
% 3.53/0.98  --bmc1_pre_inst_reach_state             false
% 3.53/0.98  --bmc1_out_unsat_core                   false
% 3.53/0.98  --bmc1_aig_witness_out                  false
% 3.53/0.98  --bmc1_verbose                          false
% 3.53/0.98  --bmc1_dump_clauses_tptp                false
% 3.53/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.98  --bmc1_dump_file                        -
% 3.53/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.98  --bmc1_ucm_extend_mode                  1
% 3.53/0.98  --bmc1_ucm_init_mode                    2
% 3.53/0.98  --bmc1_ucm_cone_mode                    none
% 3.53/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.98  --bmc1_ucm_relax_model                  4
% 3.53/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.98  --bmc1_ucm_layered_model                none
% 3.53/0.98  --bmc1_ucm_max_lemma_size               10
% 3.53/0.98  
% 3.53/0.98  ------ AIG Options
% 3.53/0.98  
% 3.53/0.98  --aig_mode                              false
% 3.53/0.98  
% 3.53/0.98  ------ Instantiation Options
% 3.53/0.98  
% 3.53/0.98  --instantiation_flag                    true
% 3.53/0.98  --inst_sos_flag                         false
% 3.53/0.98  --inst_sos_phase                        true
% 3.53/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.98  --inst_lit_sel_side                     none
% 3.53/0.98  --inst_solver_per_active                1400
% 3.53/0.98  --inst_solver_calls_frac                1.
% 3.53/0.98  --inst_passive_queue_type               priority_queues
% 3.53/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.98  --inst_passive_queues_freq              [25;2]
% 3.53/0.98  --inst_dismatching                      true
% 3.53/0.98  --inst_eager_unprocessed_to_passive     true
% 3.53/0.98  --inst_prop_sim_given                   true
% 3.53/0.98  --inst_prop_sim_new                     false
% 3.53/0.98  --inst_subs_new                         false
% 3.53/0.98  --inst_eq_res_simp                      false
% 3.53/0.98  --inst_subs_given                       false
% 3.53/0.98  --inst_orphan_elimination               true
% 3.53/0.98  --inst_learning_loop_flag               true
% 3.53/0.98  --inst_learning_start                   3000
% 3.53/0.98  --inst_learning_factor                  2
% 3.53/0.98  --inst_start_prop_sim_after_learn       3
% 3.53/0.98  --inst_sel_renew                        solver
% 3.53/0.98  --inst_lit_activity_flag                true
% 3.53/0.98  --inst_restr_to_given                   false
% 3.53/0.98  --inst_activity_threshold               500
% 3.53/0.98  --inst_out_proof                        true
% 3.53/0.98  
% 3.53/0.98  ------ Resolution Options
% 3.53/0.98  
% 3.53/0.98  --resolution_flag                       false
% 3.53/0.98  --res_lit_sel                           adaptive
% 3.53/0.98  --res_lit_sel_side                      none
% 3.53/0.98  --res_ordering                          kbo
% 3.53/0.98  --res_to_prop_solver                    active
% 3.53/0.98  --res_prop_simpl_new                    false
% 3.53/0.98  --res_prop_simpl_given                  true
% 3.53/0.98  --res_passive_queue_type                priority_queues
% 3.53/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.98  --res_passive_queues_freq               [15;5]
% 3.53/0.98  --res_forward_subs                      full
% 3.53/0.98  --res_backward_subs                     full
% 3.53/0.98  --res_forward_subs_resolution           true
% 3.53/0.98  --res_backward_subs_resolution          true
% 3.53/0.98  --res_orphan_elimination                true
% 3.53/0.98  --res_time_limit                        2.
% 3.53/0.98  --res_out_proof                         true
% 3.53/0.98  
% 3.53/0.98  ------ Superposition Options
% 3.53/0.98  
% 3.53/0.98  --superposition_flag                    true
% 3.53/0.98  --sup_passive_queue_type                priority_queues
% 3.53/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.98  --demod_completeness_check              fast
% 3.53/0.98  --demod_use_ground                      true
% 3.53/0.98  --sup_to_prop_solver                    passive
% 3.53/0.98  --sup_prop_simpl_new                    true
% 3.53/0.98  --sup_prop_simpl_given                  true
% 3.53/0.98  --sup_fun_splitting                     false
% 3.53/0.98  --sup_smt_interval                      50000
% 3.53/0.98  
% 3.53/0.98  ------ Superposition Simplification Setup
% 3.53/0.98  
% 3.53/0.98  --sup_indices_passive                   []
% 3.53/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.98  --sup_full_bw                           [BwDemod]
% 3.53/0.98  --sup_immed_triv                        [TrivRules]
% 3.53/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.98  --sup_immed_bw_main                     []
% 3.53/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.98  
% 3.53/0.98  ------ Combination Options
% 3.53/0.98  
% 3.53/0.98  --comb_res_mult                         3
% 3.53/0.98  --comb_sup_mult                         2
% 3.53/0.98  --comb_inst_mult                        10
% 3.53/0.98  
% 3.53/0.98  ------ Debug Options
% 3.53/0.98  
% 3.53/0.98  --dbg_backtrace                         false
% 3.53/0.98  --dbg_dump_prop_clauses                 false
% 3.53/0.98  --dbg_dump_prop_clauses_file            -
% 3.53/0.98  --dbg_out_stat                          false
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  ------ Proving...
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  % SZS status Theorem for theBenchmark.p
% 3.53/0.98  
% 3.53/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.98  
% 3.53/0.98  fof(f18,conjecture,(
% 3.53/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f19,negated_conjecture,(
% 3.53/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.53/0.98    inference(negated_conjecture,[],[f18])).
% 3.53/0.98  
% 3.53/0.98  fof(f42,plain,(
% 3.53/0.98    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.53/0.98    inference(ennf_transformation,[],[f19])).
% 3.53/0.98  
% 3.53/0.98  fof(f43,plain,(
% 3.53/0.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.53/0.98    inference(flattening,[],[f42])).
% 3.53/0.98  
% 3.53/0.98  fof(f47,plain,(
% 3.53/0.98    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.53/0.98    introduced(choice_axiom,[])).
% 3.53/0.98  
% 3.53/0.98  fof(f46,plain,(
% 3.53/0.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.53/0.98    introduced(choice_axiom,[])).
% 3.53/0.98  
% 3.53/0.98  fof(f48,plain,(
% 3.53/0.98    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.53/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f47,f46])).
% 3.53/0.98  
% 3.53/0.98  fof(f82,plain,(
% 3.53/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f77,plain,(
% 3.53/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f9,axiom,(
% 3.53/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f29,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.98    inference(ennf_transformation,[],[f9])).
% 3.53/0.98  
% 3.53/0.98  fof(f60,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f29])).
% 3.53/0.98  
% 3.53/0.98  fof(f17,axiom,(
% 3.53/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f40,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.53/0.98    inference(ennf_transformation,[],[f17])).
% 3.53/0.98  
% 3.53/0.98  fof(f41,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.53/0.98    inference(flattening,[],[f40])).
% 3.53/0.98  
% 3.53/0.98  fof(f73,plain,(
% 3.53/0.98    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f41])).
% 3.53/0.98  
% 3.53/0.98  fof(f16,axiom,(
% 3.53/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f38,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.53/0.98    inference(ennf_transformation,[],[f16])).
% 3.53/0.98  
% 3.53/0.98  fof(f39,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.53/0.98    inference(flattening,[],[f38])).
% 3.53/0.98  
% 3.53/0.98  fof(f71,plain,(
% 3.53/0.98    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f39])).
% 3.53/0.98  
% 3.53/0.98  fof(f74,plain,(
% 3.53/0.98    v1_funct_1(sK1)),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f75,plain,(
% 3.53/0.98    v1_funct_2(sK1,sK0,sK0)),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f11,axiom,(
% 3.53/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f32,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.98    inference(ennf_transformation,[],[f11])).
% 3.53/0.98  
% 3.53/0.98  fof(f33,plain,(
% 3.53/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.98    inference(flattening,[],[f32])).
% 3.53/0.98  
% 3.53/0.98  fof(f65,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f33])).
% 3.53/0.98  
% 3.53/0.98  fof(f76,plain,(
% 3.53/0.98    v3_funct_2(sK1,sK0,sK0)),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f8,axiom,(
% 3.53/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f21,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.53/0.98    inference(pure_predicate_removal,[],[f8])).
% 3.53/0.98  
% 3.53/0.98  fof(f28,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.98    inference(ennf_transformation,[],[f21])).
% 3.53/0.98  
% 3.53/0.98  fof(f59,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f28])).
% 3.53/0.98  
% 3.53/0.98  fof(f12,axiom,(
% 3.53/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f34,plain,(
% 3.53/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.53/0.98    inference(ennf_transformation,[],[f12])).
% 3.53/0.98  
% 3.53/0.98  fof(f35,plain,(
% 3.53/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.53/0.98    inference(flattening,[],[f34])).
% 3.53/0.98  
% 3.53/0.98  fof(f45,plain,(
% 3.53/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.53/0.98    inference(nnf_transformation,[],[f35])).
% 3.53/0.98  
% 3.53/0.98  fof(f66,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f45])).
% 3.53/0.98  
% 3.53/0.98  fof(f7,axiom,(
% 3.53/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f27,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.98    inference(ennf_transformation,[],[f7])).
% 3.53/0.98  
% 3.53/0.98  fof(f58,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f27])).
% 3.53/0.98  
% 3.53/0.98  fof(f78,plain,(
% 3.53/0.98    v1_funct_1(sK2)),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f79,plain,(
% 3.53/0.98    v1_funct_2(sK2,sK0,sK0)),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f81,plain,(
% 3.53/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f83,plain,(
% 3.53/0.98    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f14,axiom,(
% 3.53/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f36,plain,(
% 3.53/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.53/0.98    inference(ennf_transformation,[],[f14])).
% 3.53/0.98  
% 3.53/0.98  fof(f37,plain,(
% 3.53/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.53/0.98    inference(flattening,[],[f36])).
% 3.53/0.98  
% 3.53/0.98  fof(f69,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f37])).
% 3.53/0.98  
% 3.53/0.98  fof(f10,axiom,(
% 3.53/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f30,plain,(
% 3.53/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.53/0.98    inference(ennf_transformation,[],[f10])).
% 3.53/0.98  
% 3.53/0.98  fof(f31,plain,(
% 3.53/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.98    inference(flattening,[],[f30])).
% 3.53/0.98  
% 3.53/0.98  fof(f44,plain,(
% 3.53/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.98    inference(nnf_transformation,[],[f31])).
% 3.53/0.98  
% 3.53/0.98  fof(f62,plain,(
% 3.53/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f44])).
% 3.53/0.98  
% 3.53/0.98  fof(f89,plain,(
% 3.53/0.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.98    inference(equality_resolution,[],[f62])).
% 3.53/0.98  
% 3.53/0.98  fof(f80,plain,(
% 3.53/0.98    v3_funct_2(sK2,sK0,sK0)),
% 3.53/0.98    inference(cnf_transformation,[],[f48])).
% 3.53/0.98  
% 3.53/0.98  fof(f2,axiom,(
% 3.53/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f22,plain,(
% 3.53/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.53/0.98    inference(ennf_transformation,[],[f2])).
% 3.53/0.98  
% 3.53/0.98  fof(f23,plain,(
% 3.53/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.53/0.98    inference(flattening,[],[f22])).
% 3.53/0.98  
% 3.53/0.98  fof(f52,plain,(
% 3.53/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f23])).
% 3.53/0.98  
% 3.53/0.98  fof(f4,axiom,(
% 3.53/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f54,plain,(
% 3.53/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.53/0.98    inference(cnf_transformation,[],[f4])).
% 3.53/0.98  
% 3.53/0.98  fof(f15,axiom,(
% 3.53/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f70,plain,(
% 3.53/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f15])).
% 3.53/0.98  
% 3.53/0.98  fof(f85,plain,(
% 3.53/0.98    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.53/0.98    inference(definition_unfolding,[],[f54,f70])).
% 3.53/0.98  
% 3.53/0.98  fof(f5,axiom,(
% 3.53/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f55,plain,(
% 3.53/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f5])).
% 3.53/0.98  
% 3.53/0.98  fof(f87,plain,(
% 3.53/0.98    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.53/0.98    inference(definition_unfolding,[],[f55,f70])).
% 3.53/0.98  
% 3.53/0.98  fof(f3,axiom,(
% 3.53/0.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f24,plain,(
% 3.53/0.98    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.53/0.98    inference(ennf_transformation,[],[f3])).
% 3.53/0.98  
% 3.53/0.98  fof(f53,plain,(
% 3.53/0.98    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f24])).
% 3.53/0.98  
% 3.53/0.98  fof(f84,plain,(
% 3.53/0.98    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f53,f70])).
% 3.53/0.98  
% 3.53/0.98  fof(f6,axiom,(
% 3.53/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f25,plain,(
% 3.53/0.98    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.53/0.98    inference(ennf_transformation,[],[f6])).
% 3.53/0.98  
% 3.53/0.98  fof(f26,plain,(
% 3.53/0.98    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.53/0.98    inference(flattening,[],[f25])).
% 3.53/0.98  
% 3.53/0.98  fof(f57,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f26])).
% 3.53/0.98  
% 3.53/0.98  fof(f88,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f57,f70])).
% 3.53/0.98  
% 3.53/0.98  fof(f56,plain,(
% 3.53/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f5])).
% 3.53/0.98  
% 3.53/0.98  fof(f86,plain,(
% 3.53/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.53/0.98    inference(definition_unfolding,[],[f56,f70])).
% 3.53/0.98  
% 3.53/0.98  fof(f1,axiom,(
% 3.53/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f49,plain,(
% 3.53/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.53/0.98    inference(cnf_transformation,[],[f1])).
% 3.53/0.98  
% 3.53/0.98  fof(f50,plain,(
% 3.53/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.53/0.98    inference(cnf_transformation,[],[f1])).
% 3.53/0.98  
% 3.53/0.98  fof(f13,axiom,(
% 3.53/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.53/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f20,plain,(
% 3.53/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.53/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.53/0.98  
% 3.53/0.98  fof(f68,plain,(
% 3.53/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f20])).
% 3.53/0.98  
% 3.53/0.98  cnf(c_25,negated_conjecture,
% 3.53/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.53/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1732,negated_conjecture,
% 3.53/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2312,plain,
% 3.53/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1732]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_30,negated_conjecture,
% 3.53/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.53/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1728,negated_conjecture,
% 3.53/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_30]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2316,plain,
% 3.53/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1728]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_11,plain,
% 3.53/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1739,plain,
% 3.53/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 3.53/0.98      | k2_relset_1(X1_51,X2_51,X0_51) = k2_relat_1(X0_51) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2305,plain,
% 3.53/0.98      ( k2_relset_1(X0_51,X1_51,X2_51) = k2_relat_1(X2_51)
% 3.53/0.98      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1739]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4021,plain,
% 3.53/0.98      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_2316,c_2305]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_23,plain,
% 3.53/0.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.53/0.98      | ~ v1_funct_2(X3,X1,X0)
% 3.53/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.53/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.53/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.53/0.98      | ~ v1_funct_1(X2)
% 3.53/0.98      | ~ v1_funct_1(X3)
% 3.53/0.98      | ~ v2_funct_1(X2)
% 3.53/0.98      | k2_relset_1(X0,X1,X2) != X1
% 3.53/0.98      | k2_funct_1(X2) = X3
% 3.53/0.98      | k1_xboole_0 = X0
% 3.53/0.98      | k1_xboole_0 = X1 ),
% 3.53/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_22,plain,
% 3.53/0.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.53/0.98      | ~ v1_funct_2(X3,X1,X0)
% 3.53/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.53/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.53/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.53/0.98      | ~ v1_funct_1(X2)
% 3.53/0.98      | ~ v1_funct_1(X3)
% 3.53/0.98      | v2_funct_1(X2) ),
% 3.53/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_178,plain,
% 3.53/0.98      ( ~ v1_funct_1(X3)
% 3.53/0.98      | ~ v1_funct_1(X2)
% 3.53/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.53/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.53/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.53/0.98      | ~ v1_funct_2(X3,X1,X0)
% 3.53/0.98      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.53/0.98      | k2_relset_1(X0,X1,X2) != X1
% 3.53/0.98      | k2_funct_1(X2) = X3
% 3.53/0.98      | k1_xboole_0 = X0
% 3.53/0.98      | k1_xboole_0 = X1 ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_23,c_22]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_179,plain,
% 3.53/0.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.53/0.98      | ~ v1_funct_2(X3,X1,X0)
% 3.53/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.53/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.53/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.53/0.98      | ~ v1_funct_1(X2)
% 3.53/0.98      | ~ v1_funct_1(X3)
% 3.53/0.98      | k2_relset_1(X0,X1,X2) != X1
% 3.53/0.98      | k2_funct_1(X2) = X3
% 3.53/0.98      | k1_xboole_0 = X0
% 3.53/0.98      | k1_xboole_0 = X1 ),
% 3.53/0.98      inference(renaming,[status(thm)],[c_178]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1725,plain,
% 3.53/0.98      ( ~ r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51))
% 3.53/0.98      | ~ v1_funct_2(X3_51,X1_51,X0_51)
% 3.53/0.98      | ~ v1_funct_2(X2_51,X0_51,X1_51)
% 3.53/0.98      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.53/0.98      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 3.53/0.98      | ~ v1_funct_1(X2_51)
% 3.53/0.98      | ~ v1_funct_1(X3_51)
% 3.53/0.98      | k2_relset_1(X0_51,X1_51,X2_51) != X1_51
% 3.53/0.98      | k2_funct_1(X2_51) = X3_51
% 3.53/0.98      | k1_xboole_0 = X0_51
% 3.53/0.98      | k1_xboole_0 = X1_51 ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_179]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2319,plain,
% 3.53/0.98      ( k2_relset_1(X0_51,X1_51,X2_51) != X1_51
% 3.53/0.98      | k2_funct_1(X2_51) = X3_51
% 3.53/0.98      | k1_xboole_0 = X0_51
% 3.53/0.98      | k1_xboole_0 = X1_51
% 3.53/0.98      | r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51)) != iProver_top
% 3.53/0.98      | v1_funct_2(X3_51,X1_51,X0_51) != iProver_top
% 3.53/0.98      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 3.53/0.98      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.53/0.98      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
% 3.53/0.98      | v1_funct_1(X2_51) != iProver_top
% 3.53/0.98      | v1_funct_1(X3_51) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1725]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5073,plain,
% 3.53/0.98      ( k2_funct_1(sK1) = X0_51
% 3.53/0.98      | k2_relat_1(sK1) != sK0
% 3.53/0.98      | sK0 = k1_xboole_0
% 3.53/0.98      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.53/0.98      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.53/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.53/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.53/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.53/0.98      | v1_funct_1(X0_51) != iProver_top
% 3.53/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_4021,c_2319]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_33,negated_conjecture,
% 3.53/0.98      ( v1_funct_1(sK1) ),
% 3.53/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_34,plain,
% 3.53/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_32,negated_conjecture,
% 3.53/0.98      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_35,plain,
% 3.53/0.98      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_37,plain,
% 3.53/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_14,plain,
% 3.53/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.53/0.98      | v2_funct_2(X0,X2)
% 3.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/0.98      | ~ v1_funct_1(X0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_31,negated_conjecture,
% 3.53/0.98      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_494,plain,
% 3.53/0.98      ( v2_funct_2(X0,X1)
% 3.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.53/0.98      | ~ v1_funct_1(X0)
% 3.53/0.98      | sK1 != X0
% 3.53/0.98      | sK0 != X1
% 3.53/0.98      | sK0 != X2 ),
% 3.53/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_495,plain,
% 3.53/0.98      ( v2_funct_2(sK1,sK0)
% 3.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.53/0.98      | ~ v1_funct_1(sK1) ),
% 3.53/0.98      inference(unflattening,[status(thm)],[c_494]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_10,plain,
% 3.53/0.98      ( v5_relat_1(X0,X1)
% 3.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.53/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_18,plain,
% 3.53/0.98      ( ~ v2_funct_2(X0,X1)
% 3.53/0.98      | ~ v5_relat_1(X0,X1)
% 3.53/0.98      | ~ v1_relat_1(X0)
% 3.53/0.98      | k2_relat_1(X0) = X1 ),
% 3.53/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_348,plain,
% 3.53/0.98      ( ~ v2_funct_2(X0,X1)
% 3.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.53/0.98      | ~ v1_relat_1(X0)
% 3.53/0.98      | k2_relat_1(X0) = X1 ),
% 3.53/0.98      inference(resolution,[status(thm)],[c_10,c_18]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_9,plain,
% 3.53/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/0.98      | v1_relat_1(X0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_360,plain,
% 3.53/0.98      ( ~ v2_funct_2(X0,X1)
% 3.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.53/0.98      | k2_relat_1(X0) = X1 ),
% 3.53/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_348,c_9]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1724,plain,
% 3.53/0.98      ( ~ v2_funct_2(X0_51,X1_51)
% 3.53/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 3.53/0.98      | k2_relat_1(X0_51) = X1_51 ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_360]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2579,plain,
% 3.53/0.98      ( ~ v2_funct_2(sK1,sK0)
% 3.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 3.53/0.98      | k2_relat_1(sK1) = sK0 ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_1724]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2581,plain,
% 3.53/0.98      ( ~ v2_funct_2(sK1,sK0)
% 3.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.53/0.98      | k2_relat_1(sK1) = sK0 ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_2579]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7303,plain,
% 3.53/0.98      ( v1_funct_1(X0_51) != iProver_top
% 3.53/0.98      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.53/0.98      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.53/0.98      | sK0 = k1_xboole_0
% 3.53/0.98      | k2_funct_1(sK1) = X0_51
% 3.53/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_5073,c_33,c_34,c_35,c_30,c_37,c_495,c_2581]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7304,plain,
% 3.53/0.98      ( k2_funct_1(sK1) = X0_51
% 3.53/0.98      | sK0 = k1_xboole_0
% 3.53/0.98      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.53/0.98      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.53/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.53/0.98      | v1_funct_1(X0_51) != iProver_top ),
% 3.53/0.98      inference(renaming,[status(thm)],[c_7303]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7315,plain,
% 3.53/0.98      ( k2_funct_1(sK1) = sK2
% 3.53/0.98      | sK0 = k1_xboole_0
% 3.53/0.98      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.53/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.53/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_2312,c_7304]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_29,negated_conjecture,
% 3.53/0.98      ( v1_funct_1(sK2) ),
% 3.53/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_28,negated_conjecture,
% 3.53/0.98      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_26,negated_conjecture,
% 3.53/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.53/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7316,plain,
% 3.53/0.98      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.53/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.53/0.98      | ~ v1_funct_1(sK2)
% 3.53/0.98      | k2_funct_1(sK1) = sK2
% 3.53/0.98      | sK0 = k1_xboole_0 ),
% 3.53/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_7315]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7478,plain,
% 3.53/0.98      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_7315,c_38,c_39,c_41]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7479,plain,
% 3.53/0.98      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.53/0.98      inference(renaming,[status(thm)],[c_7478]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_24,negated_conjecture,
% 3.53/0.98      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.53/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1733,negated_conjecture,
% 3.53/0.98      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2311,plain,
% 3.53/0.98      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1733]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_20,plain,
% 3.53/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.53/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.53/0.98      | ~ v1_funct_1(X0)
% 3.53/0.98      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_513,plain,
% 3.53/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.53/0.98      | ~ v1_funct_1(X0)
% 3.53/0.98      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.53/0.98      | sK1 != X0
% 3.53/0.98      | sK0 != X1 ),
% 3.53/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_514,plain,
% 3.53/0.98      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.53/0.98      | ~ v1_funct_1(sK1)
% 3.53/0.98      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.53/0.98      inference(unflattening,[status(thm)],[c_513]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_516,plain,
% 3.53/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_514,c_33,c_32,c_30]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1717,plain,
% 3.53/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_516]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2362,plain,
% 3.53/0.98      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.53/0.98      inference(light_normalisation,[status(thm)],[c_2311,c_1717]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7482,plain,
% 3.53/0.98      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_7479,c_2362]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_41,plain,
% 3.53/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_12,plain,
% 3.53/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 3.53/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.53/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1738,plain,
% 3.53/0.98      ( r2_relset_1(X0_51,X1_51,X2_51,X2_51)
% 3.53/0.98      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2584,plain,
% 3.53/0.98      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.53/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_1738]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2585,plain,
% 3.53/0.98      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.53/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_2584]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7485,plain,
% 3.53/0.98      ( sK0 = k1_xboole_0 ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_7482,c_41,c_2585]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1731,negated_conjecture,
% 3.53/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_26]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2313,plain,
% 3.53/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1731]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2320,plain,
% 3.53/0.98      ( k2_relat_1(X0_51) = X1_51
% 3.53/0.98      | v2_funct_2(X0_51,X1_51) != iProver_top
% 3.53/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51))) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1724]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5205,plain,
% 3.53/0.98      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_2313,c_2320]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_27,negated_conjecture,
% 3.53/0.98      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_472,plain,
% 3.53/0.98      ( v2_funct_2(X0,X1)
% 3.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.53/0.98      | ~ v1_funct_1(X0)
% 3.53/0.98      | sK2 != X0
% 3.53/0.98      | sK0 != X1
% 3.53/0.98      | sK0 != X2 ),
% 3.53/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_473,plain,
% 3.53/0.98      ( v2_funct_2(sK2,sK0)
% 3.53/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.53/0.98      | ~ v1_funct_1(sK2) ),
% 3.53/0.98      inference(unflattening,[status(thm)],[c_472]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2574,plain,
% 3.53/0.98      ( ~ v2_funct_2(sK2,sK0)
% 3.53/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 3.53/0.98      | k2_relat_1(sK2) = sK0 ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_1724]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2576,plain,
% 3.53/0.98      ( ~ v2_funct_2(sK2,sK0)
% 3.53/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.53/0.98      | k2_relat_1(sK2) = sK0 ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_2574]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5566,plain,
% 3.53/0.98      ( k2_relat_1(sK2) = sK0 ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_5205,c_29,c_26,c_473,c_2576]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2,plain,
% 3.53/0.98      ( ~ v1_relat_1(X0)
% 3.53/0.98      | k2_relat_1(X0) != k1_xboole_0
% 3.53/0.98      | k1_xboole_0 = X0 ),
% 3.53/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1747,plain,
% 3.53/0.98      ( ~ v1_relat_1(X0_51)
% 3.53/0.98      | k2_relat_1(X0_51) != k1_xboole_0
% 3.53/0.98      | k1_xboole_0 = X0_51 ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2298,plain,
% 3.53/0.98      ( k2_relat_1(X0_51) != k1_xboole_0
% 3.53/0.98      | k1_xboole_0 = X0_51
% 3.53/0.98      | v1_relat_1(X0_51) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1747]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5586,plain,
% 3.53/0.98      ( sK2 = k1_xboole_0
% 3.53/0.98      | sK0 != k1_xboole_0
% 3.53/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_5566,c_2298]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1740,plain,
% 3.53/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 3.53/0.98      | v1_relat_1(X0_51) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2550,plain,
% 3.53/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.53/0.98      | v1_relat_1(sK2) ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_1740]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2551,plain,
% 3.53/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.53/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_2550]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5991,plain,
% 3.53/0.98      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_5586,c_41,c_2551]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5992,plain,
% 3.53/0.98      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.53/0.98      inference(renaming,[status(thm)],[c_5991]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7493,plain,
% 3.53/0.98      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.53/0.98      inference(demodulation,[status(thm)],[c_7485,c_5992]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7587,plain,
% 3.53/0.98      ( sK2 = k1_xboole_0 ),
% 3.53/0.98      inference(equality_resolution_simp,[status(thm)],[c_7493]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1729,negated_conjecture,
% 3.53/0.98      ( v1_funct_1(sK2) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_29]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2315,plain,
% 3.53/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1729]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_8389,plain,
% 3.53/0.98      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.53/0.98      inference(demodulation,[status(thm)],[c_7587,c_2315]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5,plain,
% 3.53/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.53/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1744,plain,
% 3.53/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7,plain,
% 3.53/0.98      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.53/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1742,plain,
% 3.53/0.98      ( v1_relat_1(k6_partfun1(X0_51)) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2302,plain,
% 3.53/0.98      ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1742]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4,plain,
% 3.53/0.98      ( ~ v1_relat_1(X0)
% 3.53/0.98      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 3.53/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1745,plain,
% 3.53/0.98      ( ~ v1_relat_1(X0_51)
% 3.53/0.98      | k5_relat_1(X0_51,k6_partfun1(k2_relat_1(X0_51))) = X0_51 ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2300,plain,
% 3.53/0.98      ( k5_relat_1(X0_51,k6_partfun1(k2_relat_1(X0_51))) = X0_51
% 3.53/0.98      | v1_relat_1(X0_51) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1745]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_3171,plain,
% 3.53/0.98      ( k5_relat_1(k6_partfun1(X0_51),k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51) ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_2302,c_2300]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_8,plain,
% 3.53/0.98      ( ~ v1_funct_1(X0)
% 3.53/0.98      | ~ v1_funct_1(X1)
% 3.53/0.98      | ~ v2_funct_1(X1)
% 3.53/0.98      | ~ v1_relat_1(X1)
% 3.53/0.98      | ~ v1_relat_1(X0)
% 3.53/0.98      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.53/0.98      | k2_funct_1(X1) = X0
% 3.53/0.98      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1741,plain,
% 3.53/0.98      ( ~ v1_funct_1(X0_51)
% 3.53/0.98      | ~ v1_funct_1(X1_51)
% 3.53/0.98      | ~ v2_funct_1(X1_51)
% 3.53/0.98      | ~ v1_relat_1(X1_51)
% 3.53/0.98      | ~ v1_relat_1(X0_51)
% 3.53/0.98      | k5_relat_1(X0_51,X1_51) != k6_partfun1(k2_relat_1(X1_51))
% 3.53/0.98      | k2_funct_1(X1_51) = X0_51
% 3.53/0.98      | k1_relat_1(X1_51) != k2_relat_1(X0_51) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2303,plain,
% 3.53/0.98      ( k5_relat_1(X0_51,X1_51) != k6_partfun1(k2_relat_1(X1_51))
% 3.53/0.98      | k2_funct_1(X1_51) = X0_51
% 3.53/0.98      | k1_relat_1(X1_51) != k2_relat_1(X0_51)
% 3.53/0.98      | v1_funct_1(X1_51) != iProver_top
% 3.53/0.98      | v1_funct_1(X0_51) != iProver_top
% 3.53/0.98      | v2_funct_1(X1_51) != iProver_top
% 3.53/0.98      | v1_relat_1(X0_51) != iProver_top
% 3.53/0.98      | v1_relat_1(X1_51) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1741]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_3898,plain,
% 3.53/0.98      ( k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51)
% 3.53/0.98      | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51))))) != k6_partfun1(X0_51)
% 3.53/0.98      | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
% 3.53/0.98      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.53/0.98      | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
% 3.53/0.98      | v2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
% 3.53/0.98      | v1_relat_1(k6_partfun1(X0_51)) != iProver_top
% 3.53/0.98      | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_3171,c_2303]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1801,plain,
% 3.53/0.98      ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1742]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_6715,plain,
% 3.53/0.98      ( v2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
% 3.53/0.98      | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
% 3.53/0.98      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.53/0.98      | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
% 3.53/0.98      | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51))))) != k6_partfun1(X0_51)
% 3.53/0.98      | k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51)
% 3.53/0.98      | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_3898,c_1801]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_6716,plain,
% 3.53/0.98      ( k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51)
% 3.53/0.98      | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51))))) != k6_partfun1(X0_51)
% 3.53/0.98      | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
% 3.53/0.98      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.53/0.98      | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
% 3.53/0.98      | v2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
% 3.53/0.98      | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
% 3.53/0.98      inference(renaming,[status(thm)],[c_6715]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_6,plain,
% 3.53/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.53/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1743,plain,
% 3.53/0.98      ( v2_funct_1(k6_partfun1(X0_51)) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2301,plain,
% 3.53/0.98      ( v2_funct_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1743]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_6728,plain,
% 3.53/0.98      ( k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51)
% 3.53/0.98      | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51))))) != k6_partfun1(X0_51)
% 3.53/0.98      | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
% 3.53/0.98      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.53/0.98      | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
% 3.53/0.98      inference(forward_subsumption_resolution,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_6716,c_2302,c_2301]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_6732,plain,
% 3.53/0.98      ( k2_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0)))) = k6_partfun1(k1_xboole_0)
% 3.53/0.98      | k6_partfun1(k2_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0))))) != k6_partfun1(k1_xboole_0)
% 3.53/0.98      | k1_relat_1(k6_partfun1(k2_relat_1(k1_xboole_0))) != k2_relat_1(k6_partfun1(k1_xboole_0))
% 3.53/0.98      | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0)))) != iProver_top
% 3.53/0.98      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_1744,c_6728]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1,plain,
% 3.53/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.53/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1748,plain,
% 3.53/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_0,plain,
% 3.53/0.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.53/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1749,plain,
% 3.53/0.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_6733,plain,
% 3.53/0.98      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 3.53/0.98      | k1_xboole_0 != k1_xboole_0
% 3.53/0.98      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.53/0.98      inference(light_normalisation,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_6732,c_1744,c_1748,c_1749]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_6734,plain,
% 3.53/0.98      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 3.53/0.98      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.53/0.98      inference(equality_resolution_simp,[status(thm)],[c_6733]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_8395,plain,
% 3.53/0.98      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_8389,c_6734]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5206,plain,
% 3.53/0.98      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_2316,c_2320]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5598,plain,
% 3.53/0.98      ( k2_relat_1(sK1) = sK0 ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_5206,c_33,c_30,c_495,c_2581]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5618,plain,
% 3.53/0.98      ( sK1 = k1_xboole_0
% 3.53/0.98      | sK0 != k1_xboole_0
% 3.53/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_5598,c_2298]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2553,plain,
% 3.53/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.53/0.98      | v1_relat_1(sK1) ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_1740]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2554,plain,
% 3.53/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.53/0.98      | v1_relat_1(sK1) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_2553]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5996,plain,
% 3.53/0.98      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_5618,c_37,c_2554]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5997,plain,
% 3.53/0.98      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.53/0.98      inference(renaming,[status(thm)],[c_5996]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7492,plain,
% 3.53/0.98      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.53/0.98      inference(demodulation,[status(thm)],[c_7485,c_5997]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7615,plain,
% 3.53/0.98      ( sK1 = k1_xboole_0 ),
% 3.53/0.98      inference(equality_resolution_simp,[status(thm)],[c_7492]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7508,plain,
% 3.53/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.53/0.98      inference(demodulation,[status(thm)],[c_7485,c_2362]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7596,plain,
% 3.53/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 3.53/0.98      inference(demodulation,[status(thm)],[c_7587,c_7508]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7617,plain,
% 3.53/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.53/0.98      inference(demodulation,[status(thm)],[c_7615,c_7596]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_8425,plain,
% 3.53/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.53/0.98      inference(demodulation,[status(thm)],[c_8395,c_7617]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_19,plain,
% 3.53/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.53/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1736,plain,
% 3.53/0.98      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 3.53/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2308,plain,
% 3.53/0.98      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1736]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_3269,plain,
% 3.53/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_1744,c_2308]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2306,plain,
% 3.53/0.98      ( r2_relset_1(X0_51,X1_51,X2_51,X2_51) = iProver_top
% 3.53/0.98      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1738]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4128,plain,
% 3.53/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_3269,c_2306]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(contradiction,plain,
% 3.53/0.98      ( $false ),
% 3.53/0.98      inference(minisat,[status(thm)],[c_8425,c_4128]) ).
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/0.98  
% 3.53/0.98  ------                               Statistics
% 3.53/0.98  
% 3.53/0.98  ------ General
% 3.53/0.98  
% 3.53/0.98  abstr_ref_over_cycles:                  0
% 3.53/0.98  abstr_ref_under_cycles:                 0
% 3.53/0.98  gc_basic_clause_elim:                   0
% 3.53/0.98  forced_gc_time:                         0
% 3.53/0.98  parsing_time:                           0.01
% 3.53/0.98  unif_index_cands_time:                  0.
% 3.53/0.98  unif_index_add_time:                    0.
% 3.53/0.98  orderings_time:                         0.
% 3.53/0.98  out_proof_time:                         0.018
% 3.53/0.98  total_time:                             0.424
% 3.53/0.98  num_of_symbols:                         57
% 3.53/0.98  num_of_terms:                           9352
% 3.53/0.98  
% 3.53/0.98  ------ Preprocessing
% 3.53/0.98  
% 3.53/0.98  num_of_splits:                          0
% 3.53/0.98  num_of_split_atoms:                     0
% 3.53/0.98  num_of_reused_defs:                     0
% 3.53/0.98  num_eq_ax_congr_red:                    15
% 3.53/0.98  num_of_sem_filtered_clauses:            1
% 3.53/0.98  num_of_subtypes:                        3
% 3.53/0.98  monotx_restored_types:                  1
% 3.53/0.98  sat_num_of_epr_types:                   0
% 3.53/0.98  sat_num_of_non_cyclic_types:            0
% 3.53/0.98  sat_guarded_non_collapsed_types:        1
% 3.53/0.98  num_pure_diseq_elim:                    0
% 3.53/0.98  simp_replaced_by:                       0
% 3.53/0.98  res_preprocessed:                       173
% 3.53/0.98  prep_upred:                             0
% 3.53/0.98  prep_unflattend:                        94
% 3.53/0.98  smt_new_axioms:                         0
% 3.53/0.98  pred_elim_cands:                        7
% 3.53/0.98  pred_elim:                              2
% 3.53/0.98  pred_elim_cl:                           0
% 3.53/0.98  pred_elim_cycles:                       9
% 3.53/0.98  merged_defs:                            0
% 3.53/0.98  merged_defs_ncl:                        0
% 3.53/0.98  bin_hyper_res:                          0
% 3.53/0.98  prep_cycles:                            4
% 3.53/0.98  pred_elim_time:                         0.041
% 3.53/0.98  splitting_time:                         0.
% 3.53/0.98  sem_filter_time:                        0.
% 3.53/0.98  monotx_time:                            0.002
% 3.53/0.98  subtype_inf_time:                       0.003
% 3.53/0.98  
% 3.53/0.98  ------ Problem properties
% 3.53/0.98  
% 3.53/0.98  clauses:                                33
% 3.53/0.98  conjectures:                            8
% 3.53/0.98  epr:                                    8
% 3.53/0.98  horn:                                   32
% 3.53/0.98  ground:                                 17
% 3.53/0.98  unary:                                  20
% 3.53/0.98  binary:                                 5
% 3.53/0.98  lits:                                   78
% 3.53/0.98  lits_eq:                                20
% 3.53/0.98  fd_pure:                                0
% 3.53/0.98  fd_pseudo:                              0
% 3.53/0.98  fd_cond:                                2
% 3.53/0.98  fd_pseudo_cond:                         4
% 3.53/0.98  ac_symbols:                             0
% 3.53/0.98  
% 3.53/0.98  ------ Propositional Solver
% 3.53/0.98  
% 3.53/0.98  prop_solver_calls:                      29
% 3.53/0.98  prop_fast_solver_calls:                 1537
% 3.53/0.98  smt_solver_calls:                       0
% 3.53/0.98  smt_fast_solver_calls:                  0
% 3.53/0.98  prop_num_of_clauses:                    3132
% 3.53/0.98  prop_preprocess_simplified:             9085
% 3.53/0.98  prop_fo_subsumed:                       65
% 3.53/0.98  prop_solver_time:                       0.
% 3.53/0.98  smt_solver_time:                        0.
% 3.53/0.98  smt_fast_solver_time:                   0.
% 3.53/0.98  prop_fast_solver_time:                  0.
% 3.53/0.98  prop_unsat_core_time:                   0.
% 3.53/0.98  
% 3.53/0.98  ------ QBF
% 3.53/0.98  
% 3.53/0.98  qbf_q_res:                              0
% 3.53/0.98  qbf_num_tautologies:                    0
% 3.53/0.98  qbf_prep_cycles:                        0
% 3.53/0.98  
% 3.53/0.98  ------ BMC1
% 3.53/0.98  
% 3.53/0.98  bmc1_current_bound:                     -1
% 3.53/0.98  bmc1_last_solved_bound:                 -1
% 3.53/0.98  bmc1_unsat_core_size:                   -1
% 3.53/0.98  bmc1_unsat_core_parents_size:           -1
% 3.53/0.98  bmc1_merge_next_fun:                    0
% 3.53/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.53/0.98  
% 3.53/0.98  ------ Instantiation
% 3.53/0.98  
% 3.53/0.98  inst_num_of_clauses:                    942
% 3.53/0.98  inst_num_in_passive:                    494
% 3.53/0.98  inst_num_in_active:                     406
% 3.53/0.98  inst_num_in_unprocessed:                42
% 3.53/0.98  inst_num_of_loops:                      450
% 3.53/0.98  inst_num_of_learning_restarts:          0
% 3.53/0.98  inst_num_moves_active_passive:          41
% 3.53/0.98  inst_lit_activity:                      0
% 3.53/0.98  inst_lit_activity_moves:                0
% 3.53/0.98  inst_num_tautologies:                   0
% 3.53/0.98  inst_num_prop_implied:                  0
% 3.53/0.98  inst_num_existing_simplified:           0
% 3.53/0.98  inst_num_eq_res_simplified:             0
% 3.53/0.98  inst_num_child_elim:                    0
% 3.53/0.98  inst_num_of_dismatching_blockings:      176
% 3.53/0.98  inst_num_of_non_proper_insts:           721
% 3.53/0.98  inst_num_of_duplicates:                 0
% 3.53/0.98  inst_inst_num_from_inst_to_res:         0
% 3.53/0.98  inst_dismatching_checking_time:         0.
% 3.53/0.98  
% 3.53/0.98  ------ Resolution
% 3.53/0.98  
% 3.53/0.98  res_num_of_clauses:                     0
% 3.53/0.98  res_num_in_passive:                     0
% 3.53/0.98  res_num_in_active:                      0
% 3.53/0.98  res_num_of_loops:                       177
% 3.53/0.98  res_forward_subset_subsumed:            71
% 3.53/0.98  res_backward_subset_subsumed:           0
% 3.53/0.98  res_forward_subsumed:                   0
% 3.53/0.98  res_backward_subsumed:                  0
% 3.53/0.98  res_forward_subsumption_resolution:     4
% 3.53/0.98  res_backward_subsumption_resolution:    0
% 3.53/0.98  res_clause_to_clause_subsumption:       237
% 3.53/0.98  res_orphan_elimination:                 0
% 3.53/0.98  res_tautology_del:                      37
% 3.53/0.98  res_num_eq_res_simplified:              0
% 3.53/0.98  res_num_sel_changes:                    0
% 3.53/0.98  res_moves_from_active_to_pass:          0
% 3.53/0.98  
% 3.53/0.98  ------ Superposition
% 3.53/0.98  
% 3.53/0.98  sup_time_total:                         0.
% 3.53/0.98  sup_time_generating:                    0.
% 3.53/0.98  sup_time_sim_full:                      0.
% 3.53/0.98  sup_time_sim_immed:                     0.
% 3.53/0.98  
% 3.53/0.98  sup_num_of_clauses:                     48
% 3.53/0.98  sup_num_in_active:                      44
% 3.53/0.98  sup_num_in_passive:                     4
% 3.53/0.98  sup_num_of_loops:                       88
% 3.53/0.98  sup_fw_superposition:                   60
% 3.53/0.98  sup_bw_superposition:                   14
% 3.53/0.98  sup_immediate_simplified:               59
% 3.53/0.98  sup_given_eliminated:                   0
% 3.53/0.98  comparisons_done:                       0
% 3.53/0.98  comparisons_avoided:                    3
% 3.53/0.98  
% 3.53/0.98  ------ Simplifications
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  sim_fw_subset_subsumed:                 10
% 3.53/0.98  sim_bw_subset_subsumed:                 7
% 3.53/0.98  sim_fw_subsumed:                        2
% 3.53/0.98  sim_bw_subsumed:                        0
% 3.53/0.98  sim_fw_subsumption_res:                 6
% 3.53/0.98  sim_bw_subsumption_res:                 0
% 3.53/0.98  sim_tautology_del:                      1
% 3.53/0.98  sim_eq_tautology_del:                   11
% 3.53/0.98  sim_eq_res_simp:                        5
% 3.53/0.98  sim_fw_demodulated:                     0
% 3.53/0.98  sim_bw_demodulated:                     66
% 3.53/0.98  sim_light_normalised:                   22
% 3.53/0.98  sim_joinable_taut:                      0
% 3.53/0.98  sim_joinable_simp:                      0
% 3.53/0.98  sim_ac_normalised:                      0
% 3.53/0.98  sim_smt_subsumption:                    0
% 3.53/0.98  
%------------------------------------------------------------------------------
