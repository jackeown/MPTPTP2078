%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:12 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
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
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
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
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
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

cnf(c_4001,plain,
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
    inference(superposition,[status(thm)],[c_4001,c_2319])).

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

cnf(c_7256,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5073,c_33,c_34,c_35,c_30,c_37,c_495,c_2581])).

cnf(c_7257,plain,
    ( k2_funct_1(sK1) = X0_51
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_7256])).

cnf(c_7268,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_7257])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7269,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7268])).

cnf(c_7459,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7268,c_38,c_39,c_41])).

cnf(c_7460,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7459])).

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

cnf(c_7463,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7460,c_2362])).

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

cnf(c_7466,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7463,c_41,c_2585])).

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

cnf(c_5204,plain,
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

cnf(c_5249,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5204,c_29,c_26,c_473,c_2576])).

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

cnf(c_5269,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5249,c_2298])).

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

cnf(c_5941,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5269,c_41,c_2551])).

cnf(c_5942,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5941])).

cnf(c_7474,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7466,c_5942])).

cnf(c_7568,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7474])).

cnf(c_1729,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2315,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1729])).

cnf(c_8543,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7568,c_2315])).

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
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1741,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | ~ v2_funct_1(X1_51)
    | ~ v1_relat_1(X1_51)
    | ~ v1_relat_1(X0_51)
    | k5_relat_1(X1_51,X0_51) != k6_partfun1(k1_relat_1(X1_51))
    | k2_funct_1(X1_51) = X0_51
    | k1_relat_1(X0_51) != k2_relat_1(X1_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2303,plain,
    ( k5_relat_1(X0_51,X1_51) != k6_partfun1(k1_relat_1(X0_51))
    | k2_funct_1(X0_51) = X1_51
    | k1_relat_1(X1_51) != k2_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1741])).

cnf(c_3878,plain,
    ( k6_partfun1(k1_relat_1(k6_partfun1(X0_51))) != k6_partfun1(X0_51)
    | k6_partfun1(k2_relat_1(k6_partfun1(X0_51))) = k2_funct_1(k6_partfun1(X0_51))
    | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
    | v2_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_relat_1(k6_partfun1(X0_51)) != iProver_top
    | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3171,c_2303])).

cnf(c_6,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1743,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1800,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1743])).

cnf(c_1801,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1742])).

cnf(c_6647,plain,
    ( k6_partfun1(k1_relat_1(k6_partfun1(X0_51))) != k6_partfun1(X0_51)
    | k6_partfun1(k2_relat_1(k6_partfun1(X0_51))) = k2_funct_1(k6_partfun1(X0_51))
    | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
    | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3878,c_1800,c_1801])).

cnf(c_6659,plain,
    ( k6_partfun1(k1_relat_1(k6_partfun1(X0_51))) != k6_partfun1(X0_51)
    | k6_partfun1(k2_relat_1(k6_partfun1(X0_51))) = k2_funct_1(k6_partfun1(X0_51))
    | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6647,c_2302])).

cnf(c_6663,plain,
    ( k6_partfun1(k1_relat_1(k6_partfun1(k1_xboole_0))) != k6_partfun1(k1_xboole_0)
    | k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0))) = k2_funct_1(k6_partfun1(k1_xboole_0))
    | k1_relat_1(k6_partfun1(k2_relat_1(k1_xboole_0))) != k2_relat_1(k6_partfun1(k1_xboole_0))
    | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0)))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_6659])).

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

cnf(c_6664,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6663,c_1744,c_1748,c_1749])).

cnf(c_6665,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6664])).

cnf(c_8549,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8543,c_6665])).

cnf(c_5205,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_2320])).

cnf(c_5281,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5205,c_33,c_30,c_495,c_2581])).

cnf(c_5301,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_2298])).

cnf(c_2553,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_2554,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2553])).

cnf(c_5946,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5301,c_37,c_2554])).

cnf(c_5947,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5946])).

cnf(c_7473,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7466,c_5947])).

cnf(c_7596,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7473])).

cnf(c_7489,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7466,c_2362])).

cnf(c_7577,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7568,c_7489])).

cnf(c_7598,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7596,c_7577])).

cnf(c_8580,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8549,c_7598])).

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

cnf(c_4108,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3269,c_2306])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8580,c_4108])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:53 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.08/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.00  
% 3.08/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.08/1.00  
% 3.08/1.00  ------  iProver source info
% 3.08/1.00  
% 3.08/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.08/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.08/1.00  git: non_committed_changes: false
% 3.08/1.00  git: last_make_outside_of_git: false
% 3.08/1.00  
% 3.08/1.00  ------ 
% 3.08/1.00  
% 3.08/1.00  ------ Input Options
% 3.08/1.00  
% 3.08/1.00  --out_options                           all
% 3.08/1.00  --tptp_safe_out                         true
% 3.08/1.00  --problem_path                          ""
% 3.08/1.00  --include_path                          ""
% 3.08/1.00  --clausifier                            res/vclausify_rel
% 3.08/1.00  --clausifier_options                    --mode clausify
% 3.08/1.00  --stdin                                 false
% 3.08/1.00  --stats_out                             all
% 3.08/1.00  
% 3.08/1.00  ------ General Options
% 3.08/1.00  
% 3.08/1.00  --fof                                   false
% 3.08/1.00  --time_out_real                         305.
% 3.08/1.00  --time_out_virtual                      -1.
% 3.08/1.00  --symbol_type_check                     false
% 3.08/1.00  --clausify_out                          false
% 3.08/1.00  --sig_cnt_out                           false
% 3.08/1.00  --trig_cnt_out                          false
% 3.08/1.00  --trig_cnt_out_tolerance                1.
% 3.08/1.00  --trig_cnt_out_sk_spl                   false
% 3.08/1.00  --abstr_cl_out                          false
% 3.08/1.00  
% 3.08/1.00  ------ Global Options
% 3.08/1.00  
% 3.08/1.00  --schedule                              default
% 3.08/1.00  --add_important_lit                     false
% 3.08/1.00  --prop_solver_per_cl                    1000
% 3.08/1.00  --min_unsat_core                        false
% 3.08/1.00  --soft_assumptions                      false
% 3.08/1.00  --soft_lemma_size                       3
% 3.08/1.00  --prop_impl_unit_size                   0
% 3.08/1.00  --prop_impl_unit                        []
% 3.08/1.00  --share_sel_clauses                     true
% 3.08/1.00  --reset_solvers                         false
% 3.08/1.00  --bc_imp_inh                            [conj_cone]
% 3.08/1.00  --conj_cone_tolerance                   3.
% 3.08/1.00  --extra_neg_conj                        none
% 3.08/1.00  --large_theory_mode                     true
% 3.08/1.00  --prolific_symb_bound                   200
% 3.08/1.00  --lt_threshold                          2000
% 3.08/1.00  --clause_weak_htbl                      true
% 3.08/1.00  --gc_record_bc_elim                     false
% 3.08/1.00  
% 3.08/1.00  ------ Preprocessing Options
% 3.08/1.00  
% 3.08/1.00  --preprocessing_flag                    true
% 3.08/1.00  --time_out_prep_mult                    0.1
% 3.08/1.00  --splitting_mode                        input
% 3.08/1.00  --splitting_grd                         true
% 3.08/1.00  --splitting_cvd                         false
% 3.08/1.00  --splitting_cvd_svl                     false
% 3.08/1.00  --splitting_nvd                         32
% 3.08/1.00  --sub_typing                            true
% 3.08/1.00  --prep_gs_sim                           true
% 3.08/1.00  --prep_unflatten                        true
% 3.08/1.00  --prep_res_sim                          true
% 3.08/1.00  --prep_upred                            true
% 3.08/1.00  --prep_sem_filter                       exhaustive
% 3.08/1.00  --prep_sem_filter_out                   false
% 3.08/1.00  --pred_elim                             true
% 3.08/1.00  --res_sim_input                         true
% 3.08/1.00  --eq_ax_congr_red                       true
% 3.08/1.00  --pure_diseq_elim                       true
% 3.08/1.00  --brand_transform                       false
% 3.08/1.00  --non_eq_to_eq                          false
% 3.08/1.00  --prep_def_merge                        true
% 3.08/1.00  --prep_def_merge_prop_impl              false
% 3.08/1.00  --prep_def_merge_mbd                    true
% 3.08/1.00  --prep_def_merge_tr_red                 false
% 3.08/1.00  --prep_def_merge_tr_cl                  false
% 3.08/1.00  --smt_preprocessing                     true
% 3.08/1.00  --smt_ac_axioms                         fast
% 3.08/1.00  --preprocessed_out                      false
% 3.08/1.00  --preprocessed_stats                    false
% 3.08/1.00  
% 3.08/1.00  ------ Abstraction refinement Options
% 3.08/1.00  
% 3.08/1.00  --abstr_ref                             []
% 3.08/1.00  --abstr_ref_prep                        false
% 3.08/1.00  --abstr_ref_until_sat                   false
% 3.08/1.00  --abstr_ref_sig_restrict                funpre
% 3.08/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/1.00  --abstr_ref_under                       []
% 3.08/1.00  
% 3.08/1.00  ------ SAT Options
% 3.08/1.00  
% 3.08/1.00  --sat_mode                              false
% 3.08/1.00  --sat_fm_restart_options                ""
% 3.08/1.00  --sat_gr_def                            false
% 3.08/1.00  --sat_epr_types                         true
% 3.08/1.00  --sat_non_cyclic_types                  false
% 3.08/1.00  --sat_finite_models                     false
% 3.08/1.00  --sat_fm_lemmas                         false
% 3.08/1.00  --sat_fm_prep                           false
% 3.08/1.00  --sat_fm_uc_incr                        true
% 3.08/1.00  --sat_out_model                         small
% 3.08/1.00  --sat_out_clauses                       false
% 3.08/1.00  
% 3.08/1.00  ------ QBF Options
% 3.08/1.00  
% 3.08/1.00  --qbf_mode                              false
% 3.08/1.00  --qbf_elim_univ                         false
% 3.08/1.00  --qbf_dom_inst                          none
% 3.08/1.00  --qbf_dom_pre_inst                      false
% 3.08/1.00  --qbf_sk_in                             false
% 3.08/1.00  --qbf_pred_elim                         true
% 3.08/1.00  --qbf_split                             512
% 3.08/1.00  
% 3.08/1.00  ------ BMC1 Options
% 3.08/1.00  
% 3.08/1.00  --bmc1_incremental                      false
% 3.08/1.00  --bmc1_axioms                           reachable_all
% 3.08/1.00  --bmc1_min_bound                        0
% 3.08/1.00  --bmc1_max_bound                        -1
% 3.08/1.00  --bmc1_max_bound_default                -1
% 3.08/1.00  --bmc1_symbol_reachability              true
% 3.08/1.00  --bmc1_property_lemmas                  false
% 3.08/1.00  --bmc1_k_induction                      false
% 3.08/1.00  --bmc1_non_equiv_states                 false
% 3.08/1.00  --bmc1_deadlock                         false
% 3.08/1.00  --bmc1_ucm                              false
% 3.08/1.00  --bmc1_add_unsat_core                   none
% 3.08/1.00  --bmc1_unsat_core_children              false
% 3.08/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/1.00  --bmc1_out_stat                         full
% 3.08/1.00  --bmc1_ground_init                      false
% 3.08/1.00  --bmc1_pre_inst_next_state              false
% 3.08/1.00  --bmc1_pre_inst_state                   false
% 3.08/1.00  --bmc1_pre_inst_reach_state             false
% 3.08/1.00  --bmc1_out_unsat_core                   false
% 3.08/1.00  --bmc1_aig_witness_out                  false
% 3.08/1.00  --bmc1_verbose                          false
% 3.08/1.00  --bmc1_dump_clauses_tptp                false
% 3.08/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.08/1.00  --bmc1_dump_file                        -
% 3.08/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.08/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.08/1.00  --bmc1_ucm_extend_mode                  1
% 3.08/1.00  --bmc1_ucm_init_mode                    2
% 3.08/1.00  --bmc1_ucm_cone_mode                    none
% 3.08/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.08/1.00  --bmc1_ucm_relax_model                  4
% 3.08/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.08/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/1.00  --bmc1_ucm_layered_model                none
% 3.08/1.00  --bmc1_ucm_max_lemma_size               10
% 3.08/1.00  
% 3.08/1.00  ------ AIG Options
% 3.08/1.00  
% 3.08/1.00  --aig_mode                              false
% 3.08/1.00  
% 3.08/1.00  ------ Instantiation Options
% 3.08/1.00  
% 3.08/1.00  --instantiation_flag                    true
% 3.08/1.00  --inst_sos_flag                         false
% 3.08/1.00  --inst_sos_phase                        true
% 3.08/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/1.00  --inst_lit_sel_side                     num_symb
% 3.08/1.00  --inst_solver_per_active                1400
% 3.08/1.00  --inst_solver_calls_frac                1.
% 3.08/1.00  --inst_passive_queue_type               priority_queues
% 3.08/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/1.00  --inst_passive_queues_freq              [25;2]
% 3.08/1.00  --inst_dismatching                      true
% 3.08/1.00  --inst_eager_unprocessed_to_passive     true
% 3.08/1.00  --inst_prop_sim_given                   true
% 3.08/1.00  --inst_prop_sim_new                     false
% 3.08/1.00  --inst_subs_new                         false
% 3.08/1.00  --inst_eq_res_simp                      false
% 3.08/1.00  --inst_subs_given                       false
% 3.08/1.00  --inst_orphan_elimination               true
% 3.08/1.00  --inst_learning_loop_flag               true
% 3.08/1.00  --inst_learning_start                   3000
% 3.08/1.00  --inst_learning_factor                  2
% 3.08/1.00  --inst_start_prop_sim_after_learn       3
% 3.08/1.00  --inst_sel_renew                        solver
% 3.08/1.00  --inst_lit_activity_flag                true
% 3.08/1.00  --inst_restr_to_given                   false
% 3.08/1.00  --inst_activity_threshold               500
% 3.08/1.00  --inst_out_proof                        true
% 3.08/1.00  
% 3.08/1.00  ------ Resolution Options
% 3.08/1.00  
% 3.08/1.00  --resolution_flag                       true
% 3.08/1.00  --res_lit_sel                           adaptive
% 3.08/1.00  --res_lit_sel_side                      none
% 3.08/1.00  --res_ordering                          kbo
% 3.08/1.00  --res_to_prop_solver                    active
% 3.08/1.00  --res_prop_simpl_new                    false
% 3.08/1.00  --res_prop_simpl_given                  true
% 3.08/1.00  --res_passive_queue_type                priority_queues
% 3.08/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/1.00  --res_passive_queues_freq               [15;5]
% 3.08/1.00  --res_forward_subs                      full
% 3.08/1.00  --res_backward_subs                     full
% 3.08/1.00  --res_forward_subs_resolution           true
% 3.08/1.00  --res_backward_subs_resolution          true
% 3.08/1.00  --res_orphan_elimination                true
% 3.08/1.00  --res_time_limit                        2.
% 3.08/1.00  --res_out_proof                         true
% 3.08/1.00  
% 3.08/1.00  ------ Superposition Options
% 3.08/1.00  
% 3.08/1.00  --superposition_flag                    true
% 3.08/1.00  --sup_passive_queue_type                priority_queues
% 3.08/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.08/1.00  --demod_completeness_check              fast
% 3.08/1.00  --demod_use_ground                      true
% 3.08/1.00  --sup_to_prop_solver                    passive
% 3.08/1.00  --sup_prop_simpl_new                    true
% 3.08/1.00  --sup_prop_simpl_given                  true
% 3.08/1.00  --sup_fun_splitting                     false
% 3.08/1.00  --sup_smt_interval                      50000
% 3.08/1.00  
% 3.08/1.00  ------ Superposition Simplification Setup
% 3.08/1.00  
% 3.08/1.00  --sup_indices_passive                   []
% 3.08/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.00  --sup_full_bw                           [BwDemod]
% 3.08/1.00  --sup_immed_triv                        [TrivRules]
% 3.08/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.00  --sup_immed_bw_main                     []
% 3.08/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.00  
% 3.08/1.00  ------ Combination Options
% 3.08/1.00  
% 3.08/1.00  --comb_res_mult                         3
% 3.08/1.00  --comb_sup_mult                         2
% 3.08/1.00  --comb_inst_mult                        10
% 3.08/1.00  
% 3.08/1.00  ------ Debug Options
% 3.08/1.00  
% 3.08/1.00  --dbg_backtrace                         false
% 3.08/1.00  --dbg_dump_prop_clauses                 false
% 3.08/1.00  --dbg_dump_prop_clauses_file            -
% 3.08/1.00  --dbg_out_stat                          false
% 3.08/1.00  ------ Parsing...
% 3.08/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.08/1.00  
% 3.08/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.08/1.00  
% 3.08/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.08/1.00  
% 3.08/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.08/1.00  ------ Proving...
% 3.08/1.00  ------ Problem Properties 
% 3.08/1.00  
% 3.08/1.00  
% 3.08/1.00  clauses                                 33
% 3.08/1.00  conjectures                             8
% 3.08/1.00  EPR                                     8
% 3.08/1.00  Horn                                    32
% 3.08/1.00  unary                                   20
% 3.08/1.00  binary                                  5
% 3.08/1.00  lits                                    78
% 3.08/1.00  lits eq                                 20
% 3.08/1.00  fd_pure                                 0
% 3.08/1.00  fd_pseudo                               0
% 3.08/1.00  fd_cond                                 2
% 3.08/1.00  fd_pseudo_cond                          4
% 3.08/1.00  AC symbols                              0
% 3.08/1.00  
% 3.08/1.00  ------ Schedule dynamic 5 is on 
% 3.08/1.00  
% 3.08/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.08/1.00  
% 3.08/1.00  
% 3.08/1.00  ------ 
% 3.08/1.00  Current options:
% 3.08/1.00  ------ 
% 3.08/1.00  
% 3.08/1.00  ------ Input Options
% 3.08/1.00  
% 3.08/1.00  --out_options                           all
% 3.08/1.00  --tptp_safe_out                         true
% 3.08/1.00  --problem_path                          ""
% 3.08/1.00  --include_path                          ""
% 3.08/1.00  --clausifier                            res/vclausify_rel
% 3.08/1.00  --clausifier_options                    --mode clausify
% 3.08/1.00  --stdin                                 false
% 3.08/1.00  --stats_out                             all
% 3.08/1.00  
% 3.08/1.00  ------ General Options
% 3.08/1.00  
% 3.08/1.00  --fof                                   false
% 3.08/1.00  --time_out_real                         305.
% 3.08/1.00  --time_out_virtual                      -1.
% 3.08/1.00  --symbol_type_check                     false
% 3.08/1.00  --clausify_out                          false
% 3.08/1.00  --sig_cnt_out                           false
% 3.08/1.00  --trig_cnt_out                          false
% 3.08/1.00  --trig_cnt_out_tolerance                1.
% 3.08/1.00  --trig_cnt_out_sk_spl                   false
% 3.08/1.00  --abstr_cl_out                          false
% 3.08/1.00  
% 3.08/1.00  ------ Global Options
% 3.08/1.00  
% 3.08/1.00  --schedule                              default
% 3.08/1.00  --add_important_lit                     false
% 3.08/1.00  --prop_solver_per_cl                    1000
% 3.08/1.00  --min_unsat_core                        false
% 3.08/1.00  --soft_assumptions                      false
% 3.08/1.00  --soft_lemma_size                       3
% 3.08/1.00  --prop_impl_unit_size                   0
% 3.08/1.00  --prop_impl_unit                        []
% 3.08/1.00  --share_sel_clauses                     true
% 3.08/1.00  --reset_solvers                         false
% 3.08/1.00  --bc_imp_inh                            [conj_cone]
% 3.08/1.00  --conj_cone_tolerance                   3.
% 3.08/1.00  --extra_neg_conj                        none
% 3.08/1.00  --large_theory_mode                     true
% 3.08/1.00  --prolific_symb_bound                   200
% 3.08/1.00  --lt_threshold                          2000
% 3.08/1.00  --clause_weak_htbl                      true
% 3.08/1.00  --gc_record_bc_elim                     false
% 3.08/1.00  
% 3.08/1.00  ------ Preprocessing Options
% 3.08/1.00  
% 3.08/1.00  --preprocessing_flag                    true
% 3.08/1.00  --time_out_prep_mult                    0.1
% 3.08/1.00  --splitting_mode                        input
% 3.08/1.00  --splitting_grd                         true
% 3.08/1.00  --splitting_cvd                         false
% 3.08/1.00  --splitting_cvd_svl                     false
% 3.08/1.00  --splitting_nvd                         32
% 3.08/1.00  --sub_typing                            true
% 3.08/1.00  --prep_gs_sim                           true
% 3.08/1.00  --prep_unflatten                        true
% 3.08/1.00  --prep_res_sim                          true
% 3.08/1.00  --prep_upred                            true
% 3.08/1.00  --prep_sem_filter                       exhaustive
% 3.08/1.00  --prep_sem_filter_out                   false
% 3.08/1.00  --pred_elim                             true
% 3.08/1.00  --res_sim_input                         true
% 3.08/1.00  --eq_ax_congr_red                       true
% 3.08/1.00  --pure_diseq_elim                       true
% 3.08/1.00  --brand_transform                       false
% 3.08/1.00  --non_eq_to_eq                          false
% 3.08/1.00  --prep_def_merge                        true
% 3.08/1.00  --prep_def_merge_prop_impl              false
% 3.08/1.00  --prep_def_merge_mbd                    true
% 3.08/1.00  --prep_def_merge_tr_red                 false
% 3.08/1.00  --prep_def_merge_tr_cl                  false
% 3.08/1.00  --smt_preprocessing                     true
% 3.08/1.00  --smt_ac_axioms                         fast
% 3.08/1.00  --preprocessed_out                      false
% 3.08/1.00  --preprocessed_stats                    false
% 3.08/1.00  
% 3.08/1.00  ------ Abstraction refinement Options
% 3.08/1.00  
% 3.08/1.00  --abstr_ref                             []
% 3.08/1.00  --abstr_ref_prep                        false
% 3.08/1.00  --abstr_ref_until_sat                   false
% 3.08/1.00  --abstr_ref_sig_restrict                funpre
% 3.08/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/1.00  --abstr_ref_under                       []
% 3.08/1.00  
% 3.08/1.00  ------ SAT Options
% 3.08/1.00  
% 3.08/1.00  --sat_mode                              false
% 3.08/1.00  --sat_fm_restart_options                ""
% 3.08/1.00  --sat_gr_def                            false
% 3.08/1.00  --sat_epr_types                         true
% 3.08/1.00  --sat_non_cyclic_types                  false
% 3.08/1.00  --sat_finite_models                     false
% 3.08/1.00  --sat_fm_lemmas                         false
% 3.08/1.00  --sat_fm_prep                           false
% 3.08/1.00  --sat_fm_uc_incr                        true
% 3.08/1.00  --sat_out_model                         small
% 3.08/1.00  --sat_out_clauses                       false
% 3.08/1.00  
% 3.08/1.00  ------ QBF Options
% 3.08/1.00  
% 3.08/1.00  --qbf_mode                              false
% 3.08/1.00  --qbf_elim_univ                         false
% 3.08/1.00  --qbf_dom_inst                          none
% 3.08/1.00  --qbf_dom_pre_inst                      false
% 3.08/1.00  --qbf_sk_in                             false
% 3.08/1.00  --qbf_pred_elim                         true
% 3.08/1.00  --qbf_split                             512
% 3.08/1.00  
% 3.08/1.00  ------ BMC1 Options
% 3.08/1.00  
% 3.08/1.00  --bmc1_incremental                      false
% 3.08/1.00  --bmc1_axioms                           reachable_all
% 3.08/1.00  --bmc1_min_bound                        0
% 3.08/1.00  --bmc1_max_bound                        -1
% 3.08/1.00  --bmc1_max_bound_default                -1
% 3.08/1.00  --bmc1_symbol_reachability              true
% 3.08/1.00  --bmc1_property_lemmas                  false
% 3.08/1.00  --bmc1_k_induction                      false
% 3.08/1.00  --bmc1_non_equiv_states                 false
% 3.08/1.00  --bmc1_deadlock                         false
% 3.08/1.00  --bmc1_ucm                              false
% 3.08/1.00  --bmc1_add_unsat_core                   none
% 3.08/1.00  --bmc1_unsat_core_children              false
% 3.08/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/1.00  --bmc1_out_stat                         full
% 3.08/1.00  --bmc1_ground_init                      false
% 3.08/1.00  --bmc1_pre_inst_next_state              false
% 3.08/1.00  --bmc1_pre_inst_state                   false
% 3.08/1.00  --bmc1_pre_inst_reach_state             false
% 3.08/1.00  --bmc1_out_unsat_core                   false
% 3.08/1.00  --bmc1_aig_witness_out                  false
% 3.08/1.00  --bmc1_verbose                          false
% 3.08/1.00  --bmc1_dump_clauses_tptp                false
% 3.08/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.08/1.00  --bmc1_dump_file                        -
% 3.08/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.08/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.08/1.00  --bmc1_ucm_extend_mode                  1
% 3.08/1.00  --bmc1_ucm_init_mode                    2
% 3.08/1.00  --bmc1_ucm_cone_mode                    none
% 3.08/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.08/1.00  --bmc1_ucm_relax_model                  4
% 3.08/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.08/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/1.00  --bmc1_ucm_layered_model                none
% 3.08/1.00  --bmc1_ucm_max_lemma_size               10
% 3.08/1.00  
% 3.08/1.00  ------ AIG Options
% 3.08/1.00  
% 3.08/1.00  --aig_mode                              false
% 3.08/1.00  
% 3.08/1.00  ------ Instantiation Options
% 3.08/1.00  
% 3.08/1.00  --instantiation_flag                    true
% 3.08/1.00  --inst_sos_flag                         false
% 3.08/1.00  --inst_sos_phase                        true
% 3.08/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/1.00  --inst_lit_sel_side                     none
% 3.08/1.00  --inst_solver_per_active                1400
% 3.08/1.00  --inst_solver_calls_frac                1.
% 3.08/1.00  --inst_passive_queue_type               priority_queues
% 3.08/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/1.00  --inst_passive_queues_freq              [25;2]
% 3.08/1.00  --inst_dismatching                      true
% 3.08/1.00  --inst_eager_unprocessed_to_passive     true
% 3.08/1.00  --inst_prop_sim_given                   true
% 3.08/1.00  --inst_prop_sim_new                     false
% 3.08/1.00  --inst_subs_new                         false
% 3.08/1.00  --inst_eq_res_simp                      false
% 3.08/1.00  --inst_subs_given                       false
% 3.08/1.00  --inst_orphan_elimination               true
% 3.08/1.00  --inst_learning_loop_flag               true
% 3.08/1.00  --inst_learning_start                   3000
% 3.08/1.00  --inst_learning_factor                  2
% 3.08/1.00  --inst_start_prop_sim_after_learn       3
% 3.08/1.00  --inst_sel_renew                        solver
% 3.08/1.00  --inst_lit_activity_flag                true
% 3.08/1.00  --inst_restr_to_given                   false
% 3.08/1.00  --inst_activity_threshold               500
% 3.08/1.00  --inst_out_proof                        true
% 3.08/1.00  
% 3.08/1.00  ------ Resolution Options
% 3.08/1.00  
% 3.08/1.00  --resolution_flag                       false
% 3.08/1.00  --res_lit_sel                           adaptive
% 3.08/1.00  --res_lit_sel_side                      none
% 3.08/1.00  --res_ordering                          kbo
% 3.08/1.00  --res_to_prop_solver                    active
% 3.08/1.00  --res_prop_simpl_new                    false
% 3.08/1.00  --res_prop_simpl_given                  true
% 3.08/1.00  --res_passive_queue_type                priority_queues
% 3.08/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/1.00  --res_passive_queues_freq               [15;5]
% 3.08/1.00  --res_forward_subs                      full
% 3.08/1.00  --res_backward_subs                     full
% 3.08/1.00  --res_forward_subs_resolution           true
% 3.08/1.00  --res_backward_subs_resolution          true
% 3.08/1.00  --res_orphan_elimination                true
% 3.08/1.00  --res_time_limit                        2.
% 3.08/1.00  --res_out_proof                         true
% 3.08/1.00  
% 3.08/1.00  ------ Superposition Options
% 3.08/1.00  
% 3.08/1.00  --superposition_flag                    true
% 3.08/1.00  --sup_passive_queue_type                priority_queues
% 3.08/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.08/1.00  --demod_completeness_check              fast
% 3.08/1.00  --demod_use_ground                      true
% 3.08/1.00  --sup_to_prop_solver                    passive
% 3.08/1.00  --sup_prop_simpl_new                    true
% 3.08/1.00  --sup_prop_simpl_given                  true
% 3.08/1.00  --sup_fun_splitting                     false
% 3.08/1.00  --sup_smt_interval                      50000
% 3.08/1.00  
% 3.08/1.00  ------ Superposition Simplification Setup
% 3.08/1.00  
% 3.08/1.00  --sup_indices_passive                   []
% 3.08/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.00  --sup_full_bw                           [BwDemod]
% 3.08/1.00  --sup_immed_triv                        [TrivRules]
% 3.08/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.00  --sup_immed_bw_main                     []
% 3.08/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.00  
% 3.08/1.00  ------ Combination Options
% 3.08/1.00  
% 3.08/1.00  --comb_res_mult                         3
% 3.08/1.00  --comb_sup_mult                         2
% 3.08/1.00  --comb_inst_mult                        10
% 3.08/1.00  
% 3.08/1.00  ------ Debug Options
% 3.08/1.00  
% 3.08/1.00  --dbg_backtrace                         false
% 3.08/1.00  --dbg_dump_prop_clauses                 false
% 3.08/1.00  --dbg_dump_prop_clauses_file            -
% 3.08/1.00  --dbg_out_stat                          false
% 3.08/1.00  
% 3.08/1.00  
% 3.08/1.00  
% 3.08/1.00  
% 3.08/1.00  ------ Proving...
% 3.08/1.00  
% 3.08/1.00  
% 3.08/1.00  % SZS status Theorem for theBenchmark.p
% 3.08/1.00  
% 3.08/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.08/1.00  
% 3.08/1.00  fof(f18,conjecture,(
% 3.08/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f19,negated_conjecture,(
% 3.08/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.08/1.00    inference(negated_conjecture,[],[f18])).
% 3.08/1.00  
% 3.08/1.00  fof(f42,plain,(
% 3.08/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.08/1.00    inference(ennf_transformation,[],[f19])).
% 3.08/1.00  
% 3.08/1.00  fof(f43,plain,(
% 3.08/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.08/1.00    inference(flattening,[],[f42])).
% 3.08/1.00  
% 3.08/1.00  fof(f47,plain,(
% 3.08/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.08/1.00    introduced(choice_axiom,[])).
% 3.08/1.00  
% 3.08/1.00  fof(f46,plain,(
% 3.08/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.08/1.00    introduced(choice_axiom,[])).
% 3.08/1.00  
% 3.08/1.00  fof(f48,plain,(
% 3.08/1.00    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.08/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f47,f46])).
% 3.08/1.00  
% 3.08/1.00  fof(f82,plain,(
% 3.08/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f77,plain,(
% 3.08/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f9,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f29,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(ennf_transformation,[],[f9])).
% 3.08/1.00  
% 3.08/1.00  fof(f60,plain,(
% 3.08/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f29])).
% 3.08/1.00  
% 3.08/1.00  fof(f17,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f40,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.08/1.00    inference(ennf_transformation,[],[f17])).
% 3.08/1.00  
% 3.08/1.00  fof(f41,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.08/1.00    inference(flattening,[],[f40])).
% 3.08/1.00  
% 3.08/1.00  fof(f73,plain,(
% 3.08/1.00    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f41])).
% 3.08/1.00  
% 3.08/1.00  fof(f16,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f38,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.08/1.00    inference(ennf_transformation,[],[f16])).
% 3.08/1.00  
% 3.08/1.00  fof(f39,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.08/1.00    inference(flattening,[],[f38])).
% 3.08/1.00  
% 3.08/1.00  fof(f71,plain,(
% 3.08/1.00    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f39])).
% 3.08/1.00  
% 3.08/1.00  fof(f74,plain,(
% 3.08/1.00    v1_funct_1(sK1)),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f75,plain,(
% 3.08/1.00    v1_funct_2(sK1,sK0,sK0)),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f11,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f32,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(ennf_transformation,[],[f11])).
% 3.08/1.00  
% 3.08/1.00  fof(f33,plain,(
% 3.08/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(flattening,[],[f32])).
% 3.08/1.00  
% 3.08/1.00  fof(f65,plain,(
% 3.08/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f33])).
% 3.08/1.00  
% 3.08/1.00  fof(f76,plain,(
% 3.08/1.00    v3_funct_2(sK1,sK0,sK0)),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f8,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f21,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.08/1.00    inference(pure_predicate_removal,[],[f8])).
% 3.08/1.00  
% 3.08/1.00  fof(f28,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(ennf_transformation,[],[f21])).
% 3.08/1.00  
% 3.08/1.00  fof(f59,plain,(
% 3.08/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f28])).
% 3.08/1.00  
% 3.08/1.00  fof(f12,axiom,(
% 3.08/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f34,plain,(
% 3.08/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.08/1.00    inference(ennf_transformation,[],[f12])).
% 3.08/1.00  
% 3.08/1.00  fof(f35,plain,(
% 3.08/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.08/1.00    inference(flattening,[],[f34])).
% 3.08/1.00  
% 3.08/1.00  fof(f45,plain,(
% 3.08/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.08/1.00    inference(nnf_transformation,[],[f35])).
% 3.08/1.00  
% 3.08/1.00  fof(f66,plain,(
% 3.08/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f45])).
% 3.08/1.00  
% 3.08/1.00  fof(f7,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f27,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(ennf_transformation,[],[f7])).
% 3.08/1.00  
% 3.08/1.00  fof(f58,plain,(
% 3.08/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f27])).
% 3.08/1.00  
% 3.08/1.00  fof(f78,plain,(
% 3.08/1.00    v1_funct_1(sK2)),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f79,plain,(
% 3.08/1.00    v1_funct_2(sK2,sK0,sK0)),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f81,plain,(
% 3.08/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f83,plain,(
% 3.08/1.00    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f14,axiom,(
% 3.08/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f36,plain,(
% 3.08/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.08/1.00    inference(ennf_transformation,[],[f14])).
% 3.08/1.00  
% 3.08/1.00  fof(f37,plain,(
% 3.08/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.08/1.00    inference(flattening,[],[f36])).
% 3.08/1.00  
% 3.08/1.00  fof(f69,plain,(
% 3.08/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f37])).
% 3.08/1.00  
% 3.08/1.00  fof(f10,axiom,(
% 3.08/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f30,plain,(
% 3.08/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.08/1.00    inference(ennf_transformation,[],[f10])).
% 3.08/1.00  
% 3.08/1.00  fof(f31,plain,(
% 3.08/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(flattening,[],[f30])).
% 3.08/1.00  
% 3.08/1.00  fof(f44,plain,(
% 3.08/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(nnf_transformation,[],[f31])).
% 3.08/1.00  
% 3.08/1.00  fof(f62,plain,(
% 3.08/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f44])).
% 3.08/1.00  
% 3.08/1.00  fof(f89,plain,(
% 3.08/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(equality_resolution,[],[f62])).
% 3.08/1.00  
% 3.08/1.00  fof(f80,plain,(
% 3.08/1.00    v3_funct_2(sK2,sK0,sK0)),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f2,axiom,(
% 3.08/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f22,plain,(
% 3.08/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.08/1.00    inference(ennf_transformation,[],[f2])).
% 3.08/1.00  
% 3.08/1.00  fof(f23,plain,(
% 3.08/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.08/1.00    inference(flattening,[],[f22])).
% 3.08/1.00  
% 3.08/1.00  fof(f52,plain,(
% 3.08/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f23])).
% 3.08/1.00  
% 3.08/1.00  fof(f4,axiom,(
% 3.08/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f54,plain,(
% 3.08/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.08/1.00    inference(cnf_transformation,[],[f4])).
% 3.08/1.00  
% 3.08/1.00  fof(f15,axiom,(
% 3.08/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f70,plain,(
% 3.08/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f15])).
% 3.08/1.00  
% 3.08/1.00  fof(f85,plain,(
% 3.08/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.08/1.00    inference(definition_unfolding,[],[f54,f70])).
% 3.08/1.00  
% 3.08/1.00  fof(f5,axiom,(
% 3.08/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f55,plain,(
% 3.08/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f5])).
% 3.08/1.00  
% 3.08/1.00  fof(f87,plain,(
% 3.08/1.00    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.08/1.00    inference(definition_unfolding,[],[f55,f70])).
% 3.08/1.00  
% 3.08/1.00  fof(f3,axiom,(
% 3.08/1.00    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f24,plain,(
% 3.08/1.00    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.08/1.00    inference(ennf_transformation,[],[f3])).
% 3.08/1.00  
% 3.08/1.00  fof(f53,plain,(
% 3.08/1.00    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f24])).
% 3.08/1.00  
% 3.08/1.00  fof(f84,plain,(
% 3.08/1.00    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.08/1.00    inference(definition_unfolding,[],[f53,f70])).
% 3.08/1.00  
% 3.08/1.00  fof(f6,axiom,(
% 3.08/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f25,plain,(
% 3.08/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.08/1.00    inference(ennf_transformation,[],[f6])).
% 3.08/1.00  
% 3.08/1.00  fof(f26,plain,(
% 3.08/1.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.08/1.00    inference(flattening,[],[f25])).
% 3.08/1.00  
% 3.08/1.00  fof(f57,plain,(
% 3.08/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f26])).
% 3.08/1.00  
% 3.08/1.00  fof(f88,plain,(
% 3.08/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.00    inference(definition_unfolding,[],[f57,f70])).
% 3.08/1.00  
% 3.08/1.00  fof(f56,plain,(
% 3.08/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f5])).
% 3.08/1.00  
% 3.08/1.00  fof(f86,plain,(
% 3.08/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.08/1.00    inference(definition_unfolding,[],[f56,f70])).
% 3.08/1.00  
% 3.08/1.00  fof(f1,axiom,(
% 3.08/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f49,plain,(
% 3.08/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.08/1.00    inference(cnf_transformation,[],[f1])).
% 3.08/1.00  
% 3.08/1.00  fof(f50,plain,(
% 3.08/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.08/1.00    inference(cnf_transformation,[],[f1])).
% 3.08/1.00  
% 3.08/1.00  fof(f13,axiom,(
% 3.08/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f20,plain,(
% 3.08/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.08/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.08/1.00  
% 3.08/1.00  fof(f68,plain,(
% 3.08/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f20])).
% 3.08/1.00  
% 3.08/1.00  cnf(c_25,negated_conjecture,
% 3.08/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.08/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1732,negated_conjecture,
% 3.08/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2312,plain,
% 3.08/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1732]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_30,negated_conjecture,
% 3.08/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1728,negated_conjecture,
% 3.08/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2316,plain,
% 3.08/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1728]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_11,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1739,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 3.08/1.00      | k2_relset_1(X1_51,X2_51,X0_51) = k2_relat_1(X0_51) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2305,plain,
% 3.08/1.00      ( k2_relset_1(X0_51,X1_51,X2_51) = k2_relat_1(X2_51)
% 3.08/1.00      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1739]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4001,plain,
% 3.08/1.00      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_2316,c_2305]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_23,plain,
% 3.08/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.08/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.08/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.08/1.00      | ~ v1_funct_1(X2)
% 3.08/1.00      | ~ v1_funct_1(X3)
% 3.08/1.00      | ~ v2_funct_1(X2)
% 3.08/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.08/1.00      | k2_funct_1(X2) = X3
% 3.08/1.00      | k1_xboole_0 = X0
% 3.08/1.00      | k1_xboole_0 = X1 ),
% 3.08/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_22,plain,
% 3.08/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.08/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.08/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.08/1.00      | ~ v1_funct_1(X2)
% 3.08/1.00      | ~ v1_funct_1(X3)
% 3.08/1.00      | v2_funct_1(X2) ),
% 3.08/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_178,plain,
% 3.08/1.00      ( ~ v1_funct_1(X3)
% 3.08/1.00      | ~ v1_funct_1(X2)
% 3.08/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.08/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.08/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.08/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.08/1.00      | k2_funct_1(X2) = X3
% 3.08/1.00      | k1_xboole_0 = X0
% 3.08/1.00      | k1_xboole_0 = X1 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_23,c_22]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_179,plain,
% 3.08/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.08/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.08/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.08/1.00      | ~ v1_funct_1(X2)
% 3.08/1.00      | ~ v1_funct_1(X3)
% 3.08/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.08/1.00      | k2_funct_1(X2) = X3
% 3.08/1.00      | k1_xboole_0 = X0
% 3.08/1.00      | k1_xboole_0 = X1 ),
% 3.08/1.00      inference(renaming,[status(thm)],[c_178]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1725,plain,
% 3.08/1.00      ( ~ r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51))
% 3.08/1.00      | ~ v1_funct_2(X3_51,X1_51,X0_51)
% 3.08/1.00      | ~ v1_funct_2(X2_51,X0_51,X1_51)
% 3.08/1.00      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.08/1.00      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 3.08/1.00      | ~ v1_funct_1(X2_51)
% 3.08/1.00      | ~ v1_funct_1(X3_51)
% 3.08/1.00      | k2_relset_1(X0_51,X1_51,X2_51) != X1_51
% 3.08/1.00      | k2_funct_1(X2_51) = X3_51
% 3.08/1.00      | k1_xboole_0 = X0_51
% 3.08/1.00      | k1_xboole_0 = X1_51 ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_179]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2319,plain,
% 3.08/1.00      ( k2_relset_1(X0_51,X1_51,X2_51) != X1_51
% 3.08/1.00      | k2_funct_1(X2_51) = X3_51
% 3.08/1.00      | k1_xboole_0 = X0_51
% 3.08/1.00      | k1_xboole_0 = X1_51
% 3.08/1.00      | r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51)) != iProver_top
% 3.08/1.00      | v1_funct_2(X3_51,X1_51,X0_51) != iProver_top
% 3.08/1.00      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 3.08/1.00      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.08/1.00      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
% 3.08/1.00      | v1_funct_1(X2_51) != iProver_top
% 3.08/1.00      | v1_funct_1(X3_51) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1725]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5073,plain,
% 3.08/1.00      ( k2_funct_1(sK1) = X0_51
% 3.08/1.00      | k2_relat_1(sK1) != sK0
% 3.08/1.00      | sK0 = k1_xboole_0
% 3.08/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.08/1.00      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.08/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.08/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.08/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.08/1.00      | v1_funct_1(X0_51) != iProver_top
% 3.08/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_4001,c_2319]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_33,negated_conjecture,
% 3.08/1.00      ( v1_funct_1(sK1) ),
% 3.08/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_34,plain,
% 3.08/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_32,negated_conjecture,
% 3.08/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_35,plain,
% 3.08/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_37,plain,
% 3.08/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_14,plain,
% 3.08/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.08/1.00      | v2_funct_2(X0,X2)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.00      | ~ v1_funct_1(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_31,negated_conjecture,
% 3.08/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_494,plain,
% 3.08/1.00      ( v2_funct_2(X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.08/1.00      | ~ v1_funct_1(X0)
% 3.08/1.00      | sK1 != X0
% 3.08/1.00      | sK0 != X1
% 3.08/1.00      | sK0 != X2 ),
% 3.08/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_495,plain,
% 3.08/1.00      ( v2_funct_2(sK1,sK0)
% 3.08/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.08/1.00      | ~ v1_funct_1(sK1) ),
% 3.08/1.00      inference(unflattening,[status(thm)],[c_494]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_10,plain,
% 3.08/1.00      ( v5_relat_1(X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_18,plain,
% 3.08/1.00      ( ~ v2_funct_2(X0,X1)
% 3.08/1.00      | ~ v5_relat_1(X0,X1)
% 3.08/1.00      | ~ v1_relat_1(X0)
% 3.08/1.00      | k2_relat_1(X0) = X1 ),
% 3.08/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_348,plain,
% 3.08/1.00      ( ~ v2_funct_2(X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.08/1.00      | ~ v1_relat_1(X0)
% 3.08/1.00      | k2_relat_1(X0) = X1 ),
% 3.08/1.00      inference(resolution,[status(thm)],[c_10,c_18]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_9,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.00      | v1_relat_1(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_360,plain,
% 3.08/1.00      ( ~ v2_funct_2(X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.08/1.00      | k2_relat_1(X0) = X1 ),
% 3.08/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_348,c_9]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1724,plain,
% 3.08/1.00      ( ~ v2_funct_2(X0_51,X1_51)
% 3.08/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 3.08/1.00      | k2_relat_1(X0_51) = X1_51 ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_360]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2579,plain,
% 3.08/1.00      ( ~ v2_funct_2(sK1,sK0)
% 3.08/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 3.08/1.00      | k2_relat_1(sK1) = sK0 ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_1724]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2581,plain,
% 3.08/1.00      ( ~ v2_funct_2(sK1,sK0)
% 3.08/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.08/1.00      | k2_relat_1(sK1) = sK0 ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_2579]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7256,plain,
% 3.08/1.00      ( v1_funct_1(X0_51) != iProver_top
% 3.08/1.00      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.08/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.08/1.00      | sK0 = k1_xboole_0
% 3.08/1.00      | k2_funct_1(sK1) = X0_51
% 3.08/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_5073,c_33,c_34,c_35,c_30,c_37,c_495,c_2581]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7257,plain,
% 3.08/1.00      ( k2_funct_1(sK1) = X0_51
% 3.08/1.00      | sK0 = k1_xboole_0
% 3.08/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 3.08/1.00      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 3.08/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.08/1.00      | v1_funct_1(X0_51) != iProver_top ),
% 3.08/1.00      inference(renaming,[status(thm)],[c_7256]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7268,plain,
% 3.08/1.00      ( k2_funct_1(sK1) = sK2
% 3.08/1.00      | sK0 = k1_xboole_0
% 3.08/1.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.08/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.08/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_2312,c_7257]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_29,negated_conjecture,
% 3.08/1.00      ( v1_funct_1(sK2) ),
% 3.08/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_28,negated_conjecture,
% 3.08/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_26,negated_conjecture,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7269,plain,
% 3.08/1.00      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.08/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.08/1.00      | ~ v1_funct_1(sK2)
% 3.08/1.00      | k2_funct_1(sK1) = sK2
% 3.08/1.00      | sK0 = k1_xboole_0 ),
% 3.08/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7268]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7459,plain,
% 3.08/1.00      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_7268,c_38,c_39,c_41]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7460,plain,
% 3.08/1.00      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.08/1.00      inference(renaming,[status(thm)],[c_7459]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_24,negated_conjecture,
% 3.08/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.08/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1733,negated_conjecture,
% 3.08/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2311,plain,
% 3.08/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1733]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_20,plain,
% 3.08/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.08/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.08/1.00      | ~ v1_funct_1(X0)
% 3.08/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_513,plain,
% 3.08/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.08/1.00      | ~ v1_funct_1(X0)
% 3.08/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.08/1.00      | sK1 != X0
% 3.08/1.00      | sK0 != X1 ),
% 3.08/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_514,plain,
% 3.08/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.08/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.08/1.00      | ~ v1_funct_1(sK1)
% 3.08/1.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.08/1.00      inference(unflattening,[status(thm)],[c_513]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_516,plain,
% 3.08/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_514,c_33,c_32,c_30]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1717,plain,
% 3.08/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_516]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2362,plain,
% 3.08/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.08/1.00      inference(light_normalisation,[status(thm)],[c_2311,c_1717]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7463,plain,
% 3.08/1.00      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_7460,c_2362]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_41,plain,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_12,plain,
% 3.08/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1738,plain,
% 3.08/1.00      ( r2_relset_1(X0_51,X1_51,X2_51,X2_51)
% 3.08/1.00      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2584,plain,
% 3.08/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.08/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_1738]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2585,plain,
% 3.08/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.08/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2584]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7466,plain,
% 3.08/1.00      ( sK0 = k1_xboole_0 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_7463,c_41,c_2585]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1731,negated_conjecture,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2313,plain,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1731]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2320,plain,
% 3.08/1.00      ( k2_relat_1(X0_51) = X1_51
% 3.08/1.00      | v2_funct_2(X0_51,X1_51) != iProver_top
% 3.08/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51))) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1724]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5204,plain,
% 3.08/1.00      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_2313,c_2320]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_27,negated_conjecture,
% 3.08/1.00      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_472,plain,
% 3.08/1.00      ( v2_funct_2(X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.08/1.00      | ~ v1_funct_1(X0)
% 3.08/1.00      | sK2 != X0
% 3.08/1.00      | sK0 != X1
% 3.08/1.00      | sK0 != X2 ),
% 3.08/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_473,plain,
% 3.08/1.00      ( v2_funct_2(sK2,sK0)
% 3.08/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.08/1.00      | ~ v1_funct_1(sK2) ),
% 3.08/1.00      inference(unflattening,[status(thm)],[c_472]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2574,plain,
% 3.08/1.00      ( ~ v2_funct_2(sK2,sK0)
% 3.08/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 3.08/1.00      | k2_relat_1(sK2) = sK0 ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_1724]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2576,plain,
% 3.08/1.00      ( ~ v2_funct_2(sK2,sK0)
% 3.08/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.08/1.00      | k2_relat_1(sK2) = sK0 ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_2574]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5249,plain,
% 3.08/1.00      ( k2_relat_1(sK2) = sK0 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_5204,c_29,c_26,c_473,c_2576]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2,plain,
% 3.08/1.00      ( ~ v1_relat_1(X0)
% 3.08/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.08/1.00      | k1_xboole_0 = X0 ),
% 3.08/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1747,plain,
% 3.08/1.00      ( ~ v1_relat_1(X0_51)
% 3.08/1.00      | k2_relat_1(X0_51) != k1_xboole_0
% 3.08/1.00      | k1_xboole_0 = X0_51 ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2298,plain,
% 3.08/1.00      ( k2_relat_1(X0_51) != k1_xboole_0
% 3.08/1.00      | k1_xboole_0 = X0_51
% 3.08/1.00      | v1_relat_1(X0_51) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1747]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5269,plain,
% 3.08/1.00      ( sK2 = k1_xboole_0
% 3.08/1.00      | sK0 != k1_xboole_0
% 3.08/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_5249,c_2298]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1740,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 3.08/1.00      | v1_relat_1(X0_51) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2550,plain,
% 3.08/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.08/1.00      | v1_relat_1(sK2) ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_1740]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2551,plain,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.08/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2550]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5941,plain,
% 3.08/1.00      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_5269,c_41,c_2551]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5942,plain,
% 3.08/1.00      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.08/1.00      inference(renaming,[status(thm)],[c_5941]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7474,plain,
% 3.08/1.00      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_7466,c_5942]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7568,plain,
% 3.08/1.00      ( sK2 = k1_xboole_0 ),
% 3.08/1.00      inference(equality_resolution_simp,[status(thm)],[c_7474]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1729,negated_conjecture,
% 3.08/1.00      ( v1_funct_1(sK2) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_29]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2315,plain,
% 3.08/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1729]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_8543,plain,
% 3.08/1.00      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_7568,c_2315]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5,plain,
% 3.08/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1744,plain,
% 3.08/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7,plain,
% 3.08/1.00      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.08/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1742,plain,
% 3.08/1.00      ( v1_relat_1(k6_partfun1(X0_51)) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2302,plain,
% 3.08/1.00      ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1742]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4,plain,
% 3.08/1.00      ( ~ v1_relat_1(X0)
% 3.08/1.00      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 3.08/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1745,plain,
% 3.08/1.00      ( ~ v1_relat_1(X0_51)
% 3.08/1.00      | k5_relat_1(X0_51,k6_partfun1(k2_relat_1(X0_51))) = X0_51 ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2300,plain,
% 3.08/1.00      ( k5_relat_1(X0_51,k6_partfun1(k2_relat_1(X0_51))) = X0_51
% 3.08/1.00      | v1_relat_1(X0_51) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1745]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_3171,plain,
% 3.08/1.00      ( k5_relat_1(k6_partfun1(X0_51),k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) = k6_partfun1(X0_51) ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_2302,c_2300]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_8,plain,
% 3.08/1.00      ( ~ v1_funct_1(X0)
% 3.08/1.00      | ~ v1_funct_1(X1)
% 3.08/1.00      | ~ v2_funct_1(X1)
% 3.08/1.00      | ~ v1_relat_1(X1)
% 3.08/1.00      | ~ v1_relat_1(X0)
% 3.08/1.00      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.08/1.00      | k2_funct_1(X1) = X0
% 3.08/1.00      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.08/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1741,plain,
% 3.08/1.00      ( ~ v1_funct_1(X0_51)
% 3.08/1.00      | ~ v1_funct_1(X1_51)
% 3.08/1.00      | ~ v2_funct_1(X1_51)
% 3.08/1.00      | ~ v1_relat_1(X1_51)
% 3.08/1.00      | ~ v1_relat_1(X0_51)
% 3.08/1.00      | k5_relat_1(X1_51,X0_51) != k6_partfun1(k1_relat_1(X1_51))
% 3.08/1.00      | k2_funct_1(X1_51) = X0_51
% 3.08/1.00      | k1_relat_1(X0_51) != k2_relat_1(X1_51) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2303,plain,
% 3.08/1.00      ( k5_relat_1(X0_51,X1_51) != k6_partfun1(k1_relat_1(X0_51))
% 3.08/1.00      | k2_funct_1(X0_51) = X1_51
% 3.08/1.00      | k1_relat_1(X1_51) != k2_relat_1(X0_51)
% 3.08/1.00      | v1_funct_1(X0_51) != iProver_top
% 3.08/1.00      | v1_funct_1(X1_51) != iProver_top
% 3.08/1.00      | v2_funct_1(X0_51) != iProver_top
% 3.08/1.00      | v1_relat_1(X1_51) != iProver_top
% 3.08/1.00      | v1_relat_1(X0_51) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1741]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_3878,plain,
% 3.08/1.00      ( k6_partfun1(k1_relat_1(k6_partfun1(X0_51))) != k6_partfun1(X0_51)
% 3.08/1.00      | k6_partfun1(k2_relat_1(k6_partfun1(X0_51))) = k2_funct_1(k6_partfun1(X0_51))
% 3.08/1.00      | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
% 3.08/1.00      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.08/1.00      | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
% 3.08/1.00      | v2_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.08/1.00      | v1_relat_1(k6_partfun1(X0_51)) != iProver_top
% 3.08/1.00      | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_3171,c_2303]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6,plain,
% 3.08/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.08/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1743,plain,
% 3.08/1.00      ( v2_funct_1(k6_partfun1(X0_51)) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1800,plain,
% 3.08/1.00      ( v2_funct_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1743]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1801,plain,
% 3.08/1.00      ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1742]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6647,plain,
% 3.08/1.00      ( k6_partfun1(k1_relat_1(k6_partfun1(X0_51))) != k6_partfun1(X0_51)
% 3.08/1.00      | k6_partfun1(k2_relat_1(k6_partfun1(X0_51))) = k2_funct_1(k6_partfun1(X0_51))
% 3.08/1.00      | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
% 3.08/1.00      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.08/1.00      | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top
% 3.08/1.00      | v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_3878,c_1800,c_1801]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6659,plain,
% 3.08/1.00      ( k6_partfun1(k1_relat_1(k6_partfun1(X0_51))) != k6_partfun1(X0_51)
% 3.08/1.00      | k6_partfun1(k2_relat_1(k6_partfun1(X0_51))) = k2_funct_1(k6_partfun1(X0_51))
% 3.08/1.00      | k1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != k2_relat_1(k6_partfun1(X0_51))
% 3.08/1.00      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.08/1.00      | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(X0_51)))) != iProver_top ),
% 3.08/1.00      inference(forward_subsumption_resolution,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_6647,c_2302]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6663,plain,
% 3.08/1.00      ( k6_partfun1(k1_relat_1(k6_partfun1(k1_xboole_0))) != k6_partfun1(k1_xboole_0)
% 3.08/1.00      | k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0))) = k2_funct_1(k6_partfun1(k1_xboole_0))
% 3.08/1.00      | k1_relat_1(k6_partfun1(k2_relat_1(k1_xboole_0))) != k2_relat_1(k6_partfun1(k1_xboole_0))
% 3.08/1.00      | v1_funct_1(k6_partfun1(k2_relat_1(k6_partfun1(k1_xboole_0)))) != iProver_top
% 3.08/1.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_1744,c_6659]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1,plain,
% 3.08/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1748,plain,
% 3.08/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_0,plain,
% 3.08/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1749,plain,
% 3.08/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6664,plain,
% 3.08/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 3.08/1.00      | k1_xboole_0 != k1_xboole_0
% 3.08/1.00      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.08/1.00      inference(light_normalisation,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_6663,c_1744,c_1748,c_1749]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6665,plain,
% 3.08/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 3.08/1.00      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.08/1.00      inference(equality_resolution_simp,[status(thm)],[c_6664]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_8549,plain,
% 3.08/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_8543,c_6665]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5205,plain,
% 3.08/1.00      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_2316,c_2320]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5281,plain,
% 3.08/1.00      ( k2_relat_1(sK1) = sK0 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_5205,c_33,c_30,c_495,c_2581]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5301,plain,
% 3.08/1.00      ( sK1 = k1_xboole_0
% 3.08/1.00      | sK0 != k1_xboole_0
% 3.08/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_5281,c_2298]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2553,plain,
% 3.08/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.08/1.00      | v1_relat_1(sK1) ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_1740]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2554,plain,
% 3.08/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.08/1.00      | v1_relat_1(sK1) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2553]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5946,plain,
% 3.08/1.00      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_5301,c_37,c_2554]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5947,plain,
% 3.08/1.00      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.08/1.00      inference(renaming,[status(thm)],[c_5946]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7473,plain,
% 3.08/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_7466,c_5947]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7596,plain,
% 3.08/1.00      ( sK1 = k1_xboole_0 ),
% 3.08/1.00      inference(equality_resolution_simp,[status(thm)],[c_7473]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7489,plain,
% 3.08/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_7466,c_2362]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7577,plain,
% 3.08/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_7568,c_7489]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7598,plain,
% 3.08/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_7596,c_7577]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_8580,plain,
% 3.08/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_8549,c_7598]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_19,plain,
% 3.08/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1736,plain,
% 3.08/1.00      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 3.08/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2308,plain,
% 3.08/1.00      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1736]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_3269,plain,
% 3.08/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_1744,c_2308]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2306,plain,
% 3.08/1.00      ( r2_relset_1(X0_51,X1_51,X2_51,X2_51) = iProver_top
% 3.08/1.00      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1738]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4108,plain,
% 3.08/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_3269,c_2306]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(contradiction,plain,
% 3.08/1.00      ( $false ),
% 3.08/1.00      inference(minisat,[status(thm)],[c_8580,c_4108]) ).
% 3.08/1.00  
% 3.08/1.00  
% 3.08/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.08/1.00  
% 3.08/1.00  ------                               Statistics
% 3.08/1.00  
% 3.08/1.00  ------ General
% 3.08/1.00  
% 3.08/1.00  abstr_ref_over_cycles:                  0
% 3.08/1.00  abstr_ref_under_cycles:                 0
% 3.08/1.00  gc_basic_clause_elim:                   0
% 3.08/1.00  forced_gc_time:                         0
% 3.08/1.00  parsing_time:                           0.011
% 3.08/1.00  unif_index_cands_time:                  0.
% 3.08/1.00  unif_index_add_time:                    0.
% 3.08/1.00  orderings_time:                         0.
% 3.08/1.00  out_proof_time:                         0.013
% 3.08/1.00  total_time:                             0.302
% 3.08/1.00  num_of_symbols:                         57
% 3.08/1.00  num_of_terms:                           9473
% 3.08/1.00  
% 3.08/1.00  ------ Preprocessing
% 3.08/1.00  
% 3.08/1.00  num_of_splits:                          0
% 3.08/1.00  num_of_split_atoms:                     0
% 3.08/1.00  num_of_reused_defs:                     0
% 3.08/1.00  num_eq_ax_congr_red:                    15
% 3.08/1.00  num_of_sem_filtered_clauses:            1
% 3.08/1.00  num_of_subtypes:                        3
% 3.08/1.00  monotx_restored_types:                  1
% 3.08/1.00  sat_num_of_epr_types:                   0
% 3.08/1.00  sat_num_of_non_cyclic_types:            0
% 3.08/1.00  sat_guarded_non_collapsed_types:        1
% 3.08/1.00  num_pure_diseq_elim:                    0
% 3.08/1.00  simp_replaced_by:                       0
% 3.08/1.00  res_preprocessed:                       173
% 3.08/1.00  prep_upred:                             0
% 3.08/1.00  prep_unflattend:                        94
% 3.08/1.00  smt_new_axioms:                         0
% 3.08/1.00  pred_elim_cands:                        7
% 3.08/1.00  pred_elim:                              2
% 3.08/1.00  pred_elim_cl:                           0
% 3.08/1.00  pred_elim_cycles:                       9
% 3.08/1.00  merged_defs:                            0
% 3.08/1.00  merged_defs_ncl:                        0
% 3.08/1.00  bin_hyper_res:                          0
% 3.08/1.00  prep_cycles:                            4
% 3.08/1.00  pred_elim_time:                         0.029
% 3.08/1.00  splitting_time:                         0.
% 3.08/1.00  sem_filter_time:                        0.
% 3.08/1.00  monotx_time:                            0.001
% 3.08/1.00  subtype_inf_time:                       0.001
% 3.08/1.00  
% 3.08/1.00  ------ Problem properties
% 3.08/1.00  
% 3.08/1.00  clauses:                                33
% 3.08/1.00  conjectures:                            8
% 3.08/1.00  epr:                                    8
% 3.08/1.00  horn:                                   32
% 3.08/1.00  ground:                                 17
% 3.08/1.00  unary:                                  20
% 3.08/1.00  binary:                                 5
% 3.08/1.00  lits:                                   78
% 3.08/1.00  lits_eq:                                20
% 3.08/1.00  fd_pure:                                0
% 3.08/1.00  fd_pseudo:                              0
% 3.08/1.00  fd_cond:                                2
% 3.08/1.00  fd_pseudo_cond:                         4
% 3.08/1.00  ac_symbols:                             0
% 3.08/1.00  
% 3.08/1.00  ------ Propositional Solver
% 3.08/1.00  
% 3.08/1.00  prop_solver_calls:                      29
% 3.08/1.00  prop_fast_solver_calls:                 1534
% 3.08/1.00  smt_solver_calls:                       0
% 3.08/1.00  smt_fast_solver_calls:                  0
% 3.08/1.00  prop_num_of_clauses:                    3231
% 3.08/1.00  prop_preprocess_simplified:             9328
% 3.08/1.00  prop_fo_subsumed:                       68
% 3.08/1.00  prop_solver_time:                       0.
% 3.08/1.00  smt_solver_time:                        0.
% 3.08/1.00  smt_fast_solver_time:                   0.
% 3.08/1.00  prop_fast_solver_time:                  0.
% 3.08/1.00  prop_unsat_core_time:                   0.001
% 3.08/1.00  
% 3.08/1.00  ------ QBF
% 3.08/1.00  
% 3.08/1.00  qbf_q_res:                              0
% 3.08/1.00  qbf_num_tautologies:                    0
% 3.08/1.00  qbf_prep_cycles:                        0
% 3.08/1.00  
% 3.08/1.00  ------ BMC1
% 3.08/1.00  
% 3.08/1.00  bmc1_current_bound:                     -1
% 3.08/1.00  bmc1_last_solved_bound:                 -1
% 3.08/1.00  bmc1_unsat_core_size:                   -1
% 3.08/1.00  bmc1_unsat_core_parents_size:           -1
% 3.08/1.00  bmc1_merge_next_fun:                    0
% 3.08/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.08/1.00  
% 3.08/1.00  ------ Instantiation
% 3.08/1.00  
% 3.08/1.00  inst_num_of_clauses:                    973
% 3.08/1.00  inst_num_in_passive:                    525
% 3.08/1.00  inst_num_in_active:                     406
% 3.08/1.00  inst_num_in_unprocessed:                42
% 3.08/1.00  inst_num_of_loops:                      450
% 3.08/1.00  inst_num_of_learning_restarts:          0
% 3.08/1.00  inst_num_moves_active_passive:          41
% 3.08/1.00  inst_lit_activity:                      0
% 3.08/1.00  inst_lit_activity_moves:                0
% 3.08/1.00  inst_num_tautologies:                   0
% 3.08/1.00  inst_num_prop_implied:                  0
% 3.08/1.00  inst_num_existing_simplified:           0
% 3.08/1.00  inst_num_eq_res_simplified:             0
% 3.08/1.00  inst_num_child_elim:                    0
% 3.08/1.00  inst_num_of_dismatching_blockings:      184
% 3.08/1.00  inst_num_of_non_proper_insts:           720
% 3.08/1.00  inst_num_of_duplicates:                 0
% 3.08/1.00  inst_inst_num_from_inst_to_res:         0
% 3.08/1.00  inst_dismatching_checking_time:         0.
% 3.08/1.00  
% 3.08/1.00  ------ Resolution
% 3.08/1.00  
% 3.08/1.00  res_num_of_clauses:                     0
% 3.08/1.00  res_num_in_passive:                     0
% 3.08/1.00  res_num_in_active:                      0
% 3.08/1.00  res_num_of_loops:                       177
% 3.08/1.00  res_forward_subset_subsumed:            71
% 3.08/1.00  res_backward_subset_subsumed:           0
% 3.08/1.00  res_forward_subsumed:                   0
% 3.08/1.00  res_backward_subsumed:                  0
% 3.08/1.00  res_forward_subsumption_resolution:     4
% 3.08/1.00  res_backward_subsumption_resolution:    0
% 3.08/1.00  res_clause_to_clause_subsumption:       240
% 3.08/1.00  res_orphan_elimination:                 0
% 3.08/1.00  res_tautology_del:                      37
% 3.08/1.00  res_num_eq_res_simplified:              0
% 3.08/1.00  res_num_sel_changes:                    0
% 3.08/1.00  res_moves_from_active_to_pass:          0
% 3.08/1.00  
% 3.08/1.00  ------ Superposition
% 3.08/1.00  
% 3.08/1.00  sup_time_total:                         0.
% 3.08/1.00  sup_time_generating:                    0.
% 3.08/1.00  sup_time_sim_full:                      0.
% 3.08/1.00  sup_time_sim_immed:                     0.
% 3.08/1.00  
% 3.08/1.00  sup_num_of_clauses:                     48
% 3.08/1.00  sup_num_in_active:                      44
% 3.08/1.00  sup_num_in_passive:                     4
% 3.08/1.00  sup_num_of_loops:                       88
% 3.08/1.00  sup_fw_superposition:                   60
% 3.08/1.00  sup_bw_superposition:                   14
% 3.08/1.00  sup_immediate_simplified:               59
% 3.08/1.00  sup_given_eliminated:                   0
% 3.08/1.00  comparisons_done:                       0
% 3.08/1.00  comparisons_avoided:                    3
% 3.08/1.00  
% 3.08/1.00  ------ Simplifications
% 3.08/1.00  
% 3.08/1.00  
% 3.08/1.00  sim_fw_subset_subsumed:                 10
% 3.08/1.00  sim_bw_subset_subsumed:                 7
% 3.08/1.00  sim_fw_subsumed:                        2
% 3.08/1.00  sim_bw_subsumed:                        0
% 3.08/1.00  sim_fw_subsumption_res:                 3
% 3.08/1.00  sim_bw_subsumption_res:                 0
% 3.08/1.00  sim_tautology_del:                      1
% 3.08/1.00  sim_eq_tautology_del:                   11
% 3.08/1.00  sim_eq_res_simp:                        5
% 3.08/1.00  sim_fw_demodulated:                     0
% 3.08/1.00  sim_bw_demodulated:                     66
% 3.08/1.00  sim_light_normalised:                   22
% 3.08/1.00  sim_joinable_taut:                      0
% 3.08/1.00  sim_joinable_simp:                      0
% 3.08/1.00  sim_ac_normalised:                      0
% 3.08/1.00  sim_smt_subsumption:                    0
% 3.08/1.00  
%------------------------------------------------------------------------------
