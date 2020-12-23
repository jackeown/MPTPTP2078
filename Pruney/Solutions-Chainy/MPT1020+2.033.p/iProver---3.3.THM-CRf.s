%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:11 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_36)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f44,f43])).

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f52,f65,f65])).

cnf(c_23,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1625,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1621,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_323,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_16])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_335,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_323,c_7])).

cnf(c_1617,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_3453,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1621,c_1617])).

cnf(c_12,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_411,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_412,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_414,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_31,c_28])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_335,c_414])).

cnf(c_490,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_492,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_4403,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3453,c_28,c_492])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1631,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3633,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1621,c_1631])).

cnf(c_4406,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_4403,c_3633])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_167,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_20])).

cnf(c_168,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_1618,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_4676,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_1618])).

cnf(c_32,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6168,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4676,c_32,c_33,c_35])).

cnf(c_6169,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6168])).

cnf(c_6180,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1625,c_6169])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6181,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6180])).

cnf(c_6183,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6180,c_36,c_37,c_39])).

cnf(c_6184,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6183])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1626,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_430,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_431,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_433,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_31,c_30,c_28])).

cnf(c_1667,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1626,c_433])).

cnf(c_6187,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6184,c_1667])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1853,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1854,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1853])).

cnf(c_6529,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6187,c_39,c_1854])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1634,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4407,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4403,c_1634])).

cnf(c_1822,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1823,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1822])).

cnf(c_5678,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4407,c_35,c_1823])).

cnf(c_5679,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5678])).

cnf(c_6536,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6529,c_5679])).

cnf(c_6643,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6536])).

cnf(c_1624,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3452,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1617])).

cnf(c_25,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_400,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_401,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_403,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_27,c_24])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_335,c_403])).

cnf(c_480,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_482,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_4386,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3452,c_24,c_482])).

cnf(c_4390,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4386,c_1634])).

cnf(c_1819,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1820,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1819])).

cnf(c_5583,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4390,c_39,c_1820])).

cnf(c_5584,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5583])).

cnf(c_6537,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6529,c_5584])).

cnf(c_6611,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6537])).

cnf(c_6548,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6529,c_1667])).

cnf(c_6619,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6611,c_6548])).

cnf(c_6645,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6643,c_6619])).

cnf(c_5,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1633,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2832,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1633])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_54,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1814,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_relat_1(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1815,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_2956,plain,
    ( k1_xboole_0 != X0
    | k6_partfun1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2832,c_54,c_1815])).

cnf(c_2957,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_2956])).

cnf(c_2961,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2957])).

cnf(c_6,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2994,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2961,c_6])).

cnf(c_3001,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2994,c_2961])).

cnf(c_6659,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6645,c_3001])).

cnf(c_1628,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2993,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2961,c_1628])).

cnf(c_1630,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3613,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2993,c_1630])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6659,c_3613])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:38:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.41/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.01  
% 2.41/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/1.01  
% 2.41/1.01  ------  iProver source info
% 2.41/1.01  
% 2.41/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.41/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/1.01  git: non_committed_changes: false
% 2.41/1.01  git: last_make_outside_of_git: false
% 2.41/1.01  
% 2.41/1.01  ------ 
% 2.41/1.01  
% 2.41/1.01  ------ Input Options
% 2.41/1.01  
% 2.41/1.01  --out_options                           all
% 2.41/1.01  --tptp_safe_out                         true
% 2.41/1.01  --problem_path                          ""
% 2.41/1.01  --include_path                          ""
% 2.41/1.01  --clausifier                            res/vclausify_rel
% 2.41/1.01  --clausifier_options                    --mode clausify
% 2.41/1.01  --stdin                                 false
% 2.41/1.01  --stats_out                             all
% 2.41/1.01  
% 2.41/1.01  ------ General Options
% 2.41/1.01  
% 2.41/1.01  --fof                                   false
% 2.41/1.01  --time_out_real                         305.
% 2.41/1.01  --time_out_virtual                      -1.
% 2.41/1.01  --symbol_type_check                     false
% 2.41/1.01  --clausify_out                          false
% 2.41/1.01  --sig_cnt_out                           false
% 2.41/1.01  --trig_cnt_out                          false
% 2.41/1.01  --trig_cnt_out_tolerance                1.
% 2.41/1.01  --trig_cnt_out_sk_spl                   false
% 2.41/1.01  --abstr_cl_out                          false
% 2.41/1.01  
% 2.41/1.01  ------ Global Options
% 2.41/1.01  
% 2.41/1.01  --schedule                              default
% 2.41/1.01  --add_important_lit                     false
% 2.41/1.01  --prop_solver_per_cl                    1000
% 2.41/1.01  --min_unsat_core                        false
% 2.41/1.01  --soft_assumptions                      false
% 2.41/1.01  --soft_lemma_size                       3
% 2.41/1.01  --prop_impl_unit_size                   0
% 2.41/1.01  --prop_impl_unit                        []
% 2.41/1.01  --share_sel_clauses                     true
% 2.41/1.01  --reset_solvers                         false
% 2.41/1.01  --bc_imp_inh                            [conj_cone]
% 2.41/1.01  --conj_cone_tolerance                   3.
% 2.41/1.01  --extra_neg_conj                        none
% 2.41/1.01  --large_theory_mode                     true
% 2.41/1.01  --prolific_symb_bound                   200
% 2.41/1.01  --lt_threshold                          2000
% 2.41/1.01  --clause_weak_htbl                      true
% 2.41/1.01  --gc_record_bc_elim                     false
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing Options
% 2.41/1.01  
% 2.41/1.01  --preprocessing_flag                    true
% 2.41/1.01  --time_out_prep_mult                    0.1
% 2.41/1.01  --splitting_mode                        input
% 2.41/1.01  --splitting_grd                         true
% 2.41/1.01  --splitting_cvd                         false
% 2.41/1.01  --splitting_cvd_svl                     false
% 2.41/1.01  --splitting_nvd                         32
% 2.41/1.01  --sub_typing                            true
% 2.41/1.01  --prep_gs_sim                           true
% 2.41/1.01  --prep_unflatten                        true
% 2.41/1.01  --prep_res_sim                          true
% 2.41/1.01  --prep_upred                            true
% 2.41/1.01  --prep_sem_filter                       exhaustive
% 2.41/1.01  --prep_sem_filter_out                   false
% 2.41/1.01  --pred_elim                             true
% 2.41/1.01  --res_sim_input                         true
% 2.41/1.01  --eq_ax_congr_red                       true
% 2.41/1.01  --pure_diseq_elim                       true
% 2.41/1.01  --brand_transform                       false
% 2.41/1.01  --non_eq_to_eq                          false
% 2.41/1.01  --prep_def_merge                        true
% 2.41/1.01  --prep_def_merge_prop_impl              false
% 2.41/1.01  --prep_def_merge_mbd                    true
% 2.41/1.01  --prep_def_merge_tr_red                 false
% 2.41/1.01  --prep_def_merge_tr_cl                  false
% 2.41/1.01  --smt_preprocessing                     true
% 2.41/1.01  --smt_ac_axioms                         fast
% 2.41/1.01  --preprocessed_out                      false
% 2.41/1.01  --preprocessed_stats                    false
% 2.41/1.01  
% 2.41/1.01  ------ Abstraction refinement Options
% 2.41/1.01  
% 2.41/1.01  --abstr_ref                             []
% 2.41/1.01  --abstr_ref_prep                        false
% 2.41/1.01  --abstr_ref_until_sat                   false
% 2.41/1.01  --abstr_ref_sig_restrict                funpre
% 2.41/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.01  --abstr_ref_under                       []
% 2.41/1.01  
% 2.41/1.01  ------ SAT Options
% 2.41/1.01  
% 2.41/1.01  --sat_mode                              false
% 2.41/1.01  --sat_fm_restart_options                ""
% 2.41/1.01  --sat_gr_def                            false
% 2.41/1.01  --sat_epr_types                         true
% 2.41/1.01  --sat_non_cyclic_types                  false
% 2.41/1.01  --sat_finite_models                     false
% 2.41/1.01  --sat_fm_lemmas                         false
% 2.41/1.01  --sat_fm_prep                           false
% 2.41/1.01  --sat_fm_uc_incr                        true
% 2.41/1.01  --sat_out_model                         small
% 2.41/1.01  --sat_out_clauses                       false
% 2.41/1.01  
% 2.41/1.01  ------ QBF Options
% 2.41/1.01  
% 2.41/1.01  --qbf_mode                              false
% 2.41/1.01  --qbf_elim_univ                         false
% 2.41/1.01  --qbf_dom_inst                          none
% 2.41/1.01  --qbf_dom_pre_inst                      false
% 2.41/1.01  --qbf_sk_in                             false
% 2.41/1.01  --qbf_pred_elim                         true
% 2.41/1.01  --qbf_split                             512
% 2.41/1.01  
% 2.41/1.01  ------ BMC1 Options
% 2.41/1.01  
% 2.41/1.01  --bmc1_incremental                      false
% 2.41/1.01  --bmc1_axioms                           reachable_all
% 2.41/1.01  --bmc1_min_bound                        0
% 2.41/1.01  --bmc1_max_bound                        -1
% 2.41/1.01  --bmc1_max_bound_default                -1
% 2.41/1.01  --bmc1_symbol_reachability              true
% 2.41/1.01  --bmc1_property_lemmas                  false
% 2.41/1.01  --bmc1_k_induction                      false
% 2.41/1.01  --bmc1_non_equiv_states                 false
% 2.41/1.01  --bmc1_deadlock                         false
% 2.41/1.01  --bmc1_ucm                              false
% 2.41/1.01  --bmc1_add_unsat_core                   none
% 2.41/1.01  --bmc1_unsat_core_children              false
% 2.41/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.01  --bmc1_out_stat                         full
% 2.41/1.01  --bmc1_ground_init                      false
% 2.41/1.01  --bmc1_pre_inst_next_state              false
% 2.41/1.01  --bmc1_pre_inst_state                   false
% 2.41/1.01  --bmc1_pre_inst_reach_state             false
% 2.41/1.01  --bmc1_out_unsat_core                   false
% 2.41/1.01  --bmc1_aig_witness_out                  false
% 2.41/1.01  --bmc1_verbose                          false
% 2.41/1.01  --bmc1_dump_clauses_tptp                false
% 2.41/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.01  --bmc1_dump_file                        -
% 2.41/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.01  --bmc1_ucm_extend_mode                  1
% 2.41/1.01  --bmc1_ucm_init_mode                    2
% 2.41/1.01  --bmc1_ucm_cone_mode                    none
% 2.41/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.01  --bmc1_ucm_relax_model                  4
% 2.41/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.01  --bmc1_ucm_layered_model                none
% 2.41/1.01  --bmc1_ucm_max_lemma_size               10
% 2.41/1.01  
% 2.41/1.01  ------ AIG Options
% 2.41/1.01  
% 2.41/1.01  --aig_mode                              false
% 2.41/1.01  
% 2.41/1.01  ------ Instantiation Options
% 2.41/1.01  
% 2.41/1.01  --instantiation_flag                    true
% 2.41/1.01  --inst_sos_flag                         false
% 2.41/1.01  --inst_sos_phase                        true
% 2.41/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.01  --inst_lit_sel_side                     num_symb
% 2.41/1.01  --inst_solver_per_active                1400
% 2.41/1.01  --inst_solver_calls_frac                1.
% 2.41/1.01  --inst_passive_queue_type               priority_queues
% 2.41/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.01  --inst_passive_queues_freq              [25;2]
% 2.41/1.01  --inst_dismatching                      true
% 2.41/1.01  --inst_eager_unprocessed_to_passive     true
% 2.41/1.01  --inst_prop_sim_given                   true
% 2.41/1.01  --inst_prop_sim_new                     false
% 2.41/1.01  --inst_subs_new                         false
% 2.41/1.01  --inst_eq_res_simp                      false
% 2.41/1.01  --inst_subs_given                       false
% 2.41/1.01  --inst_orphan_elimination               true
% 2.41/1.01  --inst_learning_loop_flag               true
% 2.41/1.01  --inst_learning_start                   3000
% 2.41/1.01  --inst_learning_factor                  2
% 2.41/1.01  --inst_start_prop_sim_after_learn       3
% 2.41/1.01  --inst_sel_renew                        solver
% 2.41/1.01  --inst_lit_activity_flag                true
% 2.41/1.01  --inst_restr_to_given                   false
% 2.41/1.01  --inst_activity_threshold               500
% 2.41/1.01  --inst_out_proof                        true
% 2.41/1.01  
% 2.41/1.01  ------ Resolution Options
% 2.41/1.01  
% 2.41/1.01  --resolution_flag                       true
% 2.41/1.01  --res_lit_sel                           adaptive
% 2.41/1.01  --res_lit_sel_side                      none
% 2.41/1.01  --res_ordering                          kbo
% 2.41/1.01  --res_to_prop_solver                    active
% 2.41/1.01  --res_prop_simpl_new                    false
% 2.41/1.01  --res_prop_simpl_given                  true
% 2.41/1.01  --res_passive_queue_type                priority_queues
% 2.41/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.01  --res_passive_queues_freq               [15;5]
% 2.41/1.01  --res_forward_subs                      full
% 2.41/1.01  --res_backward_subs                     full
% 2.41/1.01  --res_forward_subs_resolution           true
% 2.41/1.01  --res_backward_subs_resolution          true
% 2.41/1.01  --res_orphan_elimination                true
% 2.41/1.01  --res_time_limit                        2.
% 2.41/1.01  --res_out_proof                         true
% 2.41/1.01  
% 2.41/1.01  ------ Superposition Options
% 2.41/1.01  
% 2.41/1.01  --superposition_flag                    true
% 2.41/1.01  --sup_passive_queue_type                priority_queues
% 2.41/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.01  --demod_completeness_check              fast
% 2.41/1.01  --demod_use_ground                      true
% 2.41/1.01  --sup_to_prop_solver                    passive
% 2.41/1.01  --sup_prop_simpl_new                    true
% 2.41/1.01  --sup_prop_simpl_given                  true
% 2.41/1.01  --sup_fun_splitting                     false
% 2.41/1.01  --sup_smt_interval                      50000
% 2.41/1.01  
% 2.41/1.01  ------ Superposition Simplification Setup
% 2.41/1.01  
% 2.41/1.01  --sup_indices_passive                   []
% 2.41/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_full_bw                           [BwDemod]
% 2.41/1.01  --sup_immed_triv                        [TrivRules]
% 2.41/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_immed_bw_main                     []
% 2.41/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.01  
% 2.41/1.01  ------ Combination Options
% 2.41/1.01  
% 2.41/1.01  --comb_res_mult                         3
% 2.41/1.01  --comb_sup_mult                         2
% 2.41/1.01  --comb_inst_mult                        10
% 2.41/1.01  
% 2.41/1.01  ------ Debug Options
% 2.41/1.01  
% 2.41/1.01  --dbg_backtrace                         false
% 2.41/1.01  --dbg_dump_prop_clauses                 false
% 2.41/1.01  --dbg_dump_prop_clauses_file            -
% 2.41/1.01  --dbg_out_stat                          false
% 2.41/1.01  ------ Parsing...
% 2.41/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/1.01  ------ Proving...
% 2.41/1.01  ------ Problem Properties 
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  clauses                                 28
% 2.41/1.01  conjectures                             8
% 2.41/1.01  EPR                                     8
% 2.41/1.01  Horn                                    27
% 2.41/1.01  unary                                   17
% 2.41/1.01  binary                                  4
% 2.41/1.01  lits                                    60
% 2.41/1.01  lits eq                                 17
% 2.41/1.01  fd_pure                                 0
% 2.41/1.01  fd_pseudo                               0
% 2.41/1.01  fd_cond                                 2
% 2.41/1.01  fd_pseudo_cond                          4
% 2.41/1.01  AC symbols                              0
% 2.41/1.01  
% 2.41/1.01  ------ Schedule dynamic 5 is on 
% 2.41/1.01  
% 2.41/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  ------ 
% 2.41/1.01  Current options:
% 2.41/1.01  ------ 
% 2.41/1.01  
% 2.41/1.01  ------ Input Options
% 2.41/1.01  
% 2.41/1.01  --out_options                           all
% 2.41/1.01  --tptp_safe_out                         true
% 2.41/1.01  --problem_path                          ""
% 2.41/1.01  --include_path                          ""
% 2.41/1.01  --clausifier                            res/vclausify_rel
% 2.41/1.01  --clausifier_options                    --mode clausify
% 2.41/1.01  --stdin                                 false
% 2.41/1.01  --stats_out                             all
% 2.41/1.01  
% 2.41/1.01  ------ General Options
% 2.41/1.01  
% 2.41/1.01  --fof                                   false
% 2.41/1.01  --time_out_real                         305.
% 2.41/1.01  --time_out_virtual                      -1.
% 2.41/1.01  --symbol_type_check                     false
% 2.41/1.01  --clausify_out                          false
% 2.41/1.01  --sig_cnt_out                           false
% 2.41/1.01  --trig_cnt_out                          false
% 2.41/1.01  --trig_cnt_out_tolerance                1.
% 2.41/1.01  --trig_cnt_out_sk_spl                   false
% 2.41/1.01  --abstr_cl_out                          false
% 2.41/1.01  
% 2.41/1.01  ------ Global Options
% 2.41/1.01  
% 2.41/1.01  --schedule                              default
% 2.41/1.01  --add_important_lit                     false
% 2.41/1.01  --prop_solver_per_cl                    1000
% 2.41/1.01  --min_unsat_core                        false
% 2.41/1.01  --soft_assumptions                      false
% 2.41/1.01  --soft_lemma_size                       3
% 2.41/1.01  --prop_impl_unit_size                   0
% 2.41/1.01  --prop_impl_unit                        []
% 2.41/1.01  --share_sel_clauses                     true
% 2.41/1.01  --reset_solvers                         false
% 2.41/1.01  --bc_imp_inh                            [conj_cone]
% 2.41/1.01  --conj_cone_tolerance                   3.
% 2.41/1.01  --extra_neg_conj                        none
% 2.41/1.01  --large_theory_mode                     true
% 2.41/1.01  --prolific_symb_bound                   200
% 2.41/1.01  --lt_threshold                          2000
% 2.41/1.01  --clause_weak_htbl                      true
% 2.41/1.01  --gc_record_bc_elim                     false
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing Options
% 2.41/1.01  
% 2.41/1.01  --preprocessing_flag                    true
% 2.41/1.01  --time_out_prep_mult                    0.1
% 2.41/1.01  --splitting_mode                        input
% 2.41/1.01  --splitting_grd                         true
% 2.41/1.01  --splitting_cvd                         false
% 2.41/1.01  --splitting_cvd_svl                     false
% 2.41/1.01  --splitting_nvd                         32
% 2.41/1.01  --sub_typing                            true
% 2.41/1.01  --prep_gs_sim                           true
% 2.41/1.01  --prep_unflatten                        true
% 2.41/1.01  --prep_res_sim                          true
% 2.41/1.01  --prep_upred                            true
% 2.41/1.01  --prep_sem_filter                       exhaustive
% 2.41/1.01  --prep_sem_filter_out                   false
% 2.41/1.01  --pred_elim                             true
% 2.41/1.01  --res_sim_input                         true
% 2.41/1.01  --eq_ax_congr_red                       true
% 2.41/1.01  --pure_diseq_elim                       true
% 2.41/1.01  --brand_transform                       false
% 2.41/1.01  --non_eq_to_eq                          false
% 2.41/1.01  --prep_def_merge                        true
% 2.41/1.01  --prep_def_merge_prop_impl              false
% 2.41/1.01  --prep_def_merge_mbd                    true
% 2.41/1.01  --prep_def_merge_tr_red                 false
% 2.41/1.01  --prep_def_merge_tr_cl                  false
% 2.41/1.01  --smt_preprocessing                     true
% 2.41/1.01  --smt_ac_axioms                         fast
% 2.41/1.01  --preprocessed_out                      false
% 2.41/1.01  --preprocessed_stats                    false
% 2.41/1.01  
% 2.41/1.01  ------ Abstraction refinement Options
% 2.41/1.01  
% 2.41/1.01  --abstr_ref                             []
% 2.41/1.01  --abstr_ref_prep                        false
% 2.41/1.01  --abstr_ref_until_sat                   false
% 2.41/1.01  --abstr_ref_sig_restrict                funpre
% 2.41/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.01  --abstr_ref_under                       []
% 2.41/1.01  
% 2.41/1.01  ------ SAT Options
% 2.41/1.01  
% 2.41/1.01  --sat_mode                              false
% 2.41/1.01  --sat_fm_restart_options                ""
% 2.41/1.01  --sat_gr_def                            false
% 2.41/1.01  --sat_epr_types                         true
% 2.41/1.01  --sat_non_cyclic_types                  false
% 2.41/1.01  --sat_finite_models                     false
% 2.41/1.01  --sat_fm_lemmas                         false
% 2.41/1.01  --sat_fm_prep                           false
% 2.41/1.01  --sat_fm_uc_incr                        true
% 2.41/1.01  --sat_out_model                         small
% 2.41/1.01  --sat_out_clauses                       false
% 2.41/1.01  
% 2.41/1.01  ------ QBF Options
% 2.41/1.01  
% 2.41/1.01  --qbf_mode                              false
% 2.41/1.01  --qbf_elim_univ                         false
% 2.41/1.01  --qbf_dom_inst                          none
% 2.41/1.01  --qbf_dom_pre_inst                      false
% 2.41/1.01  --qbf_sk_in                             false
% 2.41/1.01  --qbf_pred_elim                         true
% 2.41/1.01  --qbf_split                             512
% 2.41/1.01  
% 2.41/1.01  ------ BMC1 Options
% 2.41/1.01  
% 2.41/1.01  --bmc1_incremental                      false
% 2.41/1.01  --bmc1_axioms                           reachable_all
% 2.41/1.01  --bmc1_min_bound                        0
% 2.41/1.01  --bmc1_max_bound                        -1
% 2.41/1.01  --bmc1_max_bound_default                -1
% 2.41/1.01  --bmc1_symbol_reachability              true
% 2.41/1.01  --bmc1_property_lemmas                  false
% 2.41/1.01  --bmc1_k_induction                      false
% 2.41/1.01  --bmc1_non_equiv_states                 false
% 2.41/1.01  --bmc1_deadlock                         false
% 2.41/1.01  --bmc1_ucm                              false
% 2.41/1.01  --bmc1_add_unsat_core                   none
% 2.41/1.01  --bmc1_unsat_core_children              false
% 2.41/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.01  --bmc1_out_stat                         full
% 2.41/1.01  --bmc1_ground_init                      false
% 2.41/1.01  --bmc1_pre_inst_next_state              false
% 2.41/1.01  --bmc1_pre_inst_state                   false
% 2.41/1.01  --bmc1_pre_inst_reach_state             false
% 2.41/1.01  --bmc1_out_unsat_core                   false
% 2.41/1.01  --bmc1_aig_witness_out                  false
% 2.41/1.01  --bmc1_verbose                          false
% 2.41/1.01  --bmc1_dump_clauses_tptp                false
% 2.41/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.01  --bmc1_dump_file                        -
% 2.41/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.01  --bmc1_ucm_extend_mode                  1
% 2.41/1.01  --bmc1_ucm_init_mode                    2
% 2.41/1.01  --bmc1_ucm_cone_mode                    none
% 2.41/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.01  --bmc1_ucm_relax_model                  4
% 2.41/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.01  --bmc1_ucm_layered_model                none
% 2.41/1.01  --bmc1_ucm_max_lemma_size               10
% 2.41/1.01  
% 2.41/1.01  ------ AIG Options
% 2.41/1.01  
% 2.41/1.01  --aig_mode                              false
% 2.41/1.01  
% 2.41/1.01  ------ Instantiation Options
% 2.41/1.01  
% 2.41/1.01  --instantiation_flag                    true
% 2.41/1.01  --inst_sos_flag                         false
% 2.41/1.01  --inst_sos_phase                        true
% 2.41/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.01  --inst_lit_sel_side                     none
% 2.41/1.01  --inst_solver_per_active                1400
% 2.41/1.01  --inst_solver_calls_frac                1.
% 2.41/1.01  --inst_passive_queue_type               priority_queues
% 2.41/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.01  --inst_passive_queues_freq              [25;2]
% 2.41/1.01  --inst_dismatching                      true
% 2.41/1.01  --inst_eager_unprocessed_to_passive     true
% 2.41/1.01  --inst_prop_sim_given                   true
% 2.41/1.01  --inst_prop_sim_new                     false
% 2.41/1.01  --inst_subs_new                         false
% 2.41/1.01  --inst_eq_res_simp                      false
% 2.41/1.01  --inst_subs_given                       false
% 2.41/1.01  --inst_orphan_elimination               true
% 2.41/1.01  --inst_learning_loop_flag               true
% 2.41/1.01  --inst_learning_start                   3000
% 2.41/1.01  --inst_learning_factor                  2
% 2.41/1.01  --inst_start_prop_sim_after_learn       3
% 2.41/1.01  --inst_sel_renew                        solver
% 2.41/1.01  --inst_lit_activity_flag                true
% 2.41/1.01  --inst_restr_to_given                   false
% 2.41/1.01  --inst_activity_threshold               500
% 2.41/1.01  --inst_out_proof                        true
% 2.41/1.01  
% 2.41/1.01  ------ Resolution Options
% 2.41/1.01  
% 2.41/1.01  --resolution_flag                       false
% 2.41/1.01  --res_lit_sel                           adaptive
% 2.41/1.01  --res_lit_sel_side                      none
% 2.41/1.01  --res_ordering                          kbo
% 2.41/1.01  --res_to_prop_solver                    active
% 2.41/1.01  --res_prop_simpl_new                    false
% 2.41/1.01  --res_prop_simpl_given                  true
% 2.41/1.01  --res_passive_queue_type                priority_queues
% 2.41/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.01  --res_passive_queues_freq               [15;5]
% 2.41/1.01  --res_forward_subs                      full
% 2.41/1.01  --res_backward_subs                     full
% 2.41/1.01  --res_forward_subs_resolution           true
% 2.41/1.01  --res_backward_subs_resolution          true
% 2.41/1.01  --res_orphan_elimination                true
% 2.41/1.01  --res_time_limit                        2.
% 2.41/1.01  --res_out_proof                         true
% 2.41/1.01  
% 2.41/1.01  ------ Superposition Options
% 2.41/1.01  
% 2.41/1.01  --superposition_flag                    true
% 2.41/1.01  --sup_passive_queue_type                priority_queues
% 2.41/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.01  --demod_completeness_check              fast
% 2.41/1.01  --demod_use_ground                      true
% 2.41/1.01  --sup_to_prop_solver                    passive
% 2.41/1.01  --sup_prop_simpl_new                    true
% 2.41/1.01  --sup_prop_simpl_given                  true
% 2.41/1.01  --sup_fun_splitting                     false
% 2.41/1.01  --sup_smt_interval                      50000
% 2.41/1.01  
% 2.41/1.01  ------ Superposition Simplification Setup
% 2.41/1.01  
% 2.41/1.01  --sup_indices_passive                   []
% 2.41/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_full_bw                           [BwDemod]
% 2.41/1.01  --sup_immed_triv                        [TrivRules]
% 2.41/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_immed_bw_main                     []
% 2.41/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.01  
% 2.41/1.01  ------ Combination Options
% 2.41/1.01  
% 2.41/1.01  --comb_res_mult                         3
% 2.41/1.01  --comb_sup_mult                         2
% 2.41/1.01  --comb_inst_mult                        10
% 2.41/1.01  
% 2.41/1.01  ------ Debug Options
% 2.41/1.01  
% 2.41/1.01  --dbg_backtrace                         false
% 2.41/1.01  --dbg_dump_prop_clauses                 false
% 2.41/1.01  --dbg_dump_prop_clauses_file            -
% 2.41/1.01  --dbg_out_stat                          false
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  ------ Proving...
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  % SZS status Theorem for theBenchmark.p
% 2.41/1.01  
% 2.41/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/1.01  
% 2.41/1.01  fof(f17,conjecture,(
% 2.41/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f18,negated_conjecture,(
% 2.41/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.41/1.01    inference(negated_conjecture,[],[f17])).
% 2.41/1.01  
% 2.41/1.01  fof(f39,plain,(
% 2.41/1.01    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.41/1.01    inference(ennf_transformation,[],[f18])).
% 2.41/1.01  
% 2.41/1.01  fof(f40,plain,(
% 2.41/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.41/1.01    inference(flattening,[],[f39])).
% 2.41/1.01  
% 2.41/1.01  fof(f44,plain,(
% 2.41/1.01    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 2.41/1.01    introduced(choice_axiom,[])).
% 2.41/1.01  
% 2.41/1.01  fof(f43,plain,(
% 2.41/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.41/1.01    introduced(choice_axiom,[])).
% 2.41/1.01  
% 2.41/1.01  fof(f45,plain,(
% 2.41/1.01    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.41/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f44,f43])).
% 2.41/1.01  
% 2.41/1.01  fof(f77,plain,(
% 2.41/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f72,plain,(
% 2.41/1.01    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f7,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f20,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.41/1.01    inference(pure_predicate_removal,[],[f7])).
% 2.41/1.01  
% 2.41/1.01  fof(f25,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(ennf_transformation,[],[f20])).
% 2.41/1.01  
% 2.41/1.01  fof(f54,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f25])).
% 2.41/1.01  
% 2.41/1.01  fof(f11,axiom,(
% 2.41/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f31,plain,(
% 2.41/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.41/1.01    inference(ennf_transformation,[],[f11])).
% 2.41/1.01  
% 2.41/1.01  fof(f32,plain,(
% 2.41/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.41/1.01    inference(flattening,[],[f31])).
% 2.41/1.01  
% 2.41/1.01  fof(f42,plain,(
% 2.41/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.41/1.01    inference(nnf_transformation,[],[f32])).
% 2.41/1.01  
% 2.41/1.01  fof(f61,plain,(
% 2.41/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f42])).
% 2.41/1.01  
% 2.41/1.01  fof(f6,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f24,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(ennf_transformation,[],[f6])).
% 2.41/1.01  
% 2.41/1.01  fof(f53,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f24])).
% 2.41/1.01  
% 2.41/1.01  fof(f10,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f29,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(ennf_transformation,[],[f10])).
% 2.41/1.01  
% 2.41/1.01  fof(f30,plain,(
% 2.41/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(flattening,[],[f29])).
% 2.41/1.01  
% 2.41/1.01  fof(f60,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f30])).
% 2.41/1.01  
% 2.41/1.01  fof(f71,plain,(
% 2.41/1.01    v3_funct_2(sK1,sK0,sK0)),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f69,plain,(
% 2.41/1.01    v1_funct_1(sK1)),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f8,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f26,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(ennf_transformation,[],[f8])).
% 2.41/1.01  
% 2.41/1.01  fof(f55,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f26])).
% 2.41/1.01  
% 2.41/1.01  fof(f16,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f37,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/1.01    inference(ennf_transformation,[],[f16])).
% 2.41/1.01  
% 2.41/1.01  fof(f38,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/1.01    inference(flattening,[],[f37])).
% 2.41/1.01  
% 2.41/1.01  fof(f68,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f38])).
% 2.41/1.01  
% 2.41/1.01  fof(f15,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f35,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/1.01    inference(ennf_transformation,[],[f15])).
% 2.41/1.01  
% 2.41/1.01  fof(f36,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/1.01    inference(flattening,[],[f35])).
% 2.41/1.01  
% 2.41/1.01  fof(f66,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f36])).
% 2.41/1.01  
% 2.41/1.01  fof(f70,plain,(
% 2.41/1.01    v1_funct_2(sK1,sK0,sK0)),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f73,plain,(
% 2.41/1.01    v1_funct_1(sK2)),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f74,plain,(
% 2.41/1.01    v1_funct_2(sK2,sK0,sK0)),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f76,plain,(
% 2.41/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f78,plain,(
% 2.41/1.01    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f13,axiom,(
% 2.41/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f33,plain,(
% 2.41/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.41/1.01    inference(ennf_transformation,[],[f13])).
% 2.41/1.01  
% 2.41/1.01  fof(f34,plain,(
% 2.41/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.41/1.01    inference(flattening,[],[f33])).
% 2.41/1.01  
% 2.41/1.01  fof(f64,plain,(
% 2.41/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f34])).
% 2.41/1.01  
% 2.41/1.01  fof(f9,axiom,(
% 2.41/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f27,plain,(
% 2.41/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.41/1.01    inference(ennf_transformation,[],[f9])).
% 2.41/1.01  
% 2.41/1.01  fof(f28,plain,(
% 2.41/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(flattening,[],[f27])).
% 2.41/1.01  
% 2.41/1.01  fof(f41,plain,(
% 2.41/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(nnf_transformation,[],[f28])).
% 2.41/1.01  
% 2.41/1.01  fof(f57,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f41])).
% 2.41/1.01  
% 2.41/1.01  fof(f82,plain,(
% 2.41/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.01    inference(equality_resolution,[],[f57])).
% 2.41/1.01  
% 2.41/1.01  fof(f3,axiom,(
% 2.41/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f22,plain,(
% 2.41/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.41/1.01    inference(ennf_transformation,[],[f3])).
% 2.41/1.01  
% 2.41/1.01  fof(f23,plain,(
% 2.41/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.41/1.01    inference(flattening,[],[f22])).
% 2.41/1.01  
% 2.41/1.01  fof(f49,plain,(
% 2.41/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f23])).
% 2.41/1.01  
% 2.41/1.01  fof(f75,plain,(
% 2.41/1.01    v3_funct_2(sK2,sK0,sK0)),
% 2.41/1.01    inference(cnf_transformation,[],[f45])).
% 2.41/1.01  
% 2.41/1.01  fof(f4,axiom,(
% 2.41/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f50,plain,(
% 2.41/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.41/1.01    inference(cnf_transformation,[],[f4])).
% 2.41/1.01  
% 2.41/1.01  fof(f14,axiom,(
% 2.41/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f65,plain,(
% 2.41/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f14])).
% 2.41/1.01  
% 2.41/1.01  fof(f80,plain,(
% 2.41/1.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.41/1.01    inference(definition_unfolding,[],[f50,f65])).
% 2.41/1.01  
% 2.41/1.01  fof(f48,plain,(
% 2.41/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f23])).
% 2.41/1.01  
% 2.41/1.01  fof(f12,axiom,(
% 2.41/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f19,plain,(
% 2.41/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.41/1.01    inference(pure_predicate_removal,[],[f12])).
% 2.41/1.01  
% 2.41/1.01  fof(f63,plain,(
% 2.41/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f19])).
% 2.41/1.01  
% 2.41/1.01  fof(f5,axiom,(
% 2.41/1.01    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f52,plain,(
% 2.41/1.01    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f5])).
% 2.41/1.01  
% 2.41/1.01  fof(f81,plain,(
% 2.41/1.01    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 2.41/1.01    inference(definition_unfolding,[],[f52,f65,f65])).
% 2.41/1.01  
% 2.41/1.01  cnf(c_23,negated_conjecture,
% 2.41/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1625,plain,
% 2.41/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_28,negated_conjecture,
% 2.41/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.41/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1621,plain,
% 2.41/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_8,plain,
% 2.41/1.01      ( v5_relat_1(X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.41/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_16,plain,
% 2.41/1.01      ( ~ v2_funct_2(X0,X1)
% 2.41/1.01      | ~ v5_relat_1(X0,X1)
% 2.41/1.01      | ~ v1_relat_1(X0)
% 2.41/1.01      | k2_relat_1(X0) = X1 ),
% 2.41/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_323,plain,
% 2.41/1.01      ( ~ v2_funct_2(X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.41/1.01      | ~ v1_relat_1(X0)
% 2.41/1.01      | k2_relat_1(X0) = X1 ),
% 2.41/1.01      inference(resolution,[status(thm)],[c_8,c_16]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | v1_relat_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_335,plain,
% 2.41/1.01      ( ~ v2_funct_2(X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.41/1.01      | k2_relat_1(X0) = X1 ),
% 2.41/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_323,c_7]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1617,plain,
% 2.41/1.01      ( k2_relat_1(X0) = X1
% 2.41/1.01      | v2_funct_2(X0,X1) != iProver_top
% 2.41/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3453,plain,
% 2.41/1.01      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1621,c_1617]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_12,plain,
% 2.41/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.41/1.01      | v2_funct_2(X0,X2)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_funct_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_29,negated_conjecture,
% 2.41/1.01      ( v3_funct_2(sK1,sK0,sK0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_411,plain,
% 2.41/1.01      ( v2_funct_2(X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | sK1 != X0
% 2.41/1.01      | sK0 != X1
% 2.41/1.01      | sK0 != X2 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_412,plain,
% 2.41/1.01      ( v2_funct_2(sK1,sK0)
% 2.41/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.41/1.01      | ~ v1_funct_1(sK1) ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_411]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_31,negated_conjecture,
% 2.41/1.01      ( v1_funct_1(sK1) ),
% 2.41/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_414,plain,
% 2.41/1.01      ( v2_funct_2(sK1,sK0) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_412,c_31,c_28]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_489,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | k2_relat_1(X0) = X2
% 2.41/1.01      | sK1 != X0
% 2.41/1.01      | sK0 != X2 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_335,c_414]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_490,plain,
% 2.41/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 2.41/1.01      | k2_relat_1(sK1) = sK0 ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_489]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_492,plain,
% 2.41/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.41/1.01      | k2_relat_1(sK1) = sK0 ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_490]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4403,plain,
% 2.41/1.01      ( k2_relat_1(sK1) = sK0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_3453,c_28,c_492]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_9,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1631,plain,
% 2.41/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.41/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3633,plain,
% 2.41/1.01      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1621,c_1631]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4406,plain,
% 2.41/1.01      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_4403,c_3633]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_21,plain,
% 2.41/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.41/1.01      | ~ v1_funct_2(X3,X1,X0)
% 2.41/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.41/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.41/1.01      | ~ v2_funct_1(X2)
% 2.41/1.01      | ~ v1_funct_1(X2)
% 2.41/1.01      | ~ v1_funct_1(X3)
% 2.41/1.01      | k2_relset_1(X0,X1,X2) != X1
% 2.41/1.01      | k2_funct_1(X2) = X3
% 2.41/1.01      | k1_xboole_0 = X0
% 2.41/1.01      | k1_xboole_0 = X1 ),
% 2.41/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_20,plain,
% 2.41/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.41/1.01      | ~ v1_funct_2(X3,X1,X0)
% 2.41/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.41/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.41/1.01      | v2_funct_1(X2)
% 2.41/1.01      | ~ v1_funct_1(X2)
% 2.41/1.01      | ~ v1_funct_1(X3) ),
% 2.41/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_167,plain,
% 2.41/1.01      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.41/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.41/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.41/1.01      | ~ v1_funct_2(X3,X1,X0)
% 2.41/1.01      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.41/1.01      | ~ v1_funct_1(X2)
% 2.41/1.01      | ~ v1_funct_1(X3)
% 2.41/1.01      | k2_relset_1(X0,X1,X2) != X1
% 2.41/1.01      | k2_funct_1(X2) = X3
% 2.41/1.01      | k1_xboole_0 = X0
% 2.41/1.01      | k1_xboole_0 = X1 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_21,c_20]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_168,plain,
% 2.41/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.41/1.01      | ~ v1_funct_2(X3,X1,X0)
% 2.41/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.41/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.41/1.01      | ~ v1_funct_1(X2)
% 2.41/1.01      | ~ v1_funct_1(X3)
% 2.41/1.01      | k2_relset_1(X0,X1,X2) != X1
% 2.41/1.01      | k2_funct_1(X2) = X3
% 2.41/1.01      | k1_xboole_0 = X1
% 2.41/1.01      | k1_xboole_0 = X0 ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_167]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1618,plain,
% 2.41/1.01      ( k2_relset_1(X0,X1,X2) != X1
% 2.41/1.01      | k2_funct_1(X2) = X3
% 2.41/1.01      | k1_xboole_0 = X1
% 2.41/1.01      | k1_xboole_0 = X0
% 2.41/1.01      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 2.41/1.01      | v1_funct_2(X3,X1,X0) != iProver_top
% 2.41/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.41/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.41/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 2.41/1.01      | v1_funct_1(X2) != iProver_top
% 2.41/1.01      | v1_funct_1(X3) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_168]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4676,plain,
% 2.41/1.01      ( k2_funct_1(sK1) = X0
% 2.41/1.01      | sK0 = k1_xboole_0
% 2.41/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 2.41/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 2.41/1.01      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.41/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.41/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.41/1.01      | v1_funct_1(X0) != iProver_top
% 2.41/1.01      | v1_funct_1(sK1) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4406,c_1618]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_32,plain,
% 2.41/1.01      ( v1_funct_1(sK1) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_30,negated_conjecture,
% 2.41/1.01      ( v1_funct_2(sK1,sK0,sK0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_33,plain,
% 2.41/1.01      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_35,plain,
% 2.41/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6168,plain,
% 2.41/1.01      ( v1_funct_1(X0) != iProver_top
% 2.41/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 2.41/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 2.41/1.01      | sK0 = k1_xboole_0
% 2.41/1.01      | k2_funct_1(sK1) = X0
% 2.41/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_4676,c_32,c_33,c_35]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6169,plain,
% 2.41/1.01      ( k2_funct_1(sK1) = X0
% 2.41/1.01      | sK0 = k1_xboole_0
% 2.41/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 2.41/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 2.41/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.41/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_6168]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6180,plain,
% 2.41/1.01      ( k2_funct_1(sK1) = sK2
% 2.41/1.01      | sK0 = k1_xboole_0
% 2.41/1.01      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.41/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.41/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1625,c_6169]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_27,negated_conjecture,
% 2.41/1.01      ( v1_funct_1(sK2) ),
% 2.41/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_26,negated_conjecture,
% 2.41/1.01      ( v1_funct_2(sK2,sK0,sK0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_24,negated_conjecture,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.41/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6181,plain,
% 2.41/1.01      ( ~ v1_funct_2(sK2,sK0,sK0)
% 2.41/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.41/1.01      | ~ v1_funct_1(sK2)
% 2.41/1.01      | k2_funct_1(sK1) = sK2
% 2.41/1.01      | sK0 = k1_xboole_0 ),
% 2.41/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6180]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6183,plain,
% 2.41/1.01      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_6180,c_36,c_37,c_39]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6184,plain,
% 2.41/1.01      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_6183]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_22,negated_conjecture,
% 2.41/1.01      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1626,plain,
% 2.41/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_18,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.41/1.01      | ~ v3_funct_2(X0,X1,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_430,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 2.41/1.01      | sK1 != X0
% 2.41/1.01      | sK0 != X1 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_431,plain,
% 2.41/1.01      ( ~ v1_funct_2(sK1,sK0,sK0)
% 2.41/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.41/1.01      | ~ v1_funct_1(sK1)
% 2.41/1.01      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_430]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_433,plain,
% 2.41/1.01      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_431,c_31,c_30,c_28]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1667,plain,
% 2.41/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_1626,c_433]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6187,plain,
% 2.41/1.01      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_6184,c_1667]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_39,plain,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_10,plain,
% 2.41/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 2.41/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.41/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1853,plain,
% 2.41/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 2.41/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1854,plain,
% 2.41/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 2.41/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_1853]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6529,plain,
% 2.41/1.01      ( sK0 = k1_xboole_0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_6187,c_39,c_1854]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2,plain,
% 2.41/1.01      ( ~ v1_relat_1(X0)
% 2.41/1.01      | k2_relat_1(X0) != k1_xboole_0
% 2.41/1.01      | k1_xboole_0 = X0 ),
% 2.41/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1634,plain,
% 2.41/1.01      ( k2_relat_1(X0) != k1_xboole_0
% 2.41/1.01      | k1_xboole_0 = X0
% 2.41/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4407,plain,
% 2.41/1.01      ( sK1 = k1_xboole_0
% 2.41/1.01      | sK0 != k1_xboole_0
% 2.41/1.01      | v1_relat_1(sK1) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4403,c_1634]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1822,plain,
% 2.41/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.41/1.01      | v1_relat_1(sK1) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1823,plain,
% 2.41/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.41/1.01      | v1_relat_1(sK1) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_1822]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5678,plain,
% 2.41/1.01      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_4407,c_35,c_1823]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5679,plain,
% 2.41/1.01      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_5678]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6536,plain,
% 2.41/1.01      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_6529,c_5679]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6643,plain,
% 2.41/1.01      ( sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(equality_resolution_simp,[status(thm)],[c_6536]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1624,plain,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3452,plain,
% 2.41/1.01      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1624,c_1617]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_25,negated_conjecture,
% 2.41/1.01      ( v3_funct_2(sK2,sK0,sK0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_400,plain,
% 2.41/1.01      ( v2_funct_2(X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | sK2 != X0
% 2.41/1.01      | sK0 != X1
% 2.41/1.01      | sK0 != X2 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_401,plain,
% 2.41/1.01      ( v2_funct_2(sK2,sK0)
% 2.41/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.41/1.01      | ~ v1_funct_1(sK2) ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_400]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_403,plain,
% 2.41/1.01      ( v2_funct_2(sK2,sK0) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_401,c_27,c_24]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_479,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | k2_relat_1(X0) = X2
% 2.41/1.01      | sK2 != X0
% 2.41/1.01      | sK0 != X2 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_335,c_403]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_480,plain,
% 2.41/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 2.41/1.01      | k2_relat_1(sK2) = sK0 ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_479]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_482,plain,
% 2.41/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.41/1.01      | k2_relat_1(sK2) = sK0 ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_480]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4386,plain,
% 2.41/1.01      ( k2_relat_1(sK2) = sK0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_3452,c_24,c_482]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4390,plain,
% 2.41/1.01      ( sK2 = k1_xboole_0
% 2.41/1.01      | sK0 != k1_xboole_0
% 2.41/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4386,c_1634]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1819,plain,
% 2.41/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.41/1.01      | v1_relat_1(sK2) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1820,plain,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.41/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_1819]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5583,plain,
% 2.41/1.01      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_4390,c_39,c_1820]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5584,plain,
% 2.41/1.01      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_5583]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6537,plain,
% 2.41/1.01      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_6529,c_5584]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6611,plain,
% 2.41/1.01      ( sK2 = k1_xboole_0 ),
% 2.41/1.01      inference(equality_resolution_simp,[status(thm)],[c_6537]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6548,plain,
% 2.41/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_6529,c_1667]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6619,plain,
% 2.41/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_6611,c_6548]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6645,plain,
% 2.41/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_6643,c_6619]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5,plain,
% 2.41/1.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.41/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3,plain,
% 2.41/1.01      ( ~ v1_relat_1(X0)
% 2.41/1.01      | k1_relat_1(X0) != k1_xboole_0
% 2.41/1.01      | k1_xboole_0 = X0 ),
% 2.41/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1633,plain,
% 2.41/1.01      ( k1_relat_1(X0) != k1_xboole_0
% 2.41/1.01      | k1_xboole_0 = X0
% 2.41/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2832,plain,
% 2.41/1.01      ( k6_partfun1(X0) = k1_xboole_0
% 2.41/1.01      | k1_xboole_0 != X0
% 2.41/1.01      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_5,c_1633]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_17,plain,
% 2.41/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.41/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_54,plain,
% 2.41/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1814,plain,
% 2.41/1.01      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 2.41/1.01      | v1_relat_1(k6_partfun1(X0)) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1815,plain,
% 2.41/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.41/1.01      | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_1814]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2956,plain,
% 2.41/1.01      ( k1_xboole_0 != X0 | k6_partfun1(X0) = k1_xboole_0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_2832,c_54,c_1815]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2957,plain,
% 2.41/1.01      ( k6_partfun1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_2956]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2961,plain,
% 2.41/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.41/1.01      inference(equality_resolution,[status(thm)],[c_2957]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6,plain,
% 2.41/1.01      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2994,plain,
% 2.41/1.01      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2961,c_6]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3001,plain,
% 2.41/1.01      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_2994,c_2961]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6659,plain,
% 2.41/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_6645,c_3001]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1628,plain,
% 2.41/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2993,plain,
% 2.41/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2961,c_1628]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1630,plain,
% 2.41/1.01      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 2.41/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3613,plain,
% 2.41/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2993,c_1630]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(contradiction,plain,
% 2.41/1.01      ( $false ),
% 2.41/1.01      inference(minisat,[status(thm)],[c_6659,c_3613]) ).
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/1.01  
% 2.41/1.01  ------                               Statistics
% 2.41/1.01  
% 2.41/1.01  ------ General
% 2.41/1.01  
% 2.41/1.01  abstr_ref_over_cycles:                  0
% 2.41/1.01  abstr_ref_under_cycles:                 0
% 2.41/1.01  gc_basic_clause_elim:                   0
% 2.41/1.01  forced_gc_time:                         0
% 2.41/1.01  parsing_time:                           0.009
% 2.41/1.01  unif_index_cands_time:                  0.
% 2.41/1.01  unif_index_add_time:                    0.
% 2.41/1.01  orderings_time:                         0.
% 2.41/1.01  out_proof_time:                         0.015
% 2.41/1.01  total_time:                             0.311
% 2.41/1.01  num_of_symbols:                         54
% 2.41/1.01  num_of_terms:                           6704
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing
% 2.41/1.01  
% 2.41/1.01  num_of_splits:                          0
% 2.41/1.01  num_of_split_atoms:                     0
% 2.41/1.01  num_of_reused_defs:                     0
% 2.41/1.01  num_eq_ax_congr_red:                    15
% 2.41/1.01  num_of_sem_filtered_clauses:            3
% 2.41/1.01  num_of_subtypes:                        0
% 2.41/1.01  monotx_restored_types:                  0
% 2.41/1.01  sat_num_of_epr_types:                   0
% 2.41/1.01  sat_num_of_non_cyclic_types:            0
% 2.41/1.01  sat_guarded_non_collapsed_types:        0
% 2.41/1.01  num_pure_diseq_elim:                    0
% 2.41/1.01  simp_replaced_by:                       0
% 2.41/1.01  res_preprocessed:                       148
% 2.41/1.01  prep_upred:                             0
% 2.41/1.01  prep_unflattend:                        66
% 2.41/1.01  smt_new_axioms:                         0
% 2.41/1.01  pred_elim_cands:                        7
% 2.41/1.01  pred_elim:                              2
% 2.41/1.01  pred_elim_cl:                           1
% 2.41/1.01  pred_elim_cycles:                       8
% 2.41/1.01  merged_defs:                            0
% 2.41/1.01  merged_defs_ncl:                        0
% 2.41/1.01  bin_hyper_res:                          0
% 2.41/1.01  prep_cycles:                            4
% 2.41/1.01  pred_elim_time:                         0.017
% 2.41/1.01  splitting_time:                         0.
% 2.41/1.01  sem_filter_time:                        0.
% 2.41/1.01  monotx_time:                            0.
% 2.41/1.01  subtype_inf_time:                       0.
% 2.41/1.01  
% 2.41/1.01  ------ Problem properties
% 2.41/1.01  
% 2.41/1.01  clauses:                                28
% 2.41/1.01  conjectures:                            8
% 2.41/1.01  epr:                                    8
% 2.41/1.01  horn:                                   27
% 2.41/1.01  ground:                                 13
% 2.41/1.01  unary:                                  17
% 2.41/1.01  binary:                                 4
% 2.41/1.01  lits:                                   60
% 2.41/1.01  lits_eq:                                17
% 2.41/1.01  fd_pure:                                0
% 2.41/1.01  fd_pseudo:                              0
% 2.41/1.01  fd_cond:                                2
% 2.41/1.01  fd_pseudo_cond:                         4
% 2.41/1.01  ac_symbols:                             0
% 2.41/1.01  
% 2.41/1.01  ------ Propositional Solver
% 2.41/1.01  
% 2.41/1.01  prop_solver_calls:                      27
% 2.41/1.01  prop_fast_solver_calls:                 1097
% 2.41/1.01  smt_solver_calls:                       0
% 2.41/1.01  smt_fast_solver_calls:                  0
% 2.41/1.01  prop_num_of_clauses:                    2525
% 2.41/1.01  prop_preprocess_simplified:             8369
% 2.41/1.01  prop_fo_subsumed:                       33
% 2.41/1.01  prop_solver_time:                       0.
% 2.41/1.01  smt_solver_time:                        0.
% 2.41/1.01  smt_fast_solver_time:                   0.
% 2.41/1.01  prop_fast_solver_time:                  0.
% 2.41/1.01  prop_unsat_core_time:                   0.
% 2.41/1.01  
% 2.41/1.01  ------ QBF
% 2.41/1.01  
% 2.41/1.01  qbf_q_res:                              0
% 2.41/1.01  qbf_num_tautologies:                    0
% 2.41/1.01  qbf_prep_cycles:                        0
% 2.41/1.01  
% 2.41/1.01  ------ BMC1
% 2.41/1.01  
% 2.41/1.01  bmc1_current_bound:                     -1
% 2.41/1.01  bmc1_last_solved_bound:                 -1
% 2.41/1.01  bmc1_unsat_core_size:                   -1
% 2.41/1.01  bmc1_unsat_core_parents_size:           -1
% 2.41/1.01  bmc1_merge_next_fun:                    0
% 2.41/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.41/1.01  
% 2.41/1.01  ------ Instantiation
% 2.41/1.01  
% 2.41/1.01  inst_num_of_clauses:                    761
% 2.41/1.01  inst_num_in_passive:                    428
% 2.41/1.01  inst_num_in_active:                     333
% 2.41/1.01  inst_num_in_unprocessed:                0
% 2.41/1.01  inst_num_of_loops:                      340
% 2.41/1.01  inst_num_of_learning_restarts:          0
% 2.41/1.01  inst_num_moves_active_passive:          6
% 2.41/1.01  inst_lit_activity:                      0
% 2.41/1.01  inst_lit_activity_moves:                0
% 2.41/1.01  inst_num_tautologies:                   0
% 2.41/1.01  inst_num_prop_implied:                  0
% 2.41/1.01  inst_num_existing_simplified:           0
% 2.41/1.01  inst_num_eq_res_simplified:             0
% 2.41/1.01  inst_num_child_elim:                    0
% 2.41/1.01  inst_num_of_dismatching_blockings:      76
% 2.41/1.01  inst_num_of_non_proper_insts:           619
% 2.41/1.01  inst_num_of_duplicates:                 0
% 2.41/1.01  inst_inst_num_from_inst_to_res:         0
% 2.41/1.01  inst_dismatching_checking_time:         0.
% 2.41/1.01  
% 2.41/1.01  ------ Resolution
% 2.41/1.01  
% 2.41/1.01  res_num_of_clauses:                     0
% 2.41/1.01  res_num_in_passive:                     0
% 2.41/1.01  res_num_in_active:                      0
% 2.41/1.01  res_num_of_loops:                       152
% 2.41/1.01  res_forward_subset_subsumed:            36
% 2.41/1.01  res_backward_subset_subsumed:           0
% 2.41/1.01  res_forward_subsumed:                   0
% 2.41/1.01  res_backward_subsumed:                  0
% 2.41/1.01  res_forward_subsumption_resolution:     2
% 2.41/1.01  res_backward_subsumption_resolution:    0
% 2.41/1.01  res_clause_to_clause_subsumption:       150
% 2.41/1.01  res_orphan_elimination:                 0
% 2.41/1.01  res_tautology_del:                      30
% 2.41/1.01  res_num_eq_res_simplified:              0
% 2.41/1.01  res_num_sel_changes:                    0
% 2.41/1.01  res_moves_from_active_to_pass:          0
% 2.41/1.01  
% 2.41/1.01  ------ Superposition
% 2.41/1.01  
% 2.41/1.01  sup_time_total:                         0.
% 2.41/1.01  sup_time_generating:                    0.
% 2.41/1.01  sup_time_sim_full:                      0.
% 2.41/1.01  sup_time_sim_immed:                     0.
% 2.41/1.01  
% 2.41/1.01  sup_num_of_clauses:                     48
% 2.41/1.01  sup_num_in_active:                      36
% 2.41/1.01  sup_num_in_passive:                     12
% 2.41/1.01  sup_num_of_loops:                       66
% 2.41/1.01  sup_fw_superposition:                   45
% 2.41/1.01  sup_bw_superposition:                   15
% 2.41/1.01  sup_immediate_simplified:               45
% 2.41/1.01  sup_given_eliminated:                   0
% 2.41/1.01  comparisons_done:                       0
% 2.41/1.01  comparisons_avoided:                    3
% 2.41/1.01  
% 2.41/1.01  ------ Simplifications
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  sim_fw_subset_subsumed:                 5
% 2.41/1.01  sim_bw_subset_subsumed:                 7
% 2.41/1.01  sim_fw_subsumed:                        2
% 2.41/1.01  sim_bw_subsumed:                        0
% 2.41/1.01  sim_fw_subsumption_res:                 0
% 2.41/1.01  sim_bw_subsumption_res:                 0
% 2.41/1.01  sim_tautology_del:                      0
% 2.41/1.01  sim_eq_tautology_del:                   6
% 2.41/1.01  sim_eq_res_simp:                        2
% 2.41/1.01  sim_fw_demodulated:                     2
% 2.41/1.01  sim_bw_demodulated:                     50
% 2.41/1.01  sim_light_normalised:                   15
% 2.41/1.01  sim_joinable_taut:                      0
% 2.41/1.01  sim_joinable_simp:                      0
% 2.41/1.01  sim_ac_normalised:                      0
% 2.41/1.01  sim_smt_subsumption:                    0
% 2.41/1.01  
%------------------------------------------------------------------------------
