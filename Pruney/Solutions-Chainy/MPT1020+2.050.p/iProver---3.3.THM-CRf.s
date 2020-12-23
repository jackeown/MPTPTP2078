%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:15 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_39)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f51,f50])).

fof(f87,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f39])).

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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f63,f75,f75])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1568,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1564,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1573,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4056,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1564,c_1573])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_19,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_415,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_416,plain,
    ( v2_funct_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_418,plain,
    ( v2_funct_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_34,c_31])).

cnf(c_501,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_418])).

cnf(c_502,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1
    | sK2 != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_502])).

cnf(c_549,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_551,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_553,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_31,c_551])).

cnf(c_1557,plain,
    ( k2_relat_1(sK2) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_87,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1755,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1943,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_2333,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1557,c_31,c_87,c_551,c_1943])).

cnf(c_4068,plain,
    ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4056,c_2333])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f78])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

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
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_23])).

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
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_1561,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_4919,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4068,c_1561])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5223,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0
    | k2_funct_1(sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4919,c_35,c_36,c_38])).

cnf(c_5224,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5223])).

cnf(c_5235,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_5224])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5236,plain,
    ( ~ v1_funct_2(sK3,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5235])).

cnf(c_5259,plain,
    ( sK1 = k1_xboole_0
    | k2_funct_1(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5235,c_39,c_40,c_42])).

cnf(c_5260,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5259])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1569,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_434,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_435,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_437,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_34,c_33,c_31])).

cnf(c_1614,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1569,c_437])).

cnf(c_5263,plain,
    ( sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5260,c_1614])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1788,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1789,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_5266,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5263,c_42,c_1789])).

cnf(c_5287,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5266,c_1564])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5301,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5287,c_5])).

cnf(c_1567,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1571,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4591,plain,
    ( sK3 = X0
    | r2_relset_1(sK1,sK1,sK3,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1571])).

cnf(c_5276,plain,
    ( sK3 = X0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5266,c_4591])).

cnf(c_5333,plain,
    ( sK3 = X0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5276,c_5])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_99,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_4570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_4571,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4570])).

cnf(c_1560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_4206,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1560])).

cnf(c_5278,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5266,c_4206])).

cnf(c_5322,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5278,c_5])).

cnf(c_5579,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5322,c_99])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1576,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5585,plain,
    ( sK3 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5579,c_1576])).

cnf(c_6402,plain,
    ( sK3 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5333,c_99,c_4571,c_5585])).

cnf(c_6411,plain,
    ( sK2 = sK3 ),
    inference(superposition,[status(thm)],[c_5301,c_6402])).

cnf(c_5284,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5266,c_1614])).

cnf(c_6579,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6411,c_5284])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1570,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2884,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1570])).

cnf(c_6410,plain,
    ( k6_partfun1(k1_xboole_0) = sK3 ),
    inference(superposition,[status(thm)],[c_2884,c_6402])).

cnf(c_10,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_6601,plain,
    ( k2_funct_1(sK3) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6410,c_10])).

cnf(c_6622,plain,
    ( k2_funct_1(sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_6601,c_6410])).

cnf(c_7439,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6579,c_6622])).

cnf(c_1572,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3040,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1572])).

cnf(c_5281,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5266,c_3040])).

cnf(c_7441,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7439,c_5281])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.08/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/0.99  
% 3.08/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.08/0.99  
% 3.08/0.99  ------  iProver source info
% 3.08/0.99  
% 3.08/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.08/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.08/0.99  git: non_committed_changes: false
% 3.08/0.99  git: last_make_outside_of_git: false
% 3.08/0.99  
% 3.08/0.99  ------ 
% 3.08/0.99  
% 3.08/0.99  ------ Input Options
% 3.08/0.99  
% 3.08/0.99  --out_options                           all
% 3.08/0.99  --tptp_safe_out                         true
% 3.08/0.99  --problem_path                          ""
% 3.08/0.99  --include_path                          ""
% 3.08/0.99  --clausifier                            res/vclausify_rel
% 3.08/0.99  --clausifier_options                    --mode clausify
% 3.08/0.99  --stdin                                 false
% 3.08/0.99  --stats_out                             all
% 3.08/0.99  
% 3.08/0.99  ------ General Options
% 3.08/0.99  
% 3.08/0.99  --fof                                   false
% 3.08/0.99  --time_out_real                         305.
% 3.08/0.99  --time_out_virtual                      -1.
% 3.08/0.99  --symbol_type_check                     false
% 3.08/0.99  --clausify_out                          false
% 3.08/0.99  --sig_cnt_out                           false
% 3.08/0.99  --trig_cnt_out                          false
% 3.08/0.99  --trig_cnt_out_tolerance                1.
% 3.08/0.99  --trig_cnt_out_sk_spl                   false
% 3.08/0.99  --abstr_cl_out                          false
% 3.08/0.99  
% 3.08/0.99  ------ Global Options
% 3.08/0.99  
% 3.08/0.99  --schedule                              default
% 3.08/0.99  --add_important_lit                     false
% 3.08/0.99  --prop_solver_per_cl                    1000
% 3.08/0.99  --min_unsat_core                        false
% 3.08/0.99  --soft_assumptions                      false
% 3.08/0.99  --soft_lemma_size                       3
% 3.08/0.99  --prop_impl_unit_size                   0
% 3.08/0.99  --prop_impl_unit                        []
% 3.08/0.99  --share_sel_clauses                     true
% 3.08/0.99  --reset_solvers                         false
% 3.08/0.99  --bc_imp_inh                            [conj_cone]
% 3.08/0.99  --conj_cone_tolerance                   3.
% 3.08/0.99  --extra_neg_conj                        none
% 3.08/0.99  --large_theory_mode                     true
% 3.08/0.99  --prolific_symb_bound                   200
% 3.08/0.99  --lt_threshold                          2000
% 3.08/0.99  --clause_weak_htbl                      true
% 3.08/0.99  --gc_record_bc_elim                     false
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing Options
% 3.08/0.99  
% 3.08/0.99  --preprocessing_flag                    true
% 3.08/0.99  --time_out_prep_mult                    0.1
% 3.08/0.99  --splitting_mode                        input
% 3.08/0.99  --splitting_grd                         true
% 3.08/0.99  --splitting_cvd                         false
% 3.08/0.99  --splitting_cvd_svl                     false
% 3.08/0.99  --splitting_nvd                         32
% 3.08/0.99  --sub_typing                            true
% 3.08/0.99  --prep_gs_sim                           true
% 3.08/0.99  --prep_unflatten                        true
% 3.08/0.99  --prep_res_sim                          true
% 3.08/0.99  --prep_upred                            true
% 3.08/0.99  --prep_sem_filter                       exhaustive
% 3.08/0.99  --prep_sem_filter_out                   false
% 3.08/0.99  --pred_elim                             true
% 3.08/0.99  --res_sim_input                         true
% 3.08/0.99  --eq_ax_congr_red                       true
% 3.08/0.99  --pure_diseq_elim                       true
% 3.08/0.99  --brand_transform                       false
% 3.08/0.99  --non_eq_to_eq                          false
% 3.08/0.99  --prep_def_merge                        true
% 3.08/0.99  --prep_def_merge_prop_impl              false
% 3.08/0.99  --prep_def_merge_mbd                    true
% 3.08/0.99  --prep_def_merge_tr_red                 false
% 3.08/0.99  --prep_def_merge_tr_cl                  false
% 3.08/0.99  --smt_preprocessing                     true
% 3.08/0.99  --smt_ac_axioms                         fast
% 3.08/0.99  --preprocessed_out                      false
% 3.08/0.99  --preprocessed_stats                    false
% 3.08/0.99  
% 3.08/0.99  ------ Abstraction refinement Options
% 3.08/0.99  
% 3.08/0.99  --abstr_ref                             []
% 3.08/0.99  --abstr_ref_prep                        false
% 3.08/0.99  --abstr_ref_until_sat                   false
% 3.08/0.99  --abstr_ref_sig_restrict                funpre
% 3.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/0.99  --abstr_ref_under                       []
% 3.08/0.99  
% 3.08/0.99  ------ SAT Options
% 3.08/0.99  
% 3.08/0.99  --sat_mode                              false
% 3.08/0.99  --sat_fm_restart_options                ""
% 3.08/0.99  --sat_gr_def                            false
% 3.08/0.99  --sat_epr_types                         true
% 3.08/0.99  --sat_non_cyclic_types                  false
% 3.08/0.99  --sat_finite_models                     false
% 3.08/0.99  --sat_fm_lemmas                         false
% 3.08/0.99  --sat_fm_prep                           false
% 3.08/0.99  --sat_fm_uc_incr                        true
% 3.08/0.99  --sat_out_model                         small
% 3.08/0.99  --sat_out_clauses                       false
% 3.08/0.99  
% 3.08/0.99  ------ QBF Options
% 3.08/0.99  
% 3.08/0.99  --qbf_mode                              false
% 3.08/0.99  --qbf_elim_univ                         false
% 3.08/0.99  --qbf_dom_inst                          none
% 3.08/0.99  --qbf_dom_pre_inst                      false
% 3.08/0.99  --qbf_sk_in                             false
% 3.08/0.99  --qbf_pred_elim                         true
% 3.08/0.99  --qbf_split                             512
% 3.08/0.99  
% 3.08/0.99  ------ BMC1 Options
% 3.08/0.99  
% 3.08/0.99  --bmc1_incremental                      false
% 3.08/0.99  --bmc1_axioms                           reachable_all
% 3.08/0.99  --bmc1_min_bound                        0
% 3.08/0.99  --bmc1_max_bound                        -1
% 3.08/0.99  --bmc1_max_bound_default                -1
% 3.08/0.99  --bmc1_symbol_reachability              true
% 3.08/0.99  --bmc1_property_lemmas                  false
% 3.08/0.99  --bmc1_k_induction                      false
% 3.08/0.99  --bmc1_non_equiv_states                 false
% 3.08/0.99  --bmc1_deadlock                         false
% 3.08/0.99  --bmc1_ucm                              false
% 3.08/0.99  --bmc1_add_unsat_core                   none
% 3.08/0.99  --bmc1_unsat_core_children              false
% 3.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/0.99  --bmc1_out_stat                         full
% 3.08/0.99  --bmc1_ground_init                      false
% 3.08/0.99  --bmc1_pre_inst_next_state              false
% 3.08/0.99  --bmc1_pre_inst_state                   false
% 3.08/0.99  --bmc1_pre_inst_reach_state             false
% 3.08/0.99  --bmc1_out_unsat_core                   false
% 3.08/0.99  --bmc1_aig_witness_out                  false
% 3.08/0.99  --bmc1_verbose                          false
% 3.08/0.99  --bmc1_dump_clauses_tptp                false
% 3.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.08/0.99  --bmc1_dump_file                        -
% 3.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.08/0.99  --bmc1_ucm_extend_mode                  1
% 3.08/0.99  --bmc1_ucm_init_mode                    2
% 3.08/0.99  --bmc1_ucm_cone_mode                    none
% 3.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.08/0.99  --bmc1_ucm_relax_model                  4
% 3.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/0.99  --bmc1_ucm_layered_model                none
% 3.08/0.99  --bmc1_ucm_max_lemma_size               10
% 3.08/0.99  
% 3.08/0.99  ------ AIG Options
% 3.08/0.99  
% 3.08/0.99  --aig_mode                              false
% 3.08/0.99  
% 3.08/0.99  ------ Instantiation Options
% 3.08/0.99  
% 3.08/0.99  --instantiation_flag                    true
% 3.08/0.99  --inst_sos_flag                         false
% 3.08/0.99  --inst_sos_phase                        true
% 3.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/0.99  --inst_lit_sel_side                     num_symb
% 3.08/0.99  --inst_solver_per_active                1400
% 3.08/0.99  --inst_solver_calls_frac                1.
% 3.08/0.99  --inst_passive_queue_type               priority_queues
% 3.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/0.99  --inst_passive_queues_freq              [25;2]
% 3.08/0.99  --inst_dismatching                      true
% 3.08/0.99  --inst_eager_unprocessed_to_passive     true
% 3.08/0.99  --inst_prop_sim_given                   true
% 3.08/0.99  --inst_prop_sim_new                     false
% 3.08/0.99  --inst_subs_new                         false
% 3.08/0.99  --inst_eq_res_simp                      false
% 3.08/0.99  --inst_subs_given                       false
% 3.08/0.99  --inst_orphan_elimination               true
% 3.08/0.99  --inst_learning_loop_flag               true
% 3.08/0.99  --inst_learning_start                   3000
% 3.08/0.99  --inst_learning_factor                  2
% 3.08/0.99  --inst_start_prop_sim_after_learn       3
% 3.08/0.99  --inst_sel_renew                        solver
% 3.08/0.99  --inst_lit_activity_flag                true
% 3.08/0.99  --inst_restr_to_given                   false
% 3.08/0.99  --inst_activity_threshold               500
% 3.08/0.99  --inst_out_proof                        true
% 3.08/0.99  
% 3.08/0.99  ------ Resolution Options
% 3.08/0.99  
% 3.08/0.99  --resolution_flag                       true
% 3.08/0.99  --res_lit_sel                           adaptive
% 3.08/0.99  --res_lit_sel_side                      none
% 3.08/0.99  --res_ordering                          kbo
% 3.08/0.99  --res_to_prop_solver                    active
% 3.08/0.99  --res_prop_simpl_new                    false
% 3.08/0.99  --res_prop_simpl_given                  true
% 3.08/0.99  --res_passive_queue_type                priority_queues
% 3.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/0.99  --res_passive_queues_freq               [15;5]
% 3.08/0.99  --res_forward_subs                      full
% 3.08/0.99  --res_backward_subs                     full
% 3.08/0.99  --res_forward_subs_resolution           true
% 3.08/0.99  --res_backward_subs_resolution          true
% 3.08/0.99  --res_orphan_elimination                true
% 3.08/0.99  --res_time_limit                        2.
% 3.08/0.99  --res_out_proof                         true
% 3.08/0.99  
% 3.08/0.99  ------ Superposition Options
% 3.08/0.99  
% 3.08/0.99  --superposition_flag                    true
% 3.08/0.99  --sup_passive_queue_type                priority_queues
% 3.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.08/0.99  --demod_completeness_check              fast
% 3.08/0.99  --demod_use_ground                      true
% 3.08/0.99  --sup_to_prop_solver                    passive
% 3.08/0.99  --sup_prop_simpl_new                    true
% 3.08/0.99  --sup_prop_simpl_given                  true
% 3.08/0.99  --sup_fun_splitting                     false
% 3.08/0.99  --sup_smt_interval                      50000
% 3.08/0.99  
% 3.08/0.99  ------ Superposition Simplification Setup
% 3.08/0.99  
% 3.08/0.99  --sup_indices_passive                   []
% 3.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.99  --sup_full_bw                           [BwDemod]
% 3.08/0.99  --sup_immed_triv                        [TrivRules]
% 3.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.99  --sup_immed_bw_main                     []
% 3.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.99  
% 3.08/0.99  ------ Combination Options
% 3.08/0.99  
% 3.08/0.99  --comb_res_mult                         3
% 3.08/0.99  --comb_sup_mult                         2
% 3.08/0.99  --comb_inst_mult                        10
% 3.08/0.99  
% 3.08/0.99  ------ Debug Options
% 3.08/0.99  
% 3.08/0.99  --dbg_backtrace                         false
% 3.08/0.99  --dbg_dump_prop_clauses                 false
% 3.08/0.99  --dbg_dump_prop_clauses_file            -
% 3.08/0.99  --dbg_out_stat                          false
% 3.08/0.99  ------ Parsing...
% 3.08/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.08/0.99  ------ Proving...
% 3.08/0.99  ------ Problem Properties 
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  clauses                                 27
% 3.08/0.99  conjectures                             8
% 3.08/0.99  EPR                                     6
% 3.08/0.99  Horn                                    25
% 3.08/0.99  unary                                   16
% 3.08/0.99  binary                                  4
% 3.08/0.99  lits                                    60
% 3.08/0.99  lits eq                                 18
% 3.08/0.99  fd_pure                                 0
% 3.08/0.99  fd_pseudo                               0
% 3.08/0.99  fd_cond                                 1
% 3.08/0.99  fd_pseudo_cond                          4
% 3.08/0.99  AC symbols                              0
% 3.08/0.99  
% 3.08/0.99  ------ Schedule dynamic 5 is on 
% 3.08/0.99  
% 3.08/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  ------ 
% 3.08/0.99  Current options:
% 3.08/0.99  ------ 
% 3.08/0.99  
% 3.08/0.99  ------ Input Options
% 3.08/0.99  
% 3.08/0.99  --out_options                           all
% 3.08/0.99  --tptp_safe_out                         true
% 3.08/0.99  --problem_path                          ""
% 3.08/0.99  --include_path                          ""
% 3.08/0.99  --clausifier                            res/vclausify_rel
% 3.08/0.99  --clausifier_options                    --mode clausify
% 3.08/0.99  --stdin                                 false
% 3.08/0.99  --stats_out                             all
% 3.08/0.99  
% 3.08/0.99  ------ General Options
% 3.08/0.99  
% 3.08/0.99  --fof                                   false
% 3.08/0.99  --time_out_real                         305.
% 3.08/0.99  --time_out_virtual                      -1.
% 3.08/0.99  --symbol_type_check                     false
% 3.08/0.99  --clausify_out                          false
% 3.08/0.99  --sig_cnt_out                           false
% 3.08/0.99  --trig_cnt_out                          false
% 3.08/0.99  --trig_cnt_out_tolerance                1.
% 3.08/0.99  --trig_cnt_out_sk_spl                   false
% 3.08/0.99  --abstr_cl_out                          false
% 3.08/0.99  
% 3.08/0.99  ------ Global Options
% 3.08/0.99  
% 3.08/0.99  --schedule                              default
% 3.08/0.99  --add_important_lit                     false
% 3.08/0.99  --prop_solver_per_cl                    1000
% 3.08/0.99  --min_unsat_core                        false
% 3.08/0.99  --soft_assumptions                      false
% 3.08/0.99  --soft_lemma_size                       3
% 3.08/0.99  --prop_impl_unit_size                   0
% 3.08/0.99  --prop_impl_unit                        []
% 3.08/0.99  --share_sel_clauses                     true
% 3.08/0.99  --reset_solvers                         false
% 3.08/0.99  --bc_imp_inh                            [conj_cone]
% 3.08/0.99  --conj_cone_tolerance                   3.
% 3.08/0.99  --extra_neg_conj                        none
% 3.08/0.99  --large_theory_mode                     true
% 3.08/0.99  --prolific_symb_bound                   200
% 3.08/0.99  --lt_threshold                          2000
% 3.08/0.99  --clause_weak_htbl                      true
% 3.08/0.99  --gc_record_bc_elim                     false
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing Options
% 3.08/0.99  
% 3.08/0.99  --preprocessing_flag                    true
% 3.08/0.99  --time_out_prep_mult                    0.1
% 3.08/0.99  --splitting_mode                        input
% 3.08/0.99  --splitting_grd                         true
% 3.08/0.99  --splitting_cvd                         false
% 3.08/0.99  --splitting_cvd_svl                     false
% 3.08/0.99  --splitting_nvd                         32
% 3.08/0.99  --sub_typing                            true
% 3.08/0.99  --prep_gs_sim                           true
% 3.08/0.99  --prep_unflatten                        true
% 3.08/0.99  --prep_res_sim                          true
% 3.08/0.99  --prep_upred                            true
% 3.08/0.99  --prep_sem_filter                       exhaustive
% 3.08/0.99  --prep_sem_filter_out                   false
% 3.08/0.99  --pred_elim                             true
% 3.08/0.99  --res_sim_input                         true
% 3.08/0.99  --eq_ax_congr_red                       true
% 3.08/0.99  --pure_diseq_elim                       true
% 3.08/0.99  --brand_transform                       false
% 3.08/0.99  --non_eq_to_eq                          false
% 3.08/0.99  --prep_def_merge                        true
% 3.08/0.99  --prep_def_merge_prop_impl              false
% 3.08/0.99  --prep_def_merge_mbd                    true
% 3.08/0.99  --prep_def_merge_tr_red                 false
% 3.08/0.99  --prep_def_merge_tr_cl                  false
% 3.08/0.99  --smt_preprocessing                     true
% 3.08/0.99  --smt_ac_axioms                         fast
% 3.08/0.99  --preprocessed_out                      false
% 3.08/0.99  --preprocessed_stats                    false
% 3.08/0.99  
% 3.08/0.99  ------ Abstraction refinement Options
% 3.08/0.99  
% 3.08/0.99  --abstr_ref                             []
% 3.08/0.99  --abstr_ref_prep                        false
% 3.08/0.99  --abstr_ref_until_sat                   false
% 3.08/0.99  --abstr_ref_sig_restrict                funpre
% 3.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/0.99  --abstr_ref_under                       []
% 3.08/0.99  
% 3.08/0.99  ------ SAT Options
% 3.08/0.99  
% 3.08/0.99  --sat_mode                              false
% 3.08/0.99  --sat_fm_restart_options                ""
% 3.08/0.99  --sat_gr_def                            false
% 3.08/0.99  --sat_epr_types                         true
% 3.08/0.99  --sat_non_cyclic_types                  false
% 3.08/0.99  --sat_finite_models                     false
% 3.08/0.99  --sat_fm_lemmas                         false
% 3.08/0.99  --sat_fm_prep                           false
% 3.08/0.99  --sat_fm_uc_incr                        true
% 3.08/0.99  --sat_out_model                         small
% 3.08/0.99  --sat_out_clauses                       false
% 3.08/0.99  
% 3.08/0.99  ------ QBF Options
% 3.08/0.99  
% 3.08/0.99  --qbf_mode                              false
% 3.08/0.99  --qbf_elim_univ                         false
% 3.08/0.99  --qbf_dom_inst                          none
% 3.08/0.99  --qbf_dom_pre_inst                      false
% 3.08/0.99  --qbf_sk_in                             false
% 3.08/0.99  --qbf_pred_elim                         true
% 3.08/0.99  --qbf_split                             512
% 3.08/0.99  
% 3.08/0.99  ------ BMC1 Options
% 3.08/0.99  
% 3.08/0.99  --bmc1_incremental                      false
% 3.08/0.99  --bmc1_axioms                           reachable_all
% 3.08/0.99  --bmc1_min_bound                        0
% 3.08/0.99  --bmc1_max_bound                        -1
% 3.08/0.99  --bmc1_max_bound_default                -1
% 3.08/0.99  --bmc1_symbol_reachability              true
% 3.08/0.99  --bmc1_property_lemmas                  false
% 3.08/0.99  --bmc1_k_induction                      false
% 3.08/0.99  --bmc1_non_equiv_states                 false
% 3.08/0.99  --bmc1_deadlock                         false
% 3.08/0.99  --bmc1_ucm                              false
% 3.08/0.99  --bmc1_add_unsat_core                   none
% 3.08/0.99  --bmc1_unsat_core_children              false
% 3.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/0.99  --bmc1_out_stat                         full
% 3.08/0.99  --bmc1_ground_init                      false
% 3.08/0.99  --bmc1_pre_inst_next_state              false
% 3.08/0.99  --bmc1_pre_inst_state                   false
% 3.08/0.99  --bmc1_pre_inst_reach_state             false
% 3.08/0.99  --bmc1_out_unsat_core                   false
% 3.08/0.99  --bmc1_aig_witness_out                  false
% 3.08/0.99  --bmc1_verbose                          false
% 3.08/0.99  --bmc1_dump_clauses_tptp                false
% 3.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.08/0.99  --bmc1_dump_file                        -
% 3.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.08/0.99  --bmc1_ucm_extend_mode                  1
% 3.08/0.99  --bmc1_ucm_init_mode                    2
% 3.08/0.99  --bmc1_ucm_cone_mode                    none
% 3.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.08/0.99  --bmc1_ucm_relax_model                  4
% 3.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/0.99  --bmc1_ucm_layered_model                none
% 3.08/0.99  --bmc1_ucm_max_lemma_size               10
% 3.08/0.99  
% 3.08/0.99  ------ AIG Options
% 3.08/0.99  
% 3.08/0.99  --aig_mode                              false
% 3.08/0.99  
% 3.08/0.99  ------ Instantiation Options
% 3.08/0.99  
% 3.08/0.99  --instantiation_flag                    true
% 3.08/0.99  --inst_sos_flag                         false
% 3.08/0.99  --inst_sos_phase                        true
% 3.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/0.99  --inst_lit_sel_side                     none
% 3.08/0.99  --inst_solver_per_active                1400
% 3.08/0.99  --inst_solver_calls_frac                1.
% 3.08/0.99  --inst_passive_queue_type               priority_queues
% 3.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
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
% 3.08/1.00   Resolution empty clause
% 3.08/1.00  
% 3.08/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.08/1.00  
% 3.08/1.00  fof(f19,conjecture,(
% 3.08/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f20,negated_conjecture,(
% 3.08/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.08/1.00    inference(negated_conjecture,[],[f19])).
% 3.08/1.00  
% 3.08/1.00  fof(f40,plain,(
% 3.08/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.08/1.00    inference(ennf_transformation,[],[f20])).
% 3.08/1.00  
% 3.08/1.00  fof(f41,plain,(
% 3.08/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.08/1.00    inference(flattening,[],[f40])).
% 3.08/1.00  
% 3.08/1.00  fof(f51,plain,(
% 3.08/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK3,X0,X0) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 3.08/1.00    introduced(choice_axiom,[])).
% 3.08/1.00  
% 3.08/1.00  fof(f50,plain,(
% 3.08/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(X2,sK1,sK1) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.08/1.00    introduced(choice_axiom,[])).
% 3.08/1.00  
% 3.08/1.00  fof(f52,plain,(
% 3.08/1.00    (~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.08/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f51,f50])).
% 3.08/1.00  
% 3.08/1.00  fof(f87,plain,(
% 3.08/1.00    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))),
% 3.08/1.00    inference(cnf_transformation,[],[f52])).
% 3.08/1.00  
% 3.08/1.00  fof(f82,plain,(
% 3.08/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.08/1.00    inference(cnf_transformation,[],[f52])).
% 3.08/1.00  
% 3.08/1.00  fof(f10,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f27,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(ennf_transformation,[],[f10])).
% 3.08/1.00  
% 3.08/1.00  fof(f65,plain,(
% 3.08/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f27])).
% 3.08/1.00  
% 3.08/1.00  fof(f9,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f22,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.08/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.08/1.00  
% 3.08/1.00  fof(f26,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(ennf_transformation,[],[f22])).
% 3.08/1.00  
% 3.08/1.00  fof(f64,plain,(
% 3.08/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f26])).
% 3.08/1.00  
% 3.08/1.00  fof(f13,axiom,(
% 3.08/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f32,plain,(
% 3.08/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.08/1.00    inference(ennf_transformation,[],[f13])).
% 3.08/1.00  
% 3.08/1.00  fof(f33,plain,(
% 3.08/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.08/1.00    inference(flattening,[],[f32])).
% 3.08/1.00  
% 3.08/1.00  fof(f49,plain,(
% 3.08/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.08/1.00    inference(nnf_transformation,[],[f33])).
% 3.08/1.00  
% 3.08/1.00  fof(f71,plain,(
% 3.08/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f49])).
% 3.08/1.00  
% 3.08/1.00  fof(f12,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f30,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(ennf_transformation,[],[f12])).
% 3.08/1.00  
% 3.08/1.00  fof(f31,plain,(
% 3.08/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(flattening,[],[f30])).
% 3.08/1.00  
% 3.08/1.00  fof(f70,plain,(
% 3.08/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f31])).
% 3.08/1.00  
% 3.08/1.00  fof(f81,plain,(
% 3.08/1.00    v3_funct_2(sK2,sK1,sK1)),
% 3.08/1.00    inference(cnf_transformation,[],[f52])).
% 3.08/1.00  
% 3.08/1.00  fof(f79,plain,(
% 3.08/1.00    v1_funct_1(sK2)),
% 3.08/1.00    inference(cnf_transformation,[],[f52])).
% 3.08/1.00  
% 3.08/1.00  fof(f7,axiom,(
% 3.08/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f62,plain,(
% 3.08/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f7])).
% 3.08/1.00  
% 3.08/1.00  fof(f6,axiom,(
% 3.08/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f25,plain,(
% 3.08/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.08/1.00    inference(ennf_transformation,[],[f6])).
% 3.08/1.00  
% 3.08/1.00  fof(f61,plain,(
% 3.08/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f25])).
% 3.08/1.00  
% 3.08/1.00  fof(f18,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f38,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.08/1.00    inference(ennf_transformation,[],[f18])).
% 3.08/1.00  
% 3.08/1.00  fof(f39,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.08/1.00    inference(flattening,[],[f38])).
% 3.08/1.00  
% 3.08/1.00  fof(f78,plain,(
% 3.08/1.00    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f39])).
% 3.08/1.00  
% 3.08/1.00  fof(f17,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f36,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.08/1.00    inference(ennf_transformation,[],[f17])).
% 3.08/1.00  
% 3.08/1.00  fof(f37,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.08/1.00    inference(flattening,[],[f36])).
% 3.08/1.00  
% 3.08/1.00  fof(f76,plain,(
% 3.08/1.00    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f37])).
% 3.08/1.00  
% 3.08/1.00  fof(f80,plain,(
% 3.08/1.00    v1_funct_2(sK2,sK1,sK1)),
% 3.08/1.00    inference(cnf_transformation,[],[f52])).
% 3.08/1.00  
% 3.08/1.00  fof(f83,plain,(
% 3.08/1.00    v1_funct_1(sK3)),
% 3.08/1.00    inference(cnf_transformation,[],[f52])).
% 3.08/1.00  
% 3.08/1.00  fof(f84,plain,(
% 3.08/1.00    v1_funct_2(sK3,sK1,sK1)),
% 3.08/1.00    inference(cnf_transformation,[],[f52])).
% 3.08/1.00  
% 3.08/1.00  fof(f86,plain,(
% 3.08/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.08/1.00    inference(cnf_transformation,[],[f52])).
% 3.08/1.00  
% 3.08/1.00  fof(f88,plain,(
% 3.08/1.00    ~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))),
% 3.08/1.00    inference(cnf_transformation,[],[f52])).
% 3.08/1.00  
% 3.08/1.00  fof(f15,axiom,(
% 3.08/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f34,plain,(
% 3.08/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.08/1.00    inference(ennf_transformation,[],[f15])).
% 3.08/1.00  
% 3.08/1.00  fof(f35,plain,(
% 3.08/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.08/1.00    inference(flattening,[],[f34])).
% 3.08/1.00  
% 3.08/1.00  fof(f74,plain,(
% 3.08/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f35])).
% 3.08/1.00  
% 3.08/1.00  fof(f11,axiom,(
% 3.08/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f28,plain,(
% 3.08/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.08/1.00    inference(ennf_transformation,[],[f11])).
% 3.08/1.00  
% 3.08/1.00  fof(f29,plain,(
% 3.08/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(flattening,[],[f28])).
% 3.08/1.00  
% 3.08/1.00  fof(f48,plain,(
% 3.08/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.00    inference(nnf_transformation,[],[f29])).
% 3.08/1.00  
% 3.08/1.00  fof(f67,plain,(
% 3.08/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f92,plain,(
% 3.08/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(equality_resolution,[],[f67])).
% 3.08/1.00  
% 3.08/1.00  fof(f4,axiom,(
% 3.08/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f46,plain,(
% 3.08/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.08/1.00    inference(nnf_transformation,[],[f4])).
% 3.08/1.00  
% 3.08/1.00  fof(f47,plain,(
% 3.08/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.08/1.00    inference(flattening,[],[f46])).
% 3.08/1.00  
% 3.08/1.00  fof(f58,plain,(
% 3.08/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.08/1.00    inference(cnf_transformation,[],[f47])).
% 3.08/1.00  
% 3.08/1.00  fof(f91,plain,(
% 3.08/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.08/1.00    inference(equality_resolution,[],[f58])).
% 3.08/1.00  
% 3.08/1.00  fof(f66,plain,(
% 3.08/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f48])).
% 3.08/1.00  
% 3.08/1.00  fof(f2,axiom,(
% 3.08/1.00    v1_xboole_0(k1_xboole_0)),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f55,plain,(
% 3.08/1.00    v1_xboole_0(k1_xboole_0)),
% 3.08/1.00    inference(cnf_transformation,[],[f2])).
% 3.08/1.00  
% 3.08/1.00  fof(f1,axiom,(
% 3.08/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f42,plain,(
% 3.08/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.08/1.00    inference(nnf_transformation,[],[f1])).
% 3.08/1.00  
% 3.08/1.00  fof(f43,plain,(
% 3.08/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.08/1.00    inference(rectify,[],[f42])).
% 3.08/1.00  
% 3.08/1.00  fof(f44,plain,(
% 3.08/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.08/1.00    introduced(choice_axiom,[])).
% 3.08/1.00  
% 3.08/1.00  fof(f45,plain,(
% 3.08/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.08/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.08/1.00  
% 3.08/1.00  fof(f54,plain,(
% 3.08/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f45])).
% 3.08/1.00  
% 3.08/1.00  fof(f5,axiom,(
% 3.08/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f24,plain,(
% 3.08/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.08/1.00    inference(ennf_transformation,[],[f5])).
% 3.08/1.00  
% 3.08/1.00  fof(f60,plain,(
% 3.08/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f24])).
% 3.08/1.00  
% 3.08/1.00  fof(f3,axiom,(
% 3.08/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f23,plain,(
% 3.08/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.08/1.00    inference(ennf_transformation,[],[f3])).
% 3.08/1.00  
% 3.08/1.00  fof(f56,plain,(
% 3.08/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f23])).
% 3.08/1.00  
% 3.08/1.00  fof(f59,plain,(
% 3.08/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.08/1.00    inference(cnf_transformation,[],[f47])).
% 3.08/1.00  
% 3.08/1.00  fof(f90,plain,(
% 3.08/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.08/1.00    inference(equality_resolution,[],[f59])).
% 3.08/1.00  
% 3.08/1.00  fof(f14,axiom,(
% 3.08/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f21,plain,(
% 3.08/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.08/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.08/1.00  
% 3.08/1.00  fof(f73,plain,(
% 3.08/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f21])).
% 3.08/1.00  
% 3.08/1.00  fof(f8,axiom,(
% 3.08/1.00    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f63,plain,(
% 3.08/1.00    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.08/1.00    inference(cnf_transformation,[],[f8])).
% 3.08/1.00  
% 3.08/1.00  fof(f16,axiom,(
% 3.08/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.00  
% 3.08/1.00  fof(f75,plain,(
% 3.08/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.08/1.00    inference(cnf_transformation,[],[f16])).
% 3.08/1.00  
% 3.08/1.00  fof(f89,plain,(
% 3.08/1.00    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.08/1.00    inference(definition_unfolding,[],[f63,f75,f75])).
% 3.08/1.00  
% 3.08/1.00  cnf(c_26,negated_conjecture,
% 3.08/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 3.08/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1568,plain,
% 3.08/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_31,negated_conjecture,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1564,plain,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_12,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1573,plain,
% 3.08/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4056,plain,
% 3.08/1.00      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_1564,c_1573]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_11,plain,
% 3.08/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_19,plain,
% 3.08/1.00      ( ~ v2_funct_2(X0,X1)
% 3.08/1.00      | ~ v5_relat_1(X0,X1)
% 3.08/1.00      | ~ v1_relat_1(X0)
% 3.08/1.00      | k2_relat_1(X0) = X1 ),
% 3.08/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_15,plain,
% 3.08/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.08/1.00      | v2_funct_2(X0,X2)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.00      | ~ v1_funct_1(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_32,negated_conjecture,
% 3.08/1.00      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.08/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_415,plain,
% 3.08/1.00      ( v2_funct_2(X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.08/1.00      | ~ v1_funct_1(X0)
% 3.08/1.00      | sK2 != X0
% 3.08/1.00      | sK1 != X1
% 3.08/1.00      | sK1 != X2 ),
% 3.08/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_416,plain,
% 3.08/1.00      ( v2_funct_2(sK2,sK1)
% 3.08/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.08/1.00      | ~ v1_funct_1(sK2) ),
% 3.08/1.00      inference(unflattening,[status(thm)],[c_415]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_34,negated_conjecture,
% 3.08/1.00      ( v1_funct_1(sK2) ),
% 3.08/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_418,plain,
% 3.08/1.00      ( v2_funct_2(sK2,sK1) ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_416,c_34,c_31]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_501,plain,
% 3.08/1.00      ( ~ v5_relat_1(X0,X1)
% 3.08/1.00      | ~ v1_relat_1(X0)
% 3.08/1.00      | k2_relat_1(X0) = X1
% 3.08/1.00      | sK2 != X0
% 3.08/1.00      | sK1 != X1 ),
% 3.08/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_418]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_502,plain,
% 3.08/1.00      ( ~ v5_relat_1(sK2,sK1) | ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK1 ),
% 3.08/1.00      inference(unflattening,[status(thm)],[c_501]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_548,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.00      | ~ v1_relat_1(sK2)
% 3.08/1.00      | k2_relat_1(sK2) = sK1
% 3.08/1.00      | sK2 != X0
% 3.08/1.00      | sK1 != X2 ),
% 3.08/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_502]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_549,plain,
% 3.08/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.08/1.00      | ~ v1_relat_1(sK2)
% 3.08/1.00      | k2_relat_1(sK2) = sK1 ),
% 3.08/1.00      inference(unflattening,[status(thm)],[c_548]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_551,plain,
% 3.08/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.08/1.00      | ~ v1_relat_1(sK2)
% 3.08/1.00      | k2_relat_1(sK2) = sK1 ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_549]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_553,plain,
% 3.08/1.00      ( ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK1 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_549,c_31,c_551]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1557,plain,
% 3.08/1.00      ( k2_relat_1(sK2) = sK1 | v1_relat_1(sK2) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_9,plain,
% 3.08/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.08/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_87,plain,
% 3.08/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_8,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1755,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.00      | v1_relat_1(X0)
% 3.08/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1943,plain,
% 3.08/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.08/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
% 3.08/1.00      | v1_relat_1(sK2) ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_1755]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2333,plain,
% 3.08/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_1557,c_31,c_87,c_551,c_1943]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4068,plain,
% 3.08/1.00      ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
% 3.08/1.00      inference(light_normalisation,[status(thm)],[c_4056,c_2333]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_24,plain,
% 3.08/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.08/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.08/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.08/1.00      | ~ v2_funct_1(X2)
% 3.08/1.00      | ~ v1_funct_1(X2)
% 3.08/1.00      | ~ v1_funct_1(X3)
% 3.08/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.08/1.00      | k2_funct_1(X2) = X3
% 3.08/1.00      | k1_xboole_0 = X1
% 3.08/1.00      | k1_xboole_0 = X0 ),
% 3.08/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_23,plain,
% 3.08/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.08/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.08/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.08/1.00      | v2_funct_1(X2)
% 3.08/1.00      | ~ v1_funct_1(X2)
% 3.08/1.00      | ~ v1_funct_1(X3) ),
% 3.08/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_179,plain,
% 3.08/1.00      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.08/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.08/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.08/1.00      | ~ v1_funct_1(X2)
% 3.08/1.00      | ~ v1_funct_1(X3)
% 3.08/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.08/1.00      | k2_funct_1(X2) = X3
% 3.08/1.00      | k1_xboole_0 = X1
% 3.08/1.00      | k1_xboole_0 = X0 ),
% 3.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_24,c_23]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_180,plain,
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
% 3.08/1.00      inference(renaming,[status(thm)],[c_179]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1561,plain,
% 3.08/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.08/1.00      | k2_funct_1(X2) = X3
% 3.08/1.00      | k1_xboole_0 = X0
% 3.08/1.00      | k1_xboole_0 = X1
% 3.08/1.00      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.08/1.00      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.08/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.08/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.08/1.00      | v1_funct_1(X2) != iProver_top
% 3.08/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4919,plain,
% 3.08/1.00      ( k2_funct_1(sK2) = X0
% 3.08/1.00      | sK1 = k1_xboole_0
% 3.08/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.08/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.08/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.08/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.08/1.00      | v1_funct_1(X0) != iProver_top
% 3.08/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_4068,c_1561]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_35,plain,
% 3.08/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_33,negated_conjecture,
% 3.08/1.00      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.08/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_36,plain,
% 3.08/1.00      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_38,plain,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5223,plain,
% 3.08/1.00      ( v1_funct_1(X0) != iProver_top
% 3.08/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.08/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.08/1.00      | sK1 = k1_xboole_0
% 3.08/1.00      | k2_funct_1(sK2) = X0
% 3.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_4919,c_35,c_36,c_38]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5224,plain,
% 3.08/1.00      ( k2_funct_1(sK2) = X0
% 3.08/1.00      | sK1 = k1_xboole_0
% 3.08/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.08/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.08/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.08/1.00      inference(renaming,[status(thm)],[c_5223]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5235,plain,
% 3.08/1.00      ( k2_funct_1(sK2) = sK3
% 3.08/1.00      | sK1 = k1_xboole_0
% 3.08/1.00      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.08/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.08/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_1568,c_5224]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_30,negated_conjecture,
% 3.08/1.00      ( v1_funct_1(sK3) ),
% 3.08/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_29,negated_conjecture,
% 3.08/1.00      ( v1_funct_2(sK3,sK1,sK1) ),
% 3.08/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_27,negated_conjecture,
% 3.08/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5236,plain,
% 3.08/1.00      ( ~ v1_funct_2(sK3,sK1,sK1)
% 3.08/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.08/1.00      | ~ v1_funct_1(sK3)
% 3.08/1.00      | k2_funct_1(sK2) = sK3
% 3.08/1.00      | sK1 = k1_xboole_0 ),
% 3.08/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5235]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5259,plain,
% 3.08/1.00      ( sK1 = k1_xboole_0 | k2_funct_1(sK2) = sK3 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_5235,c_39,c_40,c_42]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5260,plain,
% 3.08/1.00      ( k2_funct_1(sK2) = sK3 | sK1 = k1_xboole_0 ),
% 3.08/1.00      inference(renaming,[status(thm)],[c_5259]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_25,negated_conjecture,
% 3.08/1.00      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 3.08/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1569,plain,
% 3.08/1.00      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_21,plain,
% 3.08/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.08/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.08/1.00      | ~ v1_funct_1(X0)
% 3.08/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_434,plain,
% 3.08/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.08/1.00      | ~ v1_funct_1(X0)
% 3.08/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.08/1.00      | sK2 != X0
% 3.08/1.00      | sK1 != X1 ),
% 3.08/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_435,plain,
% 3.08/1.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.08/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.08/1.00      | ~ v1_funct_1(sK2)
% 3.08/1.00      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.08/1.00      inference(unflattening,[status(thm)],[c_434]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_437,plain,
% 3.08/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_435,c_34,c_33,c_31]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1614,plain,
% 3.08/1.00      ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.08/1.00      inference(light_normalisation,[status(thm)],[c_1569,c_437]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5263,plain,
% 3.08/1.00      ( sK1 = k1_xboole_0 | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_5260,c_1614]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_42,plain,
% 3.08/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_13,plain,
% 3.08/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1788,plain,
% 3.08/1.00      ( r2_relset_1(sK1,sK1,sK3,sK3)
% 3.08/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1789,plain,
% 3.08/1.00      ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
% 3.08/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5266,plain,
% 3.08/1.00      ( sK1 = k1_xboole_0 ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_5263,c_42,c_1789]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5287,plain,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_5266,c_1564]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5,plain,
% 3.08/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.08/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5301,plain,
% 3.08/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_5287,c_5]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1567,plain,
% 3.08/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_14,plain,
% 3.08/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.00      | X3 = X2 ),
% 3.08/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1571,plain,
% 3.08/1.00      ( X0 = X1
% 3.08/1.00      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 3.08/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4591,plain,
% 3.08/1.00      ( sK3 = X0
% 3.08/1.00      | r2_relset_1(sK1,sK1,sK3,X0) != iProver_top
% 3.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_1567,c_1571]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5276,plain,
% 3.08/1.00      ( sK3 = X0
% 3.08/1.00      | r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,X0) != iProver_top
% 3.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_5266,c_4591]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5333,plain,
% 3.08/1.00      ( sK3 = X0
% 3.08/1.00      | r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,X0) != iProver_top
% 3.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_5276,c_5]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2,plain,
% 3.08/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_99,plain,
% 3.08/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_0,plain,
% 3.08/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.08/1.00      | ~ r2_hidden(X2,X0)
% 3.08/1.00      | ~ v1_xboole_0(X1) ),
% 3.08/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_348,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.08/1.00      | ~ v1_xboole_0(X1)
% 3.08/1.00      | v1_xboole_0(X2)
% 3.08/1.00      | X0 != X2
% 3.08/1.00      | sK0(X2) != X3 ),
% 3.08/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_349,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.08/1.00      | ~ v1_xboole_0(X1)
% 3.08/1.00      | v1_xboole_0(X0) ),
% 3.08/1.00      inference(unflattening,[status(thm)],[c_348]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4570,plain,
% 3.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 3.08/1.00      | v1_xboole_0(X0)
% 3.08/1.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.08/1.00      inference(instantiation,[status(thm)],[c_349]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4571,plain,
% 3.08/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.08/1.00      | v1_xboole_0(X0) = iProver_top
% 3.08/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4570]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1560,plain,
% 3.08/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.08/1.00      | v1_xboole_0(X1) != iProver_top
% 3.08/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4206,plain,
% 3.08/1.00      ( v1_xboole_0(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 3.08/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_1567,c_1560]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5278,plain,
% 3.08/1.00      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.08/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_5266,c_4206]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5322,plain,
% 3.08/1.00      ( v1_xboole_0(sK3) = iProver_top
% 3.08/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_5278,c_5]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5579,plain,
% 3.08/1.00      ( v1_xboole_0(sK3) = iProver_top ),
% 3.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5322,c_99]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_3,plain,
% 3.08/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.08/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1576,plain,
% 3.08/1.00      ( X0 = X1
% 3.08/1.00      | v1_xboole_0(X0) != iProver_top
% 3.08/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5585,plain,
% 3.08/1.00      ( sK3 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_5579,c_1576]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6402,plain,
% 3.08/1.00      ( sK3 = X0 | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.08/1.00      inference(global_propositional_subsumption,
% 3.08/1.00                [status(thm)],
% 3.08/1.00                [c_5333,c_99,c_4571,c_5585]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6411,plain,
% 3.08/1.00      ( sK2 = sK3 ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_5301,c_6402]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5284,plain,
% 3.08/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_5266,c_1614]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6579,plain,
% 3.08/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK3)) != iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_6411,c_5284]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_4,plain,
% 3.08/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_20,plain,
% 3.08/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.08/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1570,plain,
% 3.08/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_2884,plain,
% 3.08/1.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_4,c_1570]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6410,plain,
% 3.08/1.00      ( k6_partfun1(k1_xboole_0) = sK3 ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_2884,c_6402]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_10,plain,
% 3.08/1.00      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.08/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6601,plain,
% 3.08/1.00      ( k2_funct_1(sK3) = k6_partfun1(k1_xboole_0) ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_6410,c_10]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_6622,plain,
% 3.08/1.00      ( k2_funct_1(sK3) = sK3 ),
% 3.08/1.00      inference(light_normalisation,[status(thm)],[c_6601,c_6410]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7439,plain,
% 3.08/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,sK3) != iProver_top ),
% 3.08/1.00      inference(light_normalisation,[status(thm)],[c_6579,c_6622]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_1572,plain,
% 3.08/1.00      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.08/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_3040,plain,
% 3.08/1.00      ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top ),
% 3.08/1.00      inference(superposition,[status(thm)],[c_1567,c_1572]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_5281,plain,
% 3.08/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,sK3) = iProver_top ),
% 3.08/1.00      inference(demodulation,[status(thm)],[c_5266,c_3040]) ).
% 3.08/1.00  
% 3.08/1.00  cnf(c_7441,plain,
% 3.08/1.00      ( $false ),
% 3.08/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_7439,c_5281]) ).
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
% 3.08/1.00  total_time:                             0.28
% 3.08/1.00  num_of_symbols:                         55
% 3.08/1.00  num_of_terms:                           9802
% 3.08/1.00  
% 3.08/1.00  ------ Preprocessing
% 3.08/1.00  
% 3.08/1.00  num_of_splits:                          0
% 3.08/1.00  num_of_split_atoms:                     0
% 3.08/1.00  num_of_reused_defs:                     0
% 3.08/1.00  num_eq_ax_congr_red:                    15
% 3.08/1.00  num_of_sem_filtered_clauses:            3
% 3.08/1.00  num_of_subtypes:                        0
% 3.08/1.00  monotx_restored_types:                  0
% 3.08/1.00  sat_num_of_epr_types:                   0
% 3.08/1.00  sat_num_of_non_cyclic_types:            0
% 3.08/1.00  sat_guarded_non_collapsed_types:        0
% 3.08/1.00  num_pure_diseq_elim:                    0
% 3.08/1.00  simp_replaced_by:                       0
% 3.08/1.00  res_preprocessed:                       146
% 3.08/1.00  prep_upred:                             0
% 3.08/1.00  prep_unflattend:                        66
% 3.08/1.00  smt_new_axioms:                         0
% 3.08/1.00  pred_elim_cands:                        6
% 3.08/1.00  pred_elim:                              4
% 3.08/1.00  pred_elim_cl:                           5
% 3.08/1.00  pred_elim_cycles:                       7
% 3.08/1.00  merged_defs:                            0
% 3.08/1.00  merged_defs_ncl:                        0
% 3.08/1.00  bin_hyper_res:                          0
% 3.08/1.00  prep_cycles:                            4
% 3.08/1.00  pred_elim_time:                         0.016
% 3.08/1.00  splitting_time:                         0.
% 3.08/1.00  sem_filter_time:                        0.
% 3.08/1.00  monotx_time:                            0.001
% 3.08/1.00  subtype_inf_time:                       0.
% 3.08/1.00  
% 3.08/1.00  ------ Problem properties
% 3.08/1.00  
% 3.08/1.00  clauses:                                27
% 3.08/1.00  conjectures:                            8
% 3.08/1.00  epr:                                    6
% 3.08/1.00  horn:                                   25
% 3.08/1.00  ground:                                 13
% 3.08/1.00  unary:                                  16
% 3.08/1.00  binary:                                 4
% 3.08/1.00  lits:                                   60
% 3.08/1.00  lits_eq:                                18
% 3.08/1.00  fd_pure:                                0
% 3.08/1.00  fd_pseudo:                              0
% 3.08/1.00  fd_cond:                                1
% 3.08/1.00  fd_pseudo_cond:                         4
% 3.08/1.00  ac_symbols:                             0
% 3.08/1.00  
% 3.08/1.00  ------ Propositional Solver
% 3.08/1.00  
% 3.08/1.00  prop_solver_calls:                      26
% 3.08/1.00  prop_fast_solver_calls:                 1143
% 3.08/1.00  smt_solver_calls:                       0
% 3.08/1.00  smt_fast_solver_calls:                  0
% 3.08/1.00  prop_num_of_clauses:                    2522
% 3.08/1.00  prop_preprocess_simplified:             7315
% 3.08/1.00  prop_fo_subsumed:                       35
% 3.08/1.00  prop_solver_time:                       0.
% 3.08/1.00  smt_solver_time:                        0.
% 3.08/1.00  smt_fast_solver_time:                   0.
% 3.08/1.00  prop_fast_solver_time:                  0.
% 3.08/1.00  prop_unsat_core_time:                   0.
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
% 3.08/1.00  inst_num_of_clauses:                    750
% 3.08/1.00  inst_num_in_passive:                    230
% 3.08/1.00  inst_num_in_active:                     422
% 3.08/1.00  inst_num_in_unprocessed:                98
% 3.08/1.00  inst_num_of_loops:                      430
% 3.08/1.00  inst_num_of_learning_restarts:          0
% 3.08/1.00  inst_num_moves_active_passive:          6
% 3.08/1.00  inst_lit_activity:                      0
% 3.08/1.00  inst_lit_activity_moves:                0
% 3.08/1.00  inst_num_tautologies:                   0
% 3.08/1.00  inst_num_prop_implied:                  0
% 3.08/1.00  inst_num_existing_simplified:           0
% 3.08/1.00  inst_num_eq_res_simplified:             0
% 3.08/1.00  inst_num_child_elim:                    0
% 3.08/1.00  inst_num_of_dismatching_blockings:      289
% 3.08/1.00  inst_num_of_non_proper_insts:           954
% 3.08/1.00  inst_num_of_duplicates:                 0
% 3.08/1.00  inst_inst_num_from_inst_to_res:         0
% 3.08/1.00  inst_dismatching_checking_time:         0.
% 3.08/1.00  
% 3.08/1.00  ------ Resolution
% 3.08/1.00  
% 3.08/1.00  res_num_of_clauses:                     0
% 3.08/1.00  res_num_in_passive:                     0
% 3.08/1.00  res_num_in_active:                      0
% 3.08/1.00  res_num_of_loops:                       150
% 3.08/1.00  res_forward_subset_subsumed:            55
% 3.08/1.00  res_backward_subset_subsumed:           0
% 3.08/1.00  res_forward_subsumed:                   0
% 3.08/1.00  res_backward_subsumed:                  0
% 3.08/1.00  res_forward_subsumption_resolution:     1
% 3.08/1.00  res_backward_subsumption_resolution:    0
% 3.08/1.00  res_clause_to_clause_subsumption:       191
% 3.08/1.00  res_orphan_elimination:                 0
% 3.08/1.00  res_tautology_del:                      54
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
% 3.08/1.00  sup_num_of_clauses:                     67
% 3.08/1.00  sup_num_in_active:                      45
% 3.08/1.00  sup_num_in_passive:                     22
% 3.08/1.00  sup_num_of_loops:                       85
% 3.08/1.00  sup_fw_superposition:                   58
% 3.08/1.00  sup_bw_superposition:                   36
% 3.08/1.00  sup_immediate_simplified:               25
% 3.08/1.00  sup_given_eliminated:                   3
% 3.08/1.00  comparisons_done:                       0
% 3.08/1.00  comparisons_avoided:                    3
% 3.08/1.00  
% 3.08/1.00  ------ Simplifications
% 3.08/1.00  
% 3.08/1.00  
% 3.08/1.00  sim_fw_subset_subsumed:                 10
% 3.08/1.00  sim_bw_subset_subsumed:                 5
% 3.08/1.00  sim_fw_subsumed:                        0
% 3.08/1.00  sim_bw_subsumed:                        0
% 3.08/1.00  sim_fw_subsumption_res:                 1
% 3.08/1.00  sim_bw_subsumption_res:                 0
% 3.08/1.00  sim_tautology_del:                      0
% 3.08/1.00  sim_eq_tautology_del:                   18
% 3.08/1.00  sim_eq_res_simp:                        0
% 3.08/1.00  sim_fw_demodulated:                     11
% 3.08/1.00  sim_bw_demodulated:                     41
% 3.08/1.00  sim_light_normalised:                   16
% 3.08/1.00  sim_joinable_taut:                      0
% 3.08/1.00  sim_joinable_simp:                      0
% 3.08/1.00  sim_ac_normalised:                      0
% 3.08/1.00  sim_smt_subsumption:                    0
% 3.08/1.00  
%------------------------------------------------------------------------------
