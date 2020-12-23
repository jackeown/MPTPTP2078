%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:15 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_39)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

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
    inference(ennf_transformation,[],[f21])).

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

fof(f85,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f90,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f59,f73,f73])).

fof(f83,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1603,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1599,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1610,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2818,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1599,c_1610])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_13,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_404,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_405,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_407,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_34,c_31])).

cnf(c_490,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_407])).

cnf(c_491,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_491])).

cnf(c_538,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_540,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_542,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_31,c_540])).

cnf(c_1593,plain,
    ( k2_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_98,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1674,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1744,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_1746,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_2453,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1593,c_31,c_98,c_540,c_1746])).

cnf(c_2819,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2818,c_2453])).

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
    inference(cnf_transformation,[],[f76])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_183,plain,
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

cnf(c_184,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_1596,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_3517,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_1596])).

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

cnf(c_5060,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3517,c_35,c_36,c_38])).

cnf(c_5061,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5060])).

cnf(c_5066,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_5061])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5067,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5066])).

cnf(c_5069,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5066,c_39,c_40,c_42])).

cnf(c_5070,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5069])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1604,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_423,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_424,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_426,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_424,c_34,c_33,c_31])).

cnf(c_1617,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1604,c_426])).

cnf(c_5071,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5070,c_1617])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1784,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1785,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_5210,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5071,c_42,c_1785])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1611,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2996,plain,
    ( v1_relat_1(sK1) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_1611])).

cnf(c_97,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_99,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_1745,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1744])).

cnf(c_1747,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_3414,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2996,c_38,c_99,c_1747])).

cnf(c_5222,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5210,c_3414])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_107,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1161,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3205,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_3206,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3205])).

cnf(c_3208,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3206])).

cnf(c_8117,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5222,c_38,c_42,c_99,c_107,c_1747,c_1785,c_2996,c_3208,c_5071])).

cnf(c_1616,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1615,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2593,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_1615])).

cnf(c_8123,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8117,c_2593])).

cnf(c_5230,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5210,c_1617])).

cnf(c_10182,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8123,c_5230])).

cnf(c_6,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2994,plain,
    ( v1_relat_1(k6_partfun1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1611])).

cnf(c_3,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_100,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3683,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2994,c_100])).

cnf(c_3690,plain,
    ( k6_partfun1(X0) = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3683,c_1615])).

cnf(c_4448,plain,
    ( k6_partfun1(k1_xboole_0) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_3690])).

cnf(c_4457,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1616,c_4448])).

cnf(c_8,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4609,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4457,c_8])).

cnf(c_4612,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4609,c_4457])).

cnf(c_28,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_393,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_394,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_396,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_30,c_27])).

cnf(c_477,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_396])).

cnf(c_478,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_478])).

cnf(c_522,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_526,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_27,c_524])).

cnf(c_1594,plain,
    ( k2_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_1664,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1705,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_1707,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1705])).

cnf(c_2513,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1594,c_27,c_98,c_524,c_1707])).

cnf(c_2995,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2513,c_1611])).

cnf(c_1706,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1705])).

cnf(c_1708,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_3409,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2995,c_42,c_99,c_1708])).

cnf(c_5223,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5210,c_3409])).

cnf(c_8637,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5223,c_42,c_99,c_107,c_1708,c_1785,c_2995,c_3208,c_5071])).

cnf(c_8643,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8637,c_2593])).

cnf(c_10190,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10182,c_4612,c_8643])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1605,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1609,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2807,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1609])).

cnf(c_4604,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4457,c_2807])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10190,c_4604])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:22:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.61/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.01  
% 3.61/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/1.01  
% 3.61/1.01  ------  iProver source info
% 3.61/1.01  
% 3.61/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.61/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/1.01  git: non_committed_changes: false
% 3.61/1.01  git: last_make_outside_of_git: false
% 3.61/1.01  
% 3.61/1.01  ------ 
% 3.61/1.01  
% 3.61/1.01  ------ Input Options
% 3.61/1.01  
% 3.61/1.01  --out_options                           all
% 3.61/1.01  --tptp_safe_out                         true
% 3.61/1.01  --problem_path                          ""
% 3.61/1.01  --include_path                          ""
% 3.61/1.01  --clausifier                            res/vclausify_rel
% 3.61/1.01  --clausifier_options                    ""
% 3.61/1.01  --stdin                                 false
% 3.61/1.01  --stats_out                             all
% 3.61/1.01  
% 3.61/1.01  ------ General Options
% 3.61/1.01  
% 3.61/1.01  --fof                                   false
% 3.61/1.01  --time_out_real                         305.
% 3.61/1.01  --time_out_virtual                      -1.
% 3.61/1.01  --symbol_type_check                     false
% 3.61/1.01  --clausify_out                          false
% 3.61/1.01  --sig_cnt_out                           false
% 3.61/1.01  --trig_cnt_out                          false
% 3.61/1.01  --trig_cnt_out_tolerance                1.
% 3.61/1.01  --trig_cnt_out_sk_spl                   false
% 3.61/1.01  --abstr_cl_out                          false
% 3.61/1.01  
% 3.61/1.01  ------ Global Options
% 3.61/1.01  
% 3.61/1.01  --schedule                              default
% 3.61/1.01  --add_important_lit                     false
% 3.61/1.01  --prop_solver_per_cl                    1000
% 3.61/1.01  --min_unsat_core                        false
% 3.61/1.01  --soft_assumptions                      false
% 3.61/1.01  --soft_lemma_size                       3
% 3.61/1.01  --prop_impl_unit_size                   0
% 3.61/1.01  --prop_impl_unit                        []
% 3.61/1.01  --share_sel_clauses                     true
% 3.61/1.01  --reset_solvers                         false
% 3.61/1.01  --bc_imp_inh                            [conj_cone]
% 3.61/1.01  --conj_cone_tolerance                   3.
% 3.61/1.01  --extra_neg_conj                        none
% 3.61/1.01  --large_theory_mode                     true
% 3.61/1.01  --prolific_symb_bound                   200
% 3.61/1.01  --lt_threshold                          2000
% 3.61/1.01  --clause_weak_htbl                      true
% 3.61/1.01  --gc_record_bc_elim                     false
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing Options
% 3.61/1.01  
% 3.61/1.01  --preprocessing_flag                    true
% 3.61/1.01  --time_out_prep_mult                    0.1
% 3.61/1.01  --splitting_mode                        input
% 3.61/1.01  --splitting_grd                         true
% 3.61/1.01  --splitting_cvd                         false
% 3.61/1.01  --splitting_cvd_svl                     false
% 3.61/1.01  --splitting_nvd                         32
% 3.61/1.01  --sub_typing                            true
% 3.61/1.01  --prep_gs_sim                           true
% 3.61/1.01  --prep_unflatten                        true
% 3.61/1.01  --prep_res_sim                          true
% 3.61/1.01  --prep_upred                            true
% 3.61/1.01  --prep_sem_filter                       exhaustive
% 3.61/1.01  --prep_sem_filter_out                   false
% 3.61/1.01  --pred_elim                             true
% 3.61/1.01  --res_sim_input                         true
% 3.61/1.01  --eq_ax_congr_red                       true
% 3.61/1.01  --pure_diseq_elim                       true
% 3.61/1.01  --brand_transform                       false
% 3.61/1.01  --non_eq_to_eq                          false
% 3.61/1.01  --prep_def_merge                        true
% 3.61/1.01  --prep_def_merge_prop_impl              false
% 3.61/1.01  --prep_def_merge_mbd                    true
% 3.61/1.01  --prep_def_merge_tr_red                 false
% 3.61/1.01  --prep_def_merge_tr_cl                  false
% 3.61/1.01  --smt_preprocessing                     true
% 3.61/1.01  --smt_ac_axioms                         fast
% 3.61/1.01  --preprocessed_out                      false
% 3.61/1.01  --preprocessed_stats                    false
% 3.61/1.01  
% 3.61/1.01  ------ Abstraction refinement Options
% 3.61/1.01  
% 3.61/1.01  --abstr_ref                             []
% 3.61/1.01  --abstr_ref_prep                        false
% 3.61/1.01  --abstr_ref_until_sat                   false
% 3.61/1.01  --abstr_ref_sig_restrict                funpre
% 3.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/1.01  --abstr_ref_under                       []
% 3.61/1.01  
% 3.61/1.01  ------ SAT Options
% 3.61/1.01  
% 3.61/1.01  --sat_mode                              false
% 3.61/1.01  --sat_fm_restart_options                ""
% 3.61/1.01  --sat_gr_def                            false
% 3.61/1.01  --sat_epr_types                         true
% 3.61/1.01  --sat_non_cyclic_types                  false
% 3.61/1.01  --sat_finite_models                     false
% 3.61/1.01  --sat_fm_lemmas                         false
% 3.61/1.01  --sat_fm_prep                           false
% 3.61/1.01  --sat_fm_uc_incr                        true
% 3.61/1.01  --sat_out_model                         small
% 3.61/1.01  --sat_out_clauses                       false
% 3.61/1.01  
% 3.61/1.01  ------ QBF Options
% 3.61/1.01  
% 3.61/1.01  --qbf_mode                              false
% 3.61/1.01  --qbf_elim_univ                         false
% 3.61/1.01  --qbf_dom_inst                          none
% 3.61/1.01  --qbf_dom_pre_inst                      false
% 3.61/1.01  --qbf_sk_in                             false
% 3.61/1.01  --qbf_pred_elim                         true
% 3.61/1.01  --qbf_split                             512
% 3.61/1.01  
% 3.61/1.01  ------ BMC1 Options
% 3.61/1.01  
% 3.61/1.01  --bmc1_incremental                      false
% 3.61/1.01  --bmc1_axioms                           reachable_all
% 3.61/1.01  --bmc1_min_bound                        0
% 3.61/1.01  --bmc1_max_bound                        -1
% 3.61/1.01  --bmc1_max_bound_default                -1
% 3.61/1.01  --bmc1_symbol_reachability              true
% 3.61/1.01  --bmc1_property_lemmas                  false
% 3.61/1.01  --bmc1_k_induction                      false
% 3.61/1.01  --bmc1_non_equiv_states                 false
% 3.61/1.01  --bmc1_deadlock                         false
% 3.61/1.01  --bmc1_ucm                              false
% 3.61/1.01  --bmc1_add_unsat_core                   none
% 3.61/1.01  --bmc1_unsat_core_children              false
% 3.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/1.01  --bmc1_out_stat                         full
% 3.61/1.01  --bmc1_ground_init                      false
% 3.61/1.01  --bmc1_pre_inst_next_state              false
% 3.61/1.01  --bmc1_pre_inst_state                   false
% 3.61/1.01  --bmc1_pre_inst_reach_state             false
% 3.61/1.01  --bmc1_out_unsat_core                   false
% 3.61/1.01  --bmc1_aig_witness_out                  false
% 3.61/1.01  --bmc1_verbose                          false
% 3.61/1.01  --bmc1_dump_clauses_tptp                false
% 3.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.61/1.01  --bmc1_dump_file                        -
% 3.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.61/1.01  --bmc1_ucm_extend_mode                  1
% 3.61/1.01  --bmc1_ucm_init_mode                    2
% 3.61/1.01  --bmc1_ucm_cone_mode                    none
% 3.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.61/1.01  --bmc1_ucm_relax_model                  4
% 3.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/1.01  --bmc1_ucm_layered_model                none
% 3.61/1.01  --bmc1_ucm_max_lemma_size               10
% 3.61/1.01  
% 3.61/1.01  ------ AIG Options
% 3.61/1.01  
% 3.61/1.01  --aig_mode                              false
% 3.61/1.01  
% 3.61/1.01  ------ Instantiation Options
% 3.61/1.01  
% 3.61/1.01  --instantiation_flag                    true
% 3.61/1.01  --inst_sos_flag                         true
% 3.61/1.01  --inst_sos_phase                        true
% 3.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/1.01  --inst_lit_sel_side                     num_symb
% 3.61/1.01  --inst_solver_per_active                1400
% 3.61/1.01  --inst_solver_calls_frac                1.
% 3.61/1.01  --inst_passive_queue_type               priority_queues
% 3.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/1.01  --inst_passive_queues_freq              [25;2]
% 3.61/1.01  --inst_dismatching                      true
% 3.61/1.01  --inst_eager_unprocessed_to_passive     true
% 3.61/1.01  --inst_prop_sim_given                   true
% 3.61/1.01  --inst_prop_sim_new                     false
% 3.61/1.01  --inst_subs_new                         false
% 3.61/1.01  --inst_eq_res_simp                      false
% 3.61/1.01  --inst_subs_given                       false
% 3.61/1.01  --inst_orphan_elimination               true
% 3.61/1.01  --inst_learning_loop_flag               true
% 3.61/1.01  --inst_learning_start                   3000
% 3.61/1.01  --inst_learning_factor                  2
% 3.61/1.01  --inst_start_prop_sim_after_learn       3
% 3.61/1.01  --inst_sel_renew                        solver
% 3.61/1.01  --inst_lit_activity_flag                true
% 3.61/1.01  --inst_restr_to_given                   false
% 3.61/1.01  --inst_activity_threshold               500
% 3.61/1.01  --inst_out_proof                        true
% 3.61/1.01  
% 3.61/1.01  ------ Resolution Options
% 3.61/1.01  
% 3.61/1.01  --resolution_flag                       true
% 3.61/1.01  --res_lit_sel                           adaptive
% 3.61/1.01  --res_lit_sel_side                      none
% 3.61/1.01  --res_ordering                          kbo
% 3.61/1.01  --res_to_prop_solver                    active
% 3.61/1.01  --res_prop_simpl_new                    false
% 3.61/1.01  --res_prop_simpl_given                  true
% 3.61/1.01  --res_passive_queue_type                priority_queues
% 3.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/1.01  --res_passive_queues_freq               [15;5]
% 3.61/1.01  --res_forward_subs                      full
% 3.61/1.01  --res_backward_subs                     full
% 3.61/1.01  --res_forward_subs_resolution           true
% 3.61/1.01  --res_backward_subs_resolution          true
% 3.61/1.01  --res_orphan_elimination                true
% 3.61/1.01  --res_time_limit                        2.
% 3.61/1.01  --res_out_proof                         true
% 3.61/1.01  
% 3.61/1.01  ------ Superposition Options
% 3.61/1.01  
% 3.61/1.01  --superposition_flag                    true
% 3.61/1.01  --sup_passive_queue_type                priority_queues
% 3.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.61/1.01  --demod_completeness_check              fast
% 3.61/1.01  --demod_use_ground                      true
% 3.61/1.01  --sup_to_prop_solver                    passive
% 3.61/1.01  --sup_prop_simpl_new                    true
% 3.61/1.01  --sup_prop_simpl_given                  true
% 3.61/1.01  --sup_fun_splitting                     true
% 3.61/1.01  --sup_smt_interval                      50000
% 3.61/1.01  
% 3.61/1.01  ------ Superposition Simplification Setup
% 3.61/1.01  
% 3.61/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.61/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.61/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.61/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.61/1.01  --sup_immed_triv                        [TrivRules]
% 3.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_immed_bw_main                     []
% 3.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_input_bw                          []
% 3.61/1.01  
% 3.61/1.01  ------ Combination Options
% 3.61/1.01  
% 3.61/1.01  --comb_res_mult                         3
% 3.61/1.01  --comb_sup_mult                         2
% 3.61/1.01  --comb_inst_mult                        10
% 3.61/1.01  
% 3.61/1.01  ------ Debug Options
% 3.61/1.01  
% 3.61/1.01  --dbg_backtrace                         false
% 3.61/1.01  --dbg_dump_prop_clauses                 false
% 3.61/1.01  --dbg_dump_prop_clauses_file            -
% 3.61/1.01  --dbg_out_stat                          false
% 3.61/1.01  ------ Parsing...
% 3.61/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.01  ------ Proving...
% 3.61/1.01  ------ Problem Properties 
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  clauses                                 29
% 3.61/1.01  conjectures                             8
% 3.61/1.01  EPR                                     6
% 3.61/1.01  Horn                                    28
% 3.61/1.01  unary                                   17
% 3.61/1.01  binary                                  4
% 3.61/1.01  lits                                    68
% 3.61/1.01  lits eq                                 15
% 3.61/1.01  fd_pure                                 0
% 3.61/1.01  fd_pseudo                               0
% 3.61/1.01  fd_cond                                 0
% 3.61/1.01  fd_pseudo_cond                          4
% 3.61/1.01  AC symbols                              0
% 3.61/1.01  
% 3.61/1.01  ------ Schedule dynamic 5 is on 
% 3.61/1.01  
% 3.61/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  ------ 
% 3.61/1.01  Current options:
% 3.61/1.01  ------ 
% 3.61/1.01  
% 3.61/1.01  ------ Input Options
% 3.61/1.01  
% 3.61/1.01  --out_options                           all
% 3.61/1.01  --tptp_safe_out                         true
% 3.61/1.01  --problem_path                          ""
% 3.61/1.01  --include_path                          ""
% 3.61/1.01  --clausifier                            res/vclausify_rel
% 3.61/1.01  --clausifier_options                    ""
% 3.61/1.01  --stdin                                 false
% 3.61/1.01  --stats_out                             all
% 3.61/1.01  
% 3.61/1.01  ------ General Options
% 3.61/1.01  
% 3.61/1.01  --fof                                   false
% 3.61/1.01  --time_out_real                         305.
% 3.61/1.01  --time_out_virtual                      -1.
% 3.61/1.01  --symbol_type_check                     false
% 3.61/1.01  --clausify_out                          false
% 3.61/1.01  --sig_cnt_out                           false
% 3.61/1.01  --trig_cnt_out                          false
% 3.61/1.01  --trig_cnt_out_tolerance                1.
% 3.61/1.01  --trig_cnt_out_sk_spl                   false
% 3.61/1.01  --abstr_cl_out                          false
% 3.61/1.01  
% 3.61/1.01  ------ Global Options
% 3.61/1.01  
% 3.61/1.01  --schedule                              default
% 3.61/1.01  --add_important_lit                     false
% 3.61/1.01  --prop_solver_per_cl                    1000
% 3.61/1.01  --min_unsat_core                        false
% 3.61/1.01  --soft_assumptions                      false
% 3.61/1.01  --soft_lemma_size                       3
% 3.61/1.01  --prop_impl_unit_size                   0
% 3.61/1.01  --prop_impl_unit                        []
% 3.61/1.01  --share_sel_clauses                     true
% 3.61/1.01  --reset_solvers                         false
% 3.61/1.01  --bc_imp_inh                            [conj_cone]
% 3.61/1.01  --conj_cone_tolerance                   3.
% 3.61/1.01  --extra_neg_conj                        none
% 3.61/1.01  --large_theory_mode                     true
% 3.61/1.01  --prolific_symb_bound                   200
% 3.61/1.01  --lt_threshold                          2000
% 3.61/1.01  --clause_weak_htbl                      true
% 3.61/1.01  --gc_record_bc_elim                     false
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing Options
% 3.61/1.01  
% 3.61/1.01  --preprocessing_flag                    true
% 3.61/1.01  --time_out_prep_mult                    0.1
% 3.61/1.01  --splitting_mode                        input
% 3.61/1.01  --splitting_grd                         true
% 3.61/1.01  --splitting_cvd                         false
% 3.61/1.01  --splitting_cvd_svl                     false
% 3.61/1.01  --splitting_nvd                         32
% 3.61/1.01  --sub_typing                            true
% 3.61/1.01  --prep_gs_sim                           true
% 3.61/1.01  --prep_unflatten                        true
% 3.61/1.01  --prep_res_sim                          true
% 3.61/1.01  --prep_upred                            true
% 3.61/1.01  --prep_sem_filter                       exhaustive
% 3.61/1.01  --prep_sem_filter_out                   false
% 3.61/1.01  --pred_elim                             true
% 3.61/1.01  --res_sim_input                         true
% 3.61/1.01  --eq_ax_congr_red                       true
% 3.61/1.01  --pure_diseq_elim                       true
% 3.61/1.01  --brand_transform                       false
% 3.61/1.01  --non_eq_to_eq                          false
% 3.61/1.01  --prep_def_merge                        true
% 3.61/1.01  --prep_def_merge_prop_impl              false
% 3.61/1.01  --prep_def_merge_mbd                    true
% 3.61/1.01  --prep_def_merge_tr_red                 false
% 3.61/1.01  --prep_def_merge_tr_cl                  false
% 3.61/1.01  --smt_preprocessing                     true
% 3.61/1.01  --smt_ac_axioms                         fast
% 3.61/1.01  --preprocessed_out                      false
% 3.61/1.01  --preprocessed_stats                    false
% 3.61/1.01  
% 3.61/1.01  ------ Abstraction refinement Options
% 3.61/1.01  
% 3.61/1.01  --abstr_ref                             []
% 3.61/1.01  --abstr_ref_prep                        false
% 3.61/1.01  --abstr_ref_until_sat                   false
% 3.61/1.01  --abstr_ref_sig_restrict                funpre
% 3.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/1.01  --abstr_ref_under                       []
% 3.61/1.01  
% 3.61/1.01  ------ SAT Options
% 3.61/1.01  
% 3.61/1.01  --sat_mode                              false
% 3.61/1.01  --sat_fm_restart_options                ""
% 3.61/1.01  --sat_gr_def                            false
% 3.61/1.01  --sat_epr_types                         true
% 3.61/1.01  --sat_non_cyclic_types                  false
% 3.61/1.01  --sat_finite_models                     false
% 3.61/1.01  --sat_fm_lemmas                         false
% 3.61/1.01  --sat_fm_prep                           false
% 3.61/1.01  --sat_fm_uc_incr                        true
% 3.61/1.01  --sat_out_model                         small
% 3.61/1.01  --sat_out_clauses                       false
% 3.61/1.01  
% 3.61/1.01  ------ QBF Options
% 3.61/1.01  
% 3.61/1.01  --qbf_mode                              false
% 3.61/1.01  --qbf_elim_univ                         false
% 3.61/1.01  --qbf_dom_inst                          none
% 3.61/1.01  --qbf_dom_pre_inst                      false
% 3.61/1.01  --qbf_sk_in                             false
% 3.61/1.01  --qbf_pred_elim                         true
% 3.61/1.01  --qbf_split                             512
% 3.61/1.01  
% 3.61/1.01  ------ BMC1 Options
% 3.61/1.01  
% 3.61/1.01  --bmc1_incremental                      false
% 3.61/1.01  --bmc1_axioms                           reachable_all
% 3.61/1.01  --bmc1_min_bound                        0
% 3.61/1.01  --bmc1_max_bound                        -1
% 3.61/1.01  --bmc1_max_bound_default                -1
% 3.61/1.01  --bmc1_symbol_reachability              true
% 3.61/1.01  --bmc1_property_lemmas                  false
% 3.61/1.01  --bmc1_k_induction                      false
% 3.61/1.01  --bmc1_non_equiv_states                 false
% 3.61/1.01  --bmc1_deadlock                         false
% 3.61/1.01  --bmc1_ucm                              false
% 3.61/1.01  --bmc1_add_unsat_core                   none
% 3.61/1.01  --bmc1_unsat_core_children              false
% 3.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/1.01  --bmc1_out_stat                         full
% 3.61/1.01  --bmc1_ground_init                      false
% 3.61/1.01  --bmc1_pre_inst_next_state              false
% 3.61/1.01  --bmc1_pre_inst_state                   false
% 3.61/1.01  --bmc1_pre_inst_reach_state             false
% 3.61/1.01  --bmc1_out_unsat_core                   false
% 3.61/1.01  --bmc1_aig_witness_out                  false
% 3.61/1.01  --bmc1_verbose                          false
% 3.61/1.01  --bmc1_dump_clauses_tptp                false
% 3.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.61/1.01  --bmc1_dump_file                        -
% 3.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.61/1.01  --bmc1_ucm_extend_mode                  1
% 3.61/1.01  --bmc1_ucm_init_mode                    2
% 3.61/1.01  --bmc1_ucm_cone_mode                    none
% 3.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.61/1.01  --bmc1_ucm_relax_model                  4
% 3.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/1.01  --bmc1_ucm_layered_model                none
% 3.61/1.01  --bmc1_ucm_max_lemma_size               10
% 3.61/1.01  
% 3.61/1.01  ------ AIG Options
% 3.61/1.01  
% 3.61/1.01  --aig_mode                              false
% 3.61/1.01  
% 3.61/1.01  ------ Instantiation Options
% 3.61/1.01  
% 3.61/1.01  --instantiation_flag                    true
% 3.61/1.01  --inst_sos_flag                         true
% 3.61/1.01  --inst_sos_phase                        true
% 3.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/1.01  --inst_lit_sel_side                     none
% 3.61/1.01  --inst_solver_per_active                1400
% 3.61/1.01  --inst_solver_calls_frac                1.
% 3.61/1.01  --inst_passive_queue_type               priority_queues
% 3.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/1.01  --inst_passive_queues_freq              [25;2]
% 3.61/1.01  --inst_dismatching                      true
% 3.61/1.01  --inst_eager_unprocessed_to_passive     true
% 3.61/1.01  --inst_prop_sim_given                   true
% 3.61/1.01  --inst_prop_sim_new                     false
% 3.61/1.01  --inst_subs_new                         false
% 3.61/1.01  --inst_eq_res_simp                      false
% 3.61/1.01  --inst_subs_given                       false
% 3.61/1.01  --inst_orphan_elimination               true
% 3.61/1.01  --inst_learning_loop_flag               true
% 3.61/1.01  --inst_learning_start                   3000
% 3.61/1.01  --inst_learning_factor                  2
% 3.61/1.01  --inst_start_prop_sim_after_learn       3
% 3.61/1.01  --inst_sel_renew                        solver
% 3.61/1.01  --inst_lit_activity_flag                true
% 3.61/1.01  --inst_restr_to_given                   false
% 3.61/1.01  --inst_activity_threshold               500
% 3.61/1.01  --inst_out_proof                        true
% 3.61/1.01  
% 3.61/1.01  ------ Resolution Options
% 3.61/1.01  
% 3.61/1.01  --resolution_flag                       false
% 3.61/1.01  --res_lit_sel                           adaptive
% 3.61/1.01  --res_lit_sel_side                      none
% 3.61/1.01  --res_ordering                          kbo
% 3.61/1.01  --res_to_prop_solver                    active
% 3.61/1.01  --res_prop_simpl_new                    false
% 3.61/1.01  --res_prop_simpl_given                  true
% 3.61/1.01  --res_passive_queue_type                priority_queues
% 3.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/1.01  --res_passive_queues_freq               [15;5]
% 3.61/1.01  --res_forward_subs                      full
% 3.61/1.01  --res_backward_subs                     full
% 3.61/1.01  --res_forward_subs_resolution           true
% 3.61/1.01  --res_backward_subs_resolution          true
% 3.61/1.01  --res_orphan_elimination                true
% 3.61/1.01  --res_time_limit                        2.
% 3.61/1.01  --res_out_proof                         true
% 3.61/1.01  
% 3.61/1.01  ------ Superposition Options
% 3.61/1.01  
% 3.61/1.01  --superposition_flag                    true
% 3.61/1.01  --sup_passive_queue_type                priority_queues
% 3.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.61/1.01  --demod_completeness_check              fast
% 3.61/1.01  --demod_use_ground                      true
% 3.61/1.01  --sup_to_prop_solver                    passive
% 3.61/1.01  --sup_prop_simpl_new                    true
% 3.61/1.01  --sup_prop_simpl_given                  true
% 3.61/1.01  --sup_fun_splitting                     true
% 3.61/1.01  --sup_smt_interval                      50000
% 3.61/1.01  
% 3.61/1.01  ------ Superposition Simplification Setup
% 3.61/1.01  
% 3.61/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.61/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.61/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.61/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.61/1.01  --sup_immed_triv                        [TrivRules]
% 3.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_immed_bw_main                     []
% 3.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_input_bw                          []
% 3.61/1.01  
% 3.61/1.01  ------ Combination Options
% 3.61/1.01  
% 3.61/1.01  --comb_res_mult                         3
% 3.61/1.01  --comb_sup_mult                         2
% 3.61/1.01  --comb_inst_mult                        10
% 3.61/1.01  
% 3.61/1.01  ------ Debug Options
% 3.61/1.01  
% 3.61/1.01  --dbg_backtrace                         false
% 3.61/1.01  --dbg_dump_prop_clauses                 false
% 3.61/1.01  --dbg_dump_prop_clauses_file            -
% 3.61/1.01  --dbg_out_stat                          false
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  ------ Proving...
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  % SZS status Theorem for theBenchmark.p
% 3.61/1.01  
% 3.61/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/1.01  
% 3.61/1.01  fof(f20,conjecture,(
% 3.61/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f21,negated_conjecture,(
% 3.61/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.61/1.01    inference(negated_conjecture,[],[f20])).
% 3.61/1.01  
% 3.61/1.01  fof(f44,plain,(
% 3.61/1.01    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.61/1.01    inference(ennf_transformation,[],[f21])).
% 3.61/1.01  
% 3.61/1.01  fof(f45,plain,(
% 3.61/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.61/1.01    inference(flattening,[],[f44])).
% 3.61/1.01  
% 3.61/1.01  fof(f49,plain,(
% 3.61/1.01    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f48,plain,(
% 3.61/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f50,plain,(
% 3.61/1.01    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f49,f48])).
% 3.61/1.01  
% 3.61/1.01  fof(f85,plain,(
% 3.61/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f80,plain,(
% 3.61/1.01    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f10,axiom,(
% 3.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f29,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.01    inference(ennf_transformation,[],[f10])).
% 3.61/1.01  
% 3.61/1.01  fof(f61,plain,(
% 3.61/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f29])).
% 3.61/1.01  
% 3.61/1.01  fof(f9,axiom,(
% 3.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f23,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.61/1.01    inference(pure_predicate_removal,[],[f9])).
% 3.61/1.01  
% 3.61/1.01  fof(f28,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.01    inference(ennf_transformation,[],[f23])).
% 3.61/1.01  
% 3.61/1.01  fof(f60,plain,(
% 3.61/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f28])).
% 3.61/1.01  
% 3.61/1.01  fof(f13,axiom,(
% 3.61/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f34,plain,(
% 3.61/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.61/1.01    inference(ennf_transformation,[],[f13])).
% 3.61/1.01  
% 3.61/1.01  fof(f35,plain,(
% 3.61/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.61/1.01    inference(flattening,[],[f34])).
% 3.61/1.01  
% 3.61/1.01  fof(f47,plain,(
% 3.61/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.61/1.01    inference(nnf_transformation,[],[f35])).
% 3.61/1.01  
% 3.61/1.01  fof(f67,plain,(
% 3.61/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f47])).
% 3.61/1.01  
% 3.61/1.01  fof(f12,axiom,(
% 3.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f32,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.01    inference(ennf_transformation,[],[f12])).
% 3.61/1.01  
% 3.61/1.01  fof(f33,plain,(
% 3.61/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.01    inference(flattening,[],[f32])).
% 3.61/1.01  
% 3.61/1.01  fof(f66,plain,(
% 3.61/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f33])).
% 3.61/1.01  
% 3.61/1.01  fof(f79,plain,(
% 3.61/1.01    v3_funct_2(sK1,sK0,sK0)),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f77,plain,(
% 3.61/1.01    v1_funct_1(sK1)),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f5,axiom,(
% 3.61/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f55,plain,(
% 3.61/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f5])).
% 3.61/1.01  
% 3.61/1.01  fof(f3,axiom,(
% 3.61/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f25,plain,(
% 3.61/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.61/1.01    inference(ennf_transformation,[],[f3])).
% 3.61/1.01  
% 3.61/1.01  fof(f53,plain,(
% 3.61/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f25])).
% 3.61/1.01  
% 3.61/1.01  fof(f19,axiom,(
% 3.61/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f42,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.61/1.01    inference(ennf_transformation,[],[f19])).
% 3.61/1.01  
% 3.61/1.01  fof(f43,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.61/1.01    inference(flattening,[],[f42])).
% 3.61/1.01  
% 3.61/1.01  fof(f76,plain,(
% 3.61/1.01    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f43])).
% 3.61/1.01  
% 3.61/1.01  fof(f18,axiom,(
% 3.61/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f40,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.61/1.01    inference(ennf_transformation,[],[f18])).
% 3.61/1.01  
% 3.61/1.01  fof(f41,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.61/1.01    inference(flattening,[],[f40])).
% 3.61/1.01  
% 3.61/1.01  fof(f74,plain,(
% 3.61/1.01    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f41])).
% 3.61/1.01  
% 3.61/1.01  fof(f78,plain,(
% 3.61/1.01    v1_funct_2(sK1,sK0,sK0)),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f81,plain,(
% 3.61/1.01    v1_funct_1(sK2)),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f82,plain,(
% 3.61/1.01    v1_funct_2(sK2,sK0,sK0)),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f84,plain,(
% 3.61/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f86,plain,(
% 3.61/1.01    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f16,axiom,(
% 3.61/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f38,plain,(
% 3.61/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.61/1.01    inference(ennf_transformation,[],[f16])).
% 3.61/1.01  
% 3.61/1.01  fof(f39,plain,(
% 3.61/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.61/1.01    inference(flattening,[],[f38])).
% 3.61/1.01  
% 3.61/1.01  fof(f72,plain,(
% 3.61/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f39])).
% 3.61/1.01  
% 3.61/1.01  fof(f11,axiom,(
% 3.61/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f30,plain,(
% 3.61/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.61/1.01    inference(ennf_transformation,[],[f11])).
% 3.61/1.01  
% 3.61/1.01  fof(f31,plain,(
% 3.61/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.01    inference(flattening,[],[f30])).
% 3.61/1.01  
% 3.61/1.01  fof(f46,plain,(
% 3.61/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.01    inference(nnf_transformation,[],[f31])).
% 3.61/1.01  
% 3.61/1.01  fof(f63,plain,(
% 3.61/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f46])).
% 3.61/1.01  
% 3.61/1.01  fof(f91,plain,(
% 3.61/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.01    inference(equality_resolution,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  fof(f6,axiom,(
% 3.61/1.01    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f26,plain,(
% 3.61/1.01    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.61/1.01    inference(ennf_transformation,[],[f6])).
% 3.61/1.01  
% 3.61/1.01  fof(f27,plain,(
% 3.61/1.01    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.61/1.01    inference(flattening,[],[f26])).
% 3.61/1.01  
% 3.61/1.01  fof(f56,plain,(
% 3.61/1.01    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f27])).
% 3.61/1.01  
% 3.61/1.01  fof(f1,axiom,(
% 3.61/1.01    v1_xboole_0(k1_xboole_0)),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f51,plain,(
% 3.61/1.01    v1_xboole_0(k1_xboole_0)),
% 3.61/1.01    inference(cnf_transformation,[],[f1])).
% 3.61/1.01  
% 3.61/1.01  fof(f2,axiom,(
% 3.61/1.01    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f24,plain,(
% 3.61/1.01    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.61/1.01    inference(ennf_transformation,[],[f2])).
% 3.61/1.01  
% 3.61/1.01  fof(f52,plain,(
% 3.61/1.01    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f24])).
% 3.61/1.01  
% 3.61/1.01  fof(f7,axiom,(
% 3.61/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f58,plain,(
% 3.61/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.61/1.01    inference(cnf_transformation,[],[f7])).
% 3.61/1.01  
% 3.61/1.01  fof(f17,axiom,(
% 3.61/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f73,plain,(
% 3.61/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f17])).
% 3.61/1.01  
% 3.61/1.01  fof(f88,plain,(
% 3.61/1.01    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.61/1.01    inference(definition_unfolding,[],[f58,f73])).
% 3.61/1.01  
% 3.61/1.01  fof(f4,axiom,(
% 3.61/1.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f54,plain,(
% 3.61/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f4])).
% 3.61/1.01  
% 3.61/1.01  fof(f87,plain,(
% 3.61/1.01    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.61/1.01    inference(definition_unfolding,[],[f54,f73])).
% 3.61/1.01  
% 3.61/1.01  fof(f8,axiom,(
% 3.61/1.01    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f59,plain,(
% 3.61/1.01    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f8])).
% 3.61/1.01  
% 3.61/1.01  fof(f90,plain,(
% 3.61/1.01    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.61/1.01    inference(definition_unfolding,[],[f59,f73,f73])).
% 3.61/1.01  
% 3.61/1.01  fof(f83,plain,(
% 3.61/1.01    v3_funct_2(sK2,sK0,sK0)),
% 3.61/1.01    inference(cnf_transformation,[],[f50])).
% 3.61/1.01  
% 3.61/1.01  fof(f15,axiom,(
% 3.61/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.61/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f22,plain,(
% 3.61/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.61/1.01    inference(pure_predicate_removal,[],[f15])).
% 3.61/1.01  
% 3.61/1.01  fof(f71,plain,(
% 3.61/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f22])).
% 3.61/1.01  
% 3.61/1.01  cnf(c_26,negated_conjecture,
% 3.61/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.61/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1603,plain,
% 3.61/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_31,negated_conjecture,
% 3.61/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.61/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1599,plain,
% 3.61/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_10,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1610,plain,
% 3.61/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.61/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2818,plain,
% 3.61/1.01      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_1599,c_1610]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_9,plain,
% 3.61/1.01      ( v5_relat_1(X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.61/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_17,plain,
% 3.61/1.01      ( ~ v2_funct_2(X0,X1)
% 3.61/1.01      | ~ v5_relat_1(X0,X1)
% 3.61/1.01      | ~ v1_relat_1(X0)
% 3.61/1.01      | k2_relat_1(X0) = X1 ),
% 3.61/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_13,plain,
% 3.61/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.61/1.01      | v2_funct_2(X0,X2)
% 3.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.01      | ~ v1_funct_1(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_32,negated_conjecture,
% 3.61/1.01      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_404,plain,
% 3.61/1.01      ( v2_funct_2(X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.61/1.01      | ~ v1_funct_1(X0)
% 3.61/1.01      | sK1 != X0
% 3.61/1.01      | sK0 != X1
% 3.61/1.01      | sK0 != X2 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_405,plain,
% 3.61/1.01      ( v2_funct_2(sK1,sK0)
% 3.61/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.61/1.01      | ~ v1_funct_1(sK1) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_404]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_34,negated_conjecture,
% 3.61/1.01      ( v1_funct_1(sK1) ),
% 3.61/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_407,plain,
% 3.61/1.01      ( v2_funct_2(sK1,sK0) ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_405,c_34,c_31]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_490,plain,
% 3.61/1.01      ( ~ v5_relat_1(X0,X1)
% 3.61/1.01      | ~ v1_relat_1(X0)
% 3.61/1.01      | k2_relat_1(X0) = X1
% 3.61/1.01      | sK1 != X0
% 3.61/1.01      | sK0 != X1 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_407]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_491,plain,
% 3.61/1.01      ( ~ v5_relat_1(sK1,sK0)
% 3.61/1.01      | ~ v1_relat_1(sK1)
% 3.61/1.01      | k2_relat_1(sK1) = sK0 ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_490]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_537,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.01      | ~ v1_relat_1(sK1)
% 3.61/1.01      | k2_relat_1(sK1) = sK0
% 3.61/1.01      | sK1 != X0
% 3.61/1.01      | sK0 != X2 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_491]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_538,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.61/1.01      | ~ v1_relat_1(sK1)
% 3.61/1.01      | k2_relat_1(sK1) = sK0 ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_537]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_540,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.61/1.01      | ~ v1_relat_1(sK1)
% 3.61/1.01      | k2_relat_1(sK1) = sK0 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_538]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_542,plain,
% 3.61/1.01      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_538,c_31,c_540]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1593,plain,
% 3.61/1.01      ( k2_relat_1(sK1) = sK0 | v1_relat_1(sK1) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4,plain,
% 3.61/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.61/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_98,plain,
% 3.61/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/1.01      | ~ v1_relat_1(X1)
% 3.61/1.01      | v1_relat_1(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1674,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
% 3.61/1.01      | ~ v1_relat_1(X0)
% 3.61/1.01      | v1_relat_1(sK1) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1744,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.61/1.01      | v1_relat_1(sK1) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1674]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1746,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.61/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.61/1.01      | v1_relat_1(sK1) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1744]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2453,plain,
% 3.61/1.01      ( k2_relat_1(sK1) = sK0 ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_1593,c_31,c_98,c_540,c_1746]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2819,plain,
% 3.61/1.01      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.61/1.01      inference(light_normalisation,[status(thm)],[c_2818,c_2453]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_24,plain,
% 3.61/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.61/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.61/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.61/1.01      | ~ v2_funct_1(X2)
% 3.61/1.01      | ~ v1_funct_1(X2)
% 3.61/1.01      | ~ v1_funct_1(X3)
% 3.61/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.61/1.01      | k2_funct_1(X2) = X3
% 3.61/1.01      | k1_xboole_0 = X1
% 3.61/1.01      | k1_xboole_0 = X0 ),
% 3.61/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_23,plain,
% 3.61/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.61/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.61/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.61/1.01      | v2_funct_1(X2)
% 3.61/1.01      | ~ v1_funct_1(X2)
% 3.61/1.01      | ~ v1_funct_1(X3) ),
% 3.61/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_183,plain,
% 3.61/1.01      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.61/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.61/1.01      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.61/1.01      | ~ v1_funct_1(X2)
% 3.61/1.01      | ~ v1_funct_1(X3)
% 3.61/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.61/1.01      | k2_funct_1(X2) = X3
% 3.61/1.01      | k1_xboole_0 = X1
% 3.61/1.01      | k1_xboole_0 = X0 ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_24,c_23]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_184,plain,
% 3.61/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.61/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.61/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.01      | ~ v1_funct_1(X2)
% 3.61/1.01      | ~ v1_funct_1(X3)
% 3.61/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.61/1.01      | k2_funct_1(X2) = X3
% 3.61/1.01      | k1_xboole_0 = X0
% 3.61/1.01      | k1_xboole_0 = X1 ),
% 3.61/1.01      inference(renaming,[status(thm)],[c_183]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1596,plain,
% 3.61/1.01      ( k2_relset_1(X0,X1,X2) != X1
% 3.61/1.01      | k2_funct_1(X2) = X3
% 3.61/1.01      | k1_xboole_0 = X0
% 3.61/1.01      | k1_xboole_0 = X1
% 3.61/1.01      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.61/1.01      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.61/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.61/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.61/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.61/1.01      | v1_funct_1(X2) != iProver_top
% 3.61/1.01      | v1_funct_1(X3) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3517,plain,
% 3.61/1.01      ( k2_funct_1(sK1) = X0
% 3.61/1.01      | sK0 = k1_xboole_0
% 3.61/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.61/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.61/1.01      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.61/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.61/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.61/1.01      | v1_funct_1(X0) != iProver_top
% 3.61/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2819,c_1596]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_35,plain,
% 3.61/1.01      ( v1_funct_1(sK1) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_33,negated_conjecture,
% 3.61/1.01      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_36,plain,
% 3.61/1.01      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_38,plain,
% 3.61/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5060,plain,
% 3.61/1.01      ( v1_funct_1(X0) != iProver_top
% 3.61/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.61/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.61/1.01      | sK0 = k1_xboole_0
% 3.61/1.01      | k2_funct_1(sK1) = X0
% 3.61/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_3517,c_35,c_36,c_38]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5061,plain,
% 3.61/1.01      ( k2_funct_1(sK1) = X0
% 3.61/1.01      | sK0 = k1_xboole_0
% 3.61/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.61/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.61/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.61/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.61/1.01      inference(renaming,[status(thm)],[c_5060]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5066,plain,
% 3.61/1.01      ( k2_funct_1(sK1) = sK2
% 3.61/1.01      | sK0 = k1_xboole_0
% 3.61/1.01      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.61/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_1603,c_5061]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_30,negated_conjecture,
% 3.61/1.01      ( v1_funct_1(sK2) ),
% 3.61/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_29,negated_conjecture,
% 3.61/1.01      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_27,negated_conjecture,
% 3.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.61/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5067,plain,
% 3.61/1.01      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.61/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.61/1.01      | ~ v1_funct_1(sK2)
% 3.61/1.01      | k2_funct_1(sK1) = sK2
% 3.61/1.01      | sK0 = k1_xboole_0 ),
% 3.61/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_5066]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5069,plain,
% 3.61/1.01      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_5066,c_39,c_40,c_42]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5070,plain,
% 3.61/1.01      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.61/1.01      inference(renaming,[status(thm)],[c_5069]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_25,negated_conjecture,
% 3.61/1.01      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.61/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1604,plain,
% 3.61/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_21,plain,
% 3.61/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.61/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.61/1.01      | ~ v1_funct_1(X0)
% 3.61/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_423,plain,
% 3.61/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.61/1.01      | ~ v1_funct_1(X0)
% 3.61/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.61/1.01      | sK1 != X0
% 3.61/1.01      | sK0 != X1 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_424,plain,
% 3.61/1.01      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.61/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.61/1.01      | ~ v1_funct_1(sK1)
% 3.61/1.01      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_423]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_426,plain,
% 3.61/1.01      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_424,c_34,c_33,c_31]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1617,plain,
% 3.61/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.61/1.01      inference(light_normalisation,[status(thm)],[c_1604,c_426]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5071,plain,
% 3.61/1.01      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_5070,c_1617]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_42,plain,
% 3.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_11,plain,
% 3.61/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.61/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1784,plain,
% 3.61/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.61/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1785,plain,
% 3.61/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_1784]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5210,plain,
% 3.61/1.01      ( sK0 = k1_xboole_0 ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_5071,c_42,c_1785]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5,plain,
% 3.61/1.01      ( ~ v1_relat_1(X0)
% 3.61/1.01      | v1_xboole_0(X0)
% 3.61/1.01      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 3.61/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1611,plain,
% 3.61/1.01      ( v1_relat_1(X0) != iProver_top
% 3.61/1.01      | v1_xboole_0(X0) = iProver_top
% 3.61/1.01      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2996,plain,
% 3.61/1.01      ( v1_relat_1(sK1) != iProver_top
% 3.61/1.01      | v1_xboole_0(sK1) = iProver_top
% 3.61/1.01      | v1_xboole_0(sK0) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2453,c_1611]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_97,plain,
% 3.61/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_99,plain,
% 3.61/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_97]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1745,plain,
% 3.61/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.61/1.01      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 3.61/1.01      | v1_relat_1(sK1) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_1744]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1747,plain,
% 3.61/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.61/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.61/1.01      | v1_relat_1(sK1) = iProver_top ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1745]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3414,plain,
% 3.61/1.01      ( v1_xboole_0(sK1) = iProver_top
% 3.61/1.01      | v1_xboole_0(sK0) != iProver_top ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_2996,c_38,c_99,c_1747]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5222,plain,
% 3.61/1.01      ( v1_xboole_0(sK1) = iProver_top
% 3.61/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.61/1.01      inference(demodulation,[status(thm)],[c_5210,c_3414]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_0,plain,
% 3.61/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_107,plain,
% 3.61/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1161,plain,
% 3.61/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.61/1.01      theory(equality) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3205,plain,
% 3.61/1.01      ( v1_xboole_0(X0)
% 3.61/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 3.61/1.01      | X0 != k1_xboole_0 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1161]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3206,plain,
% 3.61/1.01      ( X0 != k1_xboole_0
% 3.61/1.01      | v1_xboole_0(X0) = iProver_top
% 3.61/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_3205]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3208,plain,
% 3.61/1.01      ( sK0 != k1_xboole_0
% 3.61/1.01      | v1_xboole_0(sK0) = iProver_top
% 3.61/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_3206]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_8117,plain,
% 3.61/1.01      ( v1_xboole_0(sK1) = iProver_top ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_5222,c_38,c_42,c_99,c_107,c_1747,c_1785,c_2996,c_3208,
% 3.61/1.01                 c_5071]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1616,plain,
% 3.61/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1,plain,
% 3.61/1.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.61/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1615,plain,
% 3.61/1.01      ( X0 = X1
% 3.61/1.01      | v1_xboole_0(X1) != iProver_top
% 3.61/1.01      | v1_xboole_0(X0) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2593,plain,
% 3.61/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_1616,c_1615]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_8123,plain,
% 3.61/1.01      ( sK1 = k1_xboole_0 ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_8117,c_2593]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5230,plain,
% 3.61/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.61/1.01      inference(demodulation,[status(thm)],[c_5210,c_1617]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_10182,plain,
% 3.61/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.61/1.01      inference(demodulation,[status(thm)],[c_8123,c_5230]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_6,plain,
% 3.61/1.01      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.61/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2994,plain,
% 3.61/1.01      ( v1_relat_1(k6_partfun1(X0)) != iProver_top
% 3.61/1.01      | v1_xboole_0(X0) != iProver_top
% 3.61/1.01      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_6,c_1611]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3,plain,
% 3.61/1.01      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.61/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_100,plain,
% 3.61/1.01      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3683,plain,
% 3.61/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.61/1.01      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_2994,c_100]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3690,plain,
% 3.61/1.01      ( k6_partfun1(X0) = X1
% 3.61/1.01      | v1_xboole_0(X0) != iProver_top
% 3.61/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_3683,c_1615]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4448,plain,
% 3.61/1.01      ( k6_partfun1(k1_xboole_0) = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_1616,c_3690]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4457,plain,
% 3.61/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_1616,c_4448]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_8,plain,
% 3.61/1.01      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4609,plain,
% 3.61/1.01      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_4457,c_8]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4612,plain,
% 3.61/1.01      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.61/1.01      inference(demodulation,[status(thm)],[c_4609,c_4457]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_28,negated_conjecture,
% 3.61/1.01      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_393,plain,
% 3.61/1.01      ( v2_funct_2(X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.61/1.01      | ~ v1_funct_1(X0)
% 3.61/1.01      | sK2 != X0
% 3.61/1.01      | sK0 != X1
% 3.61/1.01      | sK0 != X2 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_394,plain,
% 3.61/1.01      ( v2_funct_2(sK2,sK0)
% 3.61/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.61/1.01      | ~ v1_funct_1(sK2) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_393]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_396,plain,
% 3.61/1.01      ( v2_funct_2(sK2,sK0) ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_394,c_30,c_27]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_477,plain,
% 3.61/1.01      ( ~ v5_relat_1(X0,X1)
% 3.61/1.01      | ~ v1_relat_1(X0)
% 3.61/1.01      | k2_relat_1(X0) = X1
% 3.61/1.01      | sK2 != X0
% 3.61/1.01      | sK0 != X1 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_396]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_478,plain,
% 3.61/1.01      ( ~ v5_relat_1(sK2,sK0)
% 3.61/1.01      | ~ v1_relat_1(sK2)
% 3.61/1.01      | k2_relat_1(sK2) = sK0 ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_477]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_521,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.01      | ~ v1_relat_1(sK2)
% 3.61/1.01      | k2_relat_1(sK2) = sK0
% 3.61/1.01      | sK2 != X0
% 3.61/1.01      | sK0 != X2 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_478]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_522,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.61/1.01      | ~ v1_relat_1(sK2)
% 3.61/1.01      | k2_relat_1(sK2) = sK0 ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_521]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_524,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.61/1.01      | ~ v1_relat_1(sK2)
% 3.61/1.01      | k2_relat_1(sK2) = sK0 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_522]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_526,plain,
% 3.61/1.01      ( ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK0 ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_522,c_27,c_524]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1594,plain,
% 3.61/1.01      ( k2_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1664,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.61/1.01      | ~ v1_relat_1(X0)
% 3.61/1.01      | v1_relat_1(sK2) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1705,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.61/1.01      | v1_relat_1(sK2) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1664]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1707,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.61/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.61/1.01      | v1_relat_1(sK2) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1705]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2513,plain,
% 3.61/1.01      ( k2_relat_1(sK2) = sK0 ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_1594,c_27,c_98,c_524,c_1707]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2995,plain,
% 3.61/1.01      ( v1_relat_1(sK2) != iProver_top
% 3.61/1.01      | v1_xboole_0(sK2) = iProver_top
% 3.61/1.01      | v1_xboole_0(sK0) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2513,c_1611]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1706,plain,
% 3.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.61/1.01      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 3.61/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_1705]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1708,plain,
% 3.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.61/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.61/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1706]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3409,plain,
% 3.61/1.01      ( v1_xboole_0(sK2) = iProver_top
% 3.61/1.01      | v1_xboole_0(sK0) != iProver_top ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_2995,c_42,c_99,c_1708]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5223,plain,
% 3.61/1.01      ( v1_xboole_0(sK2) = iProver_top
% 3.61/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.61/1.01      inference(demodulation,[status(thm)],[c_5210,c_3409]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_8637,plain,
% 3.61/1.01      ( v1_xboole_0(sK2) = iProver_top ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_5223,c_42,c_99,c_107,c_1708,c_1785,c_2995,c_3208,
% 3.61/1.01                 c_5071]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_8643,plain,
% 3.61/1.01      ( sK2 = k1_xboole_0 ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_8637,c_2593]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_10190,plain,
% 3.61/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.61/1.01      inference(light_normalisation,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_10182,c_4612,c_8643]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_20,plain,
% 3.61/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.61/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1605,plain,
% 3.61/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1609,plain,
% 3.61/1.01      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.61/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2807,plain,
% 3.61/1.01      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_1605,c_1609]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4604,plain,
% 3.61/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_4457,c_2807]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(contradiction,plain,
% 3.61/1.01      ( $false ),
% 3.61/1.01      inference(minisat,[status(thm)],[c_10190,c_4604]) ).
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/1.01  
% 3.61/1.01  ------                               Statistics
% 3.61/1.01  
% 3.61/1.01  ------ General
% 3.61/1.01  
% 3.61/1.01  abstr_ref_over_cycles:                  0
% 3.61/1.01  abstr_ref_under_cycles:                 0
% 3.61/1.01  gc_basic_clause_elim:                   0
% 3.61/1.01  forced_gc_time:                         0
% 3.61/1.01  parsing_time:                           0.007
% 3.61/1.01  unif_index_cands_time:                  0.
% 3.61/1.01  unif_index_add_time:                    0.
% 3.61/1.01  orderings_time:                         0.
% 3.61/1.01  out_proof_time:                         0.011
% 3.61/1.01  total_time:                             0.377
% 3.61/1.01  num_of_symbols:                         54
% 3.61/1.01  num_of_terms:                           13789
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing
% 3.61/1.01  
% 3.61/1.01  num_of_splits:                          0
% 3.61/1.01  num_of_split_atoms:                     0
% 3.61/1.01  num_of_reused_defs:                     0
% 3.61/1.01  num_eq_ax_congr_red:                    12
% 3.61/1.01  num_of_sem_filtered_clauses:            3
% 3.61/1.01  num_of_subtypes:                        0
% 3.61/1.01  monotx_restored_types:                  0
% 3.61/1.01  sat_num_of_epr_types:                   0
% 3.61/1.01  sat_num_of_non_cyclic_types:            0
% 3.61/1.01  sat_guarded_non_collapsed_types:        0
% 3.61/1.01  num_pure_diseq_elim:                    0
% 3.61/1.01  simp_replaced_by:                       0
% 3.61/1.01  res_preprocessed:                       154
% 3.61/1.01  prep_upred:                             0
% 3.61/1.01  prep_unflattend:                        62
% 3.61/1.01  smt_new_axioms:                         0
% 3.61/1.01  pred_elim_cands:                        6
% 3.61/1.01  pred_elim:                              3
% 3.61/1.01  pred_elim_cl:                           3
% 3.61/1.01  pred_elim_cycles:                       6
% 3.61/1.01  merged_defs:                            0
% 3.61/1.01  merged_defs_ncl:                        0
% 3.61/1.01  bin_hyper_res:                          0
% 3.61/1.01  prep_cycles:                            4
% 3.61/1.01  pred_elim_time:                         0.015
% 3.61/1.01  splitting_time:                         0.
% 3.61/1.01  sem_filter_time:                        0.
% 3.61/1.01  monotx_time:                            0.
% 3.61/1.01  subtype_inf_time:                       0.
% 3.61/1.01  
% 3.61/1.01  ------ Problem properties
% 3.61/1.01  
% 3.61/1.01  clauses:                                29
% 3.61/1.01  conjectures:                            8
% 3.61/1.01  epr:                                    6
% 3.61/1.01  horn:                                   28
% 3.61/1.01  ground:                                 13
% 3.61/1.01  unary:                                  17
% 3.61/1.01  binary:                                 4
% 3.61/1.01  lits:                                   68
% 3.61/1.01  lits_eq:                                15
% 3.61/1.01  fd_pure:                                0
% 3.61/1.01  fd_pseudo:                              0
% 3.61/1.01  fd_cond:                                0
% 3.61/1.01  fd_pseudo_cond:                         4
% 3.61/1.01  ac_symbols:                             0
% 3.61/1.01  
% 3.61/1.01  ------ Propositional Solver
% 3.61/1.01  
% 3.61/1.01  prop_solver_calls:                      29
% 3.61/1.01  prop_fast_solver_calls:                 1371
% 3.61/1.01  smt_solver_calls:                       0
% 3.61/1.01  smt_fast_solver_calls:                  0
% 3.61/1.01  prop_num_of_clauses:                    4162
% 3.61/1.01  prop_preprocess_simplified:             11755
% 3.61/1.01  prop_fo_subsumed:                       50
% 3.61/1.01  prop_solver_time:                       0.
% 3.61/1.01  smt_solver_time:                        0.
% 3.61/1.01  smt_fast_solver_time:                   0.
% 3.61/1.01  prop_fast_solver_time:                  0.
% 3.61/1.01  prop_unsat_core_time:                   0.
% 3.61/1.01  
% 3.61/1.01  ------ QBF
% 3.61/1.01  
% 3.61/1.01  qbf_q_res:                              0
% 3.61/1.01  qbf_num_tautologies:                    0
% 3.61/1.01  qbf_prep_cycles:                        0
% 3.61/1.01  
% 3.61/1.01  ------ BMC1
% 3.61/1.01  
% 3.61/1.01  bmc1_current_bound:                     -1
% 3.61/1.01  bmc1_last_solved_bound:                 -1
% 3.61/1.01  bmc1_unsat_core_size:                   -1
% 3.61/1.01  bmc1_unsat_core_parents_size:           -1
% 3.61/1.01  bmc1_merge_next_fun:                    0
% 3.61/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.61/1.01  
% 3.61/1.01  ------ Instantiation
% 3.61/1.01  
% 3.61/1.01  inst_num_of_clauses:                    1230
% 3.61/1.01  inst_num_in_passive:                    606
% 3.61/1.01  inst_num_in_active:                     457
% 3.61/1.01  inst_num_in_unprocessed:                167
% 3.61/1.01  inst_num_of_loops:                      570
% 3.61/1.01  inst_num_of_learning_restarts:          0
% 3.61/1.01  inst_num_moves_active_passive:          111
% 3.61/1.01  inst_lit_activity:                      0
% 3.61/1.01  inst_lit_activity_moves:                0
% 3.61/1.01  inst_num_tautologies:                   0
% 3.61/1.01  inst_num_prop_implied:                  0
% 3.61/1.01  inst_num_existing_simplified:           0
% 3.61/1.01  inst_num_eq_res_simplified:             0
% 3.61/1.01  inst_num_child_elim:                    0
% 3.61/1.01  inst_num_of_dismatching_blockings:      405
% 3.61/1.01  inst_num_of_non_proper_insts:           1597
% 3.61/1.01  inst_num_of_duplicates:                 0
% 3.61/1.01  inst_inst_num_from_inst_to_res:         0
% 3.61/1.01  inst_dismatching_checking_time:         0.
% 3.61/1.01  
% 3.61/1.01  ------ Resolution
% 3.61/1.01  
% 3.61/1.01  res_num_of_clauses:                     0
% 3.61/1.01  res_num_in_passive:                     0
% 3.61/1.01  res_num_in_active:                      0
% 3.61/1.01  res_num_of_loops:                       158
% 3.61/1.01  res_forward_subset_subsumed:            88
% 3.61/1.01  res_backward_subset_subsumed:           0
% 3.61/1.01  res_forward_subsumed:                   0
% 3.61/1.01  res_backward_subsumed:                  0
% 3.61/1.01  res_forward_subsumption_resolution:     3
% 3.61/1.01  res_backward_subsumption_resolution:    0
% 3.61/1.01  res_clause_to_clause_subsumption:       369
% 3.61/1.01  res_orphan_elimination:                 0
% 3.61/1.01  res_tautology_del:                      157
% 3.61/1.01  res_num_eq_res_simplified:              0
% 3.61/1.01  res_num_sel_changes:                    0
% 3.61/1.01  res_moves_from_active_to_pass:          0
% 3.61/1.01  
% 3.61/1.01  ------ Superposition
% 3.61/1.01  
% 3.61/1.01  sup_time_total:                         0.
% 3.61/1.01  sup_time_generating:                    0.
% 3.61/1.01  sup_time_sim_full:                      0.
% 3.61/1.01  sup_time_sim_immed:                     0.
% 3.61/1.01  
% 3.61/1.01  sup_num_of_clauses:                     88
% 3.61/1.01  sup_num_in_active:                      62
% 3.61/1.01  sup_num_in_passive:                     26
% 3.61/1.01  sup_num_of_loops:                       113
% 3.61/1.01  sup_fw_superposition:                   101
% 3.61/1.01  sup_bw_superposition:                   61
% 3.61/1.01  sup_immediate_simplified:               67
% 3.61/1.01  sup_given_eliminated:                   3
% 3.61/1.01  comparisons_done:                       0
% 3.61/1.01  comparisons_avoided:                    3
% 3.61/1.01  
% 3.61/1.01  ------ Simplifications
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  sim_fw_subset_subsumed:                 21
% 3.61/1.01  sim_bw_subset_subsumed:                 8
% 3.61/1.01  sim_fw_subsumed:                        2
% 3.61/1.01  sim_bw_subsumed:                        1
% 3.61/1.01  sim_fw_subsumption_res:                 0
% 3.61/1.01  sim_bw_subsumption_res:                 0
% 3.61/1.01  sim_tautology_del:                      3
% 3.61/1.01  sim_eq_tautology_del:                   25
% 3.61/1.01  sim_eq_res_simp:                        0
% 3.61/1.01  sim_fw_demodulated:                     6
% 3.61/1.01  sim_bw_demodulated:                     52
% 3.61/1.01  sim_light_normalised:                   47
% 3.61/1.01  sim_joinable_taut:                      0
% 3.61/1.01  sim_joinable_simp:                      0
% 3.61/1.01  sim_ac_normalised:                      0
% 3.61/1.01  sim_smt_subsumption:                    0
% 3.61/1.01  
%------------------------------------------------------------------------------
