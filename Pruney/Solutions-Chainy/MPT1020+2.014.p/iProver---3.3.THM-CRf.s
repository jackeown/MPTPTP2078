%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:07 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_57)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f116,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f133,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f92,f116])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f137,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f96,f116])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f91,f116])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f131,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f89,f116])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f98,f116])).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f130,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f90,f116])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f136,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f97,f116])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f134,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f95,f116])).

fof(f30,conjecture,(
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

fof(f31,negated_conjecture,(
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
    inference(negated_conjecture,[],[f30])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f74,plain,(
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

fof(f73,plain,
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

fof(f75,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f63,f74,f73])).

fof(f128,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f75])).

fof(f123,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f75])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f122,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f120,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f29,axiom,(
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

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f119,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f28,axiom,(
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

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f121,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f124,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

fof(f125,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f127,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f75])).

fof(f129,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f75])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f141,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f106])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f68])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f140,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f139,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_21,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_3599,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5177,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_3599])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_3602,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5703,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5177,c_3602])).

cnf(c_14,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_4442,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16,c_14])).

cnf(c_5704,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5703,c_16,c_4442])).

cnf(c_22,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_3597,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12747,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | k6_partfun1(k2_relat_1(k1_xboole_0)) != k1_xboole_0
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5704,c_3597])).

cnf(c_13,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_4235,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16,c_13])).

cnf(c_12751,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12747,c_16,c_4235,c_4442])).

cnf(c_12752,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12751])).

cnf(c_20,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_3598,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5083,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_3598])).

cnf(c_18,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_3600,plain,
    ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5545,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_3600])).

cnf(c_15158,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12752,c_5083,c_5177,c_5545])).

cnf(c_44,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3584,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_3580,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3593,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8278,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3580,c_3593])).

cnf(c_25,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_35,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_640,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_25,c_35])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_652,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_640,c_24])).

cnf(c_3575,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_6312,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_2(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3580,c_3575])).

cnf(c_31,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_50,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_786,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_50])).

cnf(c_787,plain,
    ( v2_funct_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_52,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_789,plain,
    ( v2_funct_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_52,c_49])).

cnf(c_866,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK2 != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_652,c_789])).

cnf(c_867,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | k2_relat_1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_866])).

cnf(c_869,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_6533,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6312,c_49,c_869])).

cnf(c_8281,plain,
    ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_8278,c_6533])).

cnf(c_42,plain,
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
    inference(cnf_transformation,[],[f119])).

cnf(c_41,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_272,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_42,c_41])).

cnf(c_273,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_3577,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_8623,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8281,c_3577])).

cnf(c_53,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_54,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_8949,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0
    | k2_funct_1(sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8623,c_53,c_54,c_56])).

cnf(c_8950,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8949])).

cnf(c_8955,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3584,c_8950])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_8956,plain,
    ( ~ v1_funct_2(sK3,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8955])).

cnf(c_8958,plain,
    ( sK1 = k1_xboole_0
    | k2_funct_1(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8955,c_57,c_58,c_60])).

cnf(c_8959,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8958])).

cnf(c_43,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_3585,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_805,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_50])).

cnf(c_806,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_808,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_806,c_52,c_51,c_49])).

cnf(c_3611,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3585,c_808])).

cnf(c_8960,plain,
    ( sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8959,c_3611])).

cnf(c_60,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_29,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_3689,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3690,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3689])).

cnf(c_9098,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8960,c_60,c_3690])).

cnf(c_9116,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9098,c_3580])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_9121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9116,c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3594,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_11788,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_3594])).

cnf(c_11868,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9121,c_11788])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_159,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2592,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4659,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_4660,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4659])).

cnf(c_4662,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4660])).

cnf(c_11872,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11868])).

cnf(c_12147,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11868,c_60,c_159,c_3690,c_4662,c_8960,c_11872])).

cnf(c_3607,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3605,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6838,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3607,c_3605])).

cnf(c_12152,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12147,c_6838])).

cnf(c_9111,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9098,c_3611])).

cnf(c_12198,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12152,c_9111])).

cnf(c_3583,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_9115,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9098,c_3583])).

cnf(c_9122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9115,c_7])).

cnf(c_11869,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_9122,c_11788])).

cnf(c_11875,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11869])).

cnf(c_12184,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11869,c_60,c_159,c_3690,c_4662,c_8960,c_11875])).

cnf(c_12189,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12184,c_6838])).

cnf(c_12212,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12198,c_12189])).

cnf(c_15160,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15158,c_12212])).

cnf(c_3592,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6955,plain,
    ( r2_relset_1(sK1,sK1,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3580,c_3592])).

cnf(c_9103,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9098,c_6955])).

cnf(c_12200,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12152,c_9103])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15160,c_12200])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n023.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:19:36 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.05/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/1.47  
% 7.05/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.05/1.47  
% 7.05/1.47  ------  iProver source info
% 7.05/1.47  
% 7.05/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.05/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.05/1.47  git: non_committed_changes: false
% 7.05/1.47  git: last_make_outside_of_git: false
% 7.05/1.47  
% 7.05/1.47  ------ 
% 7.05/1.47  
% 7.05/1.47  ------ Input Options
% 7.05/1.47  
% 7.05/1.47  --out_options                           all
% 7.05/1.47  --tptp_safe_out                         true
% 7.05/1.47  --problem_path                          ""
% 7.05/1.47  --include_path                          ""
% 7.05/1.47  --clausifier                            res/vclausify_rel
% 7.05/1.47  --clausifier_options                    ""
% 7.05/1.47  --stdin                                 false
% 7.05/1.47  --stats_out                             all
% 7.05/1.47  
% 7.05/1.47  ------ General Options
% 7.05/1.47  
% 7.05/1.47  --fof                                   false
% 7.05/1.47  --time_out_real                         305.
% 7.05/1.47  --time_out_virtual                      -1.
% 7.05/1.47  --symbol_type_check                     false
% 7.05/1.47  --clausify_out                          false
% 7.05/1.47  --sig_cnt_out                           false
% 7.05/1.47  --trig_cnt_out                          false
% 7.05/1.47  --trig_cnt_out_tolerance                1.
% 7.05/1.47  --trig_cnt_out_sk_spl                   false
% 7.05/1.47  --abstr_cl_out                          false
% 7.05/1.47  
% 7.05/1.47  ------ Global Options
% 7.05/1.47  
% 7.05/1.47  --schedule                              default
% 7.05/1.47  --add_important_lit                     false
% 7.05/1.47  --prop_solver_per_cl                    1000
% 7.05/1.47  --min_unsat_core                        false
% 7.05/1.47  --soft_assumptions                      false
% 7.05/1.47  --soft_lemma_size                       3
% 7.05/1.47  --prop_impl_unit_size                   0
% 7.05/1.47  --prop_impl_unit                        []
% 7.05/1.47  --share_sel_clauses                     true
% 7.05/1.47  --reset_solvers                         false
% 7.05/1.47  --bc_imp_inh                            [conj_cone]
% 7.05/1.47  --conj_cone_tolerance                   3.
% 7.05/1.47  --extra_neg_conj                        none
% 7.05/1.47  --large_theory_mode                     true
% 7.05/1.47  --prolific_symb_bound                   200
% 7.05/1.47  --lt_threshold                          2000
% 7.05/1.47  --clause_weak_htbl                      true
% 7.05/1.47  --gc_record_bc_elim                     false
% 7.05/1.47  
% 7.05/1.47  ------ Preprocessing Options
% 7.05/1.47  
% 7.05/1.47  --preprocessing_flag                    true
% 7.05/1.47  --time_out_prep_mult                    0.1
% 7.05/1.47  --splitting_mode                        input
% 7.05/1.47  --splitting_grd                         true
% 7.05/1.47  --splitting_cvd                         false
% 7.05/1.47  --splitting_cvd_svl                     false
% 7.05/1.47  --splitting_nvd                         32
% 7.05/1.47  --sub_typing                            true
% 7.05/1.47  --prep_gs_sim                           true
% 7.05/1.47  --prep_unflatten                        true
% 7.05/1.47  --prep_res_sim                          true
% 7.05/1.47  --prep_upred                            true
% 7.05/1.47  --prep_sem_filter                       exhaustive
% 7.05/1.47  --prep_sem_filter_out                   false
% 7.05/1.47  --pred_elim                             true
% 7.05/1.47  --res_sim_input                         true
% 7.05/1.47  --eq_ax_congr_red                       true
% 7.05/1.47  --pure_diseq_elim                       true
% 7.05/1.47  --brand_transform                       false
% 7.05/1.47  --non_eq_to_eq                          false
% 7.05/1.47  --prep_def_merge                        true
% 7.05/1.47  --prep_def_merge_prop_impl              false
% 7.05/1.47  --prep_def_merge_mbd                    true
% 7.05/1.47  --prep_def_merge_tr_red                 false
% 7.05/1.47  --prep_def_merge_tr_cl                  false
% 7.05/1.47  --smt_preprocessing                     true
% 7.05/1.47  --smt_ac_axioms                         fast
% 7.05/1.47  --preprocessed_out                      false
% 7.05/1.47  --preprocessed_stats                    false
% 7.05/1.47  
% 7.05/1.47  ------ Abstraction refinement Options
% 7.05/1.47  
% 7.05/1.47  --abstr_ref                             []
% 7.05/1.47  --abstr_ref_prep                        false
% 7.05/1.47  --abstr_ref_until_sat                   false
% 7.05/1.47  --abstr_ref_sig_restrict                funpre
% 7.05/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.47  --abstr_ref_under                       []
% 7.05/1.47  
% 7.05/1.47  ------ SAT Options
% 7.05/1.47  
% 7.05/1.47  --sat_mode                              false
% 7.05/1.47  --sat_fm_restart_options                ""
% 7.05/1.47  --sat_gr_def                            false
% 7.05/1.47  --sat_epr_types                         true
% 7.05/1.47  --sat_non_cyclic_types                  false
% 7.05/1.47  --sat_finite_models                     false
% 7.05/1.47  --sat_fm_lemmas                         false
% 7.05/1.47  --sat_fm_prep                           false
% 7.05/1.47  --sat_fm_uc_incr                        true
% 7.05/1.47  --sat_out_model                         small
% 7.05/1.47  --sat_out_clauses                       false
% 7.05/1.47  
% 7.05/1.47  ------ QBF Options
% 7.05/1.47  
% 7.05/1.47  --qbf_mode                              false
% 7.05/1.47  --qbf_elim_univ                         false
% 7.05/1.47  --qbf_dom_inst                          none
% 7.05/1.47  --qbf_dom_pre_inst                      false
% 7.05/1.47  --qbf_sk_in                             false
% 7.05/1.47  --qbf_pred_elim                         true
% 7.05/1.47  --qbf_split                             512
% 7.05/1.47  
% 7.05/1.47  ------ BMC1 Options
% 7.05/1.47  
% 7.05/1.47  --bmc1_incremental                      false
% 7.05/1.47  --bmc1_axioms                           reachable_all
% 7.05/1.47  --bmc1_min_bound                        0
% 7.05/1.47  --bmc1_max_bound                        -1
% 7.05/1.47  --bmc1_max_bound_default                -1
% 7.05/1.47  --bmc1_symbol_reachability              true
% 7.05/1.47  --bmc1_property_lemmas                  false
% 7.05/1.47  --bmc1_k_induction                      false
% 7.05/1.47  --bmc1_non_equiv_states                 false
% 7.05/1.47  --bmc1_deadlock                         false
% 7.05/1.47  --bmc1_ucm                              false
% 7.05/1.47  --bmc1_add_unsat_core                   none
% 7.05/1.47  --bmc1_unsat_core_children              false
% 7.05/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.47  --bmc1_out_stat                         full
% 7.05/1.47  --bmc1_ground_init                      false
% 7.05/1.47  --bmc1_pre_inst_next_state              false
% 7.05/1.47  --bmc1_pre_inst_state                   false
% 7.05/1.47  --bmc1_pre_inst_reach_state             false
% 7.05/1.47  --bmc1_out_unsat_core                   false
% 7.05/1.47  --bmc1_aig_witness_out                  false
% 7.05/1.47  --bmc1_verbose                          false
% 7.05/1.47  --bmc1_dump_clauses_tptp                false
% 7.05/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.47  --bmc1_dump_file                        -
% 7.05/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.47  --bmc1_ucm_extend_mode                  1
% 7.05/1.47  --bmc1_ucm_init_mode                    2
% 7.05/1.47  --bmc1_ucm_cone_mode                    none
% 7.05/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.47  --bmc1_ucm_relax_model                  4
% 7.05/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.47  --bmc1_ucm_layered_model                none
% 7.05/1.47  --bmc1_ucm_max_lemma_size               10
% 7.05/1.47  
% 7.05/1.47  ------ AIG Options
% 7.05/1.47  
% 7.05/1.47  --aig_mode                              false
% 7.05/1.47  
% 7.05/1.47  ------ Instantiation Options
% 7.05/1.47  
% 7.05/1.47  --instantiation_flag                    true
% 7.05/1.47  --inst_sos_flag                         true
% 7.05/1.47  --inst_sos_phase                        true
% 7.05/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.47  --inst_lit_sel_side                     num_symb
% 7.05/1.47  --inst_solver_per_active                1400
% 7.05/1.47  --inst_solver_calls_frac                1.
% 7.05/1.47  --inst_passive_queue_type               priority_queues
% 7.05/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.47  --inst_passive_queues_freq              [25;2]
% 7.05/1.47  --inst_dismatching                      true
% 7.05/1.47  --inst_eager_unprocessed_to_passive     true
% 7.05/1.47  --inst_prop_sim_given                   true
% 7.05/1.47  --inst_prop_sim_new                     false
% 7.05/1.47  --inst_subs_new                         false
% 7.05/1.47  --inst_eq_res_simp                      false
% 7.05/1.47  --inst_subs_given                       false
% 7.05/1.47  --inst_orphan_elimination               true
% 7.05/1.47  --inst_learning_loop_flag               true
% 7.05/1.47  --inst_learning_start                   3000
% 7.05/1.47  --inst_learning_factor                  2
% 7.05/1.47  --inst_start_prop_sim_after_learn       3
% 7.05/1.47  --inst_sel_renew                        solver
% 7.05/1.47  --inst_lit_activity_flag                true
% 7.05/1.47  --inst_restr_to_given                   false
% 7.05/1.47  --inst_activity_threshold               500
% 7.05/1.47  --inst_out_proof                        true
% 7.05/1.47  
% 7.05/1.47  ------ Resolution Options
% 7.05/1.47  
% 7.05/1.47  --resolution_flag                       true
% 7.05/1.47  --res_lit_sel                           adaptive
% 7.05/1.47  --res_lit_sel_side                      none
% 7.05/1.47  --res_ordering                          kbo
% 7.05/1.47  --res_to_prop_solver                    active
% 7.05/1.47  --res_prop_simpl_new                    false
% 7.05/1.47  --res_prop_simpl_given                  true
% 7.05/1.47  --res_passive_queue_type                priority_queues
% 7.05/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.47  --res_passive_queues_freq               [15;5]
% 7.05/1.47  --res_forward_subs                      full
% 7.05/1.47  --res_backward_subs                     full
% 7.05/1.47  --res_forward_subs_resolution           true
% 7.05/1.47  --res_backward_subs_resolution          true
% 7.05/1.47  --res_orphan_elimination                true
% 7.05/1.47  --res_time_limit                        2.
% 7.05/1.47  --res_out_proof                         true
% 7.05/1.47  
% 7.05/1.47  ------ Superposition Options
% 7.05/1.47  
% 7.05/1.47  --superposition_flag                    true
% 7.05/1.47  --sup_passive_queue_type                priority_queues
% 7.05/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.47  --demod_completeness_check              fast
% 7.05/1.47  --demod_use_ground                      true
% 7.05/1.47  --sup_to_prop_solver                    passive
% 7.05/1.47  --sup_prop_simpl_new                    true
% 7.05/1.47  --sup_prop_simpl_given                  true
% 7.05/1.47  --sup_fun_splitting                     true
% 7.05/1.47  --sup_smt_interval                      50000
% 7.05/1.47  
% 7.05/1.47  ------ Superposition Simplification Setup
% 7.05/1.47  
% 7.05/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.05/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.05/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.05/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.05/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.05/1.47  --sup_immed_triv                        [TrivRules]
% 7.05/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.47  --sup_immed_bw_main                     []
% 7.05/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.05/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.47  --sup_input_bw                          []
% 7.05/1.47  
% 7.05/1.47  ------ Combination Options
% 7.05/1.47  
% 7.05/1.47  --comb_res_mult                         3
% 7.05/1.47  --comb_sup_mult                         2
% 7.05/1.47  --comb_inst_mult                        10
% 7.05/1.47  
% 7.05/1.47  ------ Debug Options
% 7.05/1.47  
% 7.05/1.47  --dbg_backtrace                         false
% 7.05/1.47  --dbg_dump_prop_clauses                 false
% 7.05/1.47  --dbg_dump_prop_clauses_file            -
% 7.05/1.47  --dbg_out_stat                          false
% 7.05/1.47  ------ Parsing...
% 7.05/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.05/1.47  
% 7.05/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.05/1.47  
% 7.05/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.05/1.47  
% 7.05/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.05/1.47  ------ Proving...
% 7.05/1.47  ------ Problem Properties 
% 7.05/1.47  
% 7.05/1.47  
% 7.05/1.47  clauses                                 49
% 7.05/1.47  conjectures                             8
% 7.05/1.47  EPR                                     13
% 7.05/1.47  Horn                                    46
% 7.05/1.47  unary                                   25
% 7.05/1.47  binary                                  11
% 7.05/1.47  lits                                    114
% 7.05/1.47  lits eq                                 24
% 7.05/1.47  fd_pure                                 0
% 7.05/1.47  fd_pseudo                               0
% 7.05/1.47  fd_cond                                 1
% 7.05/1.47  fd_pseudo_cond                          5
% 7.05/1.47  AC symbols                              0
% 7.05/1.47  
% 7.05/1.47  ------ Schedule dynamic 5 is on 
% 7.05/1.47  
% 7.05/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.05/1.47  
% 7.05/1.47  
% 7.05/1.47  ------ 
% 7.05/1.47  Current options:
% 7.05/1.47  ------ 
% 7.05/1.47  
% 7.05/1.47  ------ Input Options
% 7.05/1.47  
% 7.05/1.47  --out_options                           all
% 7.05/1.47  --tptp_safe_out                         true
% 7.05/1.47  --problem_path                          ""
% 7.05/1.47  --include_path                          ""
% 7.05/1.47  --clausifier                            res/vclausify_rel
% 7.05/1.47  --clausifier_options                    ""
% 7.05/1.47  --stdin                                 false
% 7.05/1.47  --stats_out                             all
% 7.05/1.47  
% 7.05/1.47  ------ General Options
% 7.05/1.47  
% 7.05/1.47  --fof                                   false
% 7.05/1.47  --time_out_real                         305.
% 7.05/1.47  --time_out_virtual                      -1.
% 7.05/1.47  --symbol_type_check                     false
% 7.05/1.47  --clausify_out                          false
% 7.05/1.47  --sig_cnt_out                           false
% 7.05/1.47  --trig_cnt_out                          false
% 7.05/1.47  --trig_cnt_out_tolerance                1.
% 7.05/1.47  --trig_cnt_out_sk_spl                   false
% 7.05/1.47  --abstr_cl_out                          false
% 7.05/1.47  
% 7.05/1.47  ------ Global Options
% 7.05/1.47  
% 7.05/1.47  --schedule                              default
% 7.05/1.47  --add_important_lit                     false
% 7.05/1.47  --prop_solver_per_cl                    1000
% 7.05/1.47  --min_unsat_core                        false
% 7.05/1.47  --soft_assumptions                      false
% 7.05/1.47  --soft_lemma_size                       3
% 7.05/1.47  --prop_impl_unit_size                   0
% 7.05/1.47  --prop_impl_unit                        []
% 7.05/1.47  --share_sel_clauses                     true
% 7.05/1.47  --reset_solvers                         false
% 7.05/1.47  --bc_imp_inh                            [conj_cone]
% 7.05/1.47  --conj_cone_tolerance                   3.
% 7.05/1.47  --extra_neg_conj                        none
% 7.05/1.47  --large_theory_mode                     true
% 7.05/1.47  --prolific_symb_bound                   200
% 7.05/1.47  --lt_threshold                          2000
% 7.05/1.47  --clause_weak_htbl                      true
% 7.05/1.47  --gc_record_bc_elim                     false
% 7.05/1.47  
% 7.05/1.47  ------ Preprocessing Options
% 7.05/1.47  
% 7.05/1.47  --preprocessing_flag                    true
% 7.05/1.47  --time_out_prep_mult                    0.1
% 7.05/1.47  --splitting_mode                        input
% 7.05/1.47  --splitting_grd                         true
% 7.05/1.47  --splitting_cvd                         false
% 7.05/1.47  --splitting_cvd_svl                     false
% 7.05/1.47  --splitting_nvd                         32
% 7.05/1.47  --sub_typing                            true
% 7.05/1.47  --prep_gs_sim                           true
% 7.05/1.47  --prep_unflatten                        true
% 7.05/1.47  --prep_res_sim                          true
% 7.05/1.47  --prep_upred                            true
% 7.05/1.47  --prep_sem_filter                       exhaustive
% 7.05/1.47  --prep_sem_filter_out                   false
% 7.05/1.47  --pred_elim                             true
% 7.05/1.47  --res_sim_input                         true
% 7.05/1.47  --eq_ax_congr_red                       true
% 7.05/1.47  --pure_diseq_elim                       true
% 7.05/1.47  --brand_transform                       false
% 7.05/1.47  --non_eq_to_eq                          false
% 7.05/1.47  --prep_def_merge                        true
% 7.05/1.47  --prep_def_merge_prop_impl              false
% 7.05/1.47  --prep_def_merge_mbd                    true
% 7.05/1.47  --prep_def_merge_tr_red                 false
% 7.05/1.47  --prep_def_merge_tr_cl                  false
% 7.05/1.47  --smt_preprocessing                     true
% 7.05/1.47  --smt_ac_axioms                         fast
% 7.05/1.47  --preprocessed_out                      false
% 7.05/1.47  --preprocessed_stats                    false
% 7.05/1.47  
% 7.05/1.47  ------ Abstraction refinement Options
% 7.05/1.47  
% 7.05/1.47  --abstr_ref                             []
% 7.05/1.47  --abstr_ref_prep                        false
% 7.05/1.47  --abstr_ref_until_sat                   false
% 7.05/1.47  --abstr_ref_sig_restrict                funpre
% 7.05/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.47  --abstr_ref_under                       []
% 7.05/1.47  
% 7.05/1.47  ------ SAT Options
% 7.05/1.47  
% 7.05/1.47  --sat_mode                              false
% 7.05/1.47  --sat_fm_restart_options                ""
% 7.05/1.47  --sat_gr_def                            false
% 7.05/1.47  --sat_epr_types                         true
% 7.05/1.47  --sat_non_cyclic_types                  false
% 7.05/1.47  --sat_finite_models                     false
% 7.05/1.47  --sat_fm_lemmas                         false
% 7.05/1.47  --sat_fm_prep                           false
% 7.05/1.47  --sat_fm_uc_incr                        true
% 7.05/1.47  --sat_out_model                         small
% 7.05/1.47  --sat_out_clauses                       false
% 7.05/1.47  
% 7.05/1.47  ------ QBF Options
% 7.05/1.47  
% 7.05/1.47  --qbf_mode                              false
% 7.05/1.47  --qbf_elim_univ                         false
% 7.05/1.47  --qbf_dom_inst                          none
% 7.05/1.47  --qbf_dom_pre_inst                      false
% 7.05/1.47  --qbf_sk_in                             false
% 7.05/1.47  --qbf_pred_elim                         true
% 7.05/1.47  --qbf_split                             512
% 7.05/1.47  
% 7.05/1.47  ------ BMC1 Options
% 7.05/1.47  
% 7.05/1.47  --bmc1_incremental                      false
% 7.05/1.47  --bmc1_axioms                           reachable_all
% 7.05/1.47  --bmc1_min_bound                        0
% 7.05/1.47  --bmc1_max_bound                        -1
% 7.05/1.47  --bmc1_max_bound_default                -1
% 7.05/1.47  --bmc1_symbol_reachability              true
% 7.05/1.47  --bmc1_property_lemmas                  false
% 7.05/1.47  --bmc1_k_induction                      false
% 7.05/1.47  --bmc1_non_equiv_states                 false
% 7.05/1.47  --bmc1_deadlock                         false
% 7.05/1.47  --bmc1_ucm                              false
% 7.05/1.47  --bmc1_add_unsat_core                   none
% 7.05/1.47  --bmc1_unsat_core_children              false
% 7.05/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.47  --bmc1_out_stat                         full
% 7.05/1.47  --bmc1_ground_init                      false
% 7.05/1.47  --bmc1_pre_inst_next_state              false
% 7.05/1.47  --bmc1_pre_inst_state                   false
% 7.05/1.47  --bmc1_pre_inst_reach_state             false
% 7.05/1.47  --bmc1_out_unsat_core                   false
% 7.05/1.47  --bmc1_aig_witness_out                  false
% 7.05/1.47  --bmc1_verbose                          false
% 7.05/1.47  --bmc1_dump_clauses_tptp                false
% 7.05/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.47  --bmc1_dump_file                        -
% 7.05/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.47  --bmc1_ucm_extend_mode                  1
% 7.05/1.47  --bmc1_ucm_init_mode                    2
% 7.05/1.47  --bmc1_ucm_cone_mode                    none
% 7.05/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.47  --bmc1_ucm_relax_model                  4
% 7.05/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.47  --bmc1_ucm_layered_model                none
% 7.05/1.47  --bmc1_ucm_max_lemma_size               10
% 7.05/1.47  
% 7.05/1.47  ------ AIG Options
% 7.05/1.47  
% 7.05/1.47  --aig_mode                              false
% 7.05/1.47  
% 7.05/1.47  ------ Instantiation Options
% 7.05/1.47  
% 7.05/1.47  --instantiation_flag                    true
% 7.05/1.47  --inst_sos_flag                         true
% 7.05/1.47  --inst_sos_phase                        true
% 7.05/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.47  --inst_lit_sel_side                     none
% 7.05/1.47  --inst_solver_per_active                1400
% 7.05/1.47  --inst_solver_calls_frac                1.
% 7.05/1.47  --inst_passive_queue_type               priority_queues
% 7.05/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.47  --inst_passive_queues_freq              [25;2]
% 7.05/1.47  --inst_dismatching                      true
% 7.05/1.47  --inst_eager_unprocessed_to_passive     true
% 7.05/1.47  --inst_prop_sim_given                   true
% 7.05/1.47  --inst_prop_sim_new                     false
% 7.05/1.47  --inst_subs_new                         false
% 7.05/1.47  --inst_eq_res_simp                      false
% 7.05/1.47  --inst_subs_given                       false
% 7.05/1.47  --inst_orphan_elimination               true
% 7.05/1.47  --inst_learning_loop_flag               true
% 7.05/1.47  --inst_learning_start                   3000
% 7.05/1.47  --inst_learning_factor                  2
% 7.05/1.47  --inst_start_prop_sim_after_learn       3
% 7.05/1.47  --inst_sel_renew                        solver
% 7.05/1.47  --inst_lit_activity_flag                true
% 7.05/1.47  --inst_restr_to_given                   false
% 7.05/1.47  --inst_activity_threshold               500
% 7.05/1.47  --inst_out_proof                        true
% 7.05/1.47  
% 7.05/1.47  ------ Resolution Options
% 7.05/1.47  
% 7.05/1.47  --resolution_flag                       false
% 7.05/1.47  --res_lit_sel                           adaptive
% 7.05/1.47  --res_lit_sel_side                      none
% 7.05/1.47  --res_ordering                          kbo
% 7.05/1.47  --res_to_prop_solver                    active
% 7.05/1.47  --res_prop_simpl_new                    false
% 7.05/1.47  --res_prop_simpl_given                  true
% 7.05/1.47  --res_passive_queue_type                priority_queues
% 7.05/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.47  --res_passive_queues_freq               [15;5]
% 7.05/1.47  --res_forward_subs                      full
% 7.05/1.47  --res_backward_subs                     full
% 7.05/1.47  --res_forward_subs_resolution           true
% 7.05/1.47  --res_backward_subs_resolution          true
% 7.05/1.47  --res_orphan_elimination                true
% 7.05/1.47  --res_time_limit                        2.
% 7.05/1.47  --res_out_proof                         true
% 7.05/1.47  
% 7.05/1.47  ------ Superposition Options
% 7.05/1.47  
% 7.05/1.47  --superposition_flag                    true
% 7.05/1.47  --sup_passive_queue_type                priority_queues
% 7.05/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.47  --demod_completeness_check              fast
% 7.05/1.47  --demod_use_ground                      true
% 7.05/1.47  --sup_to_prop_solver                    passive
% 7.05/1.47  --sup_prop_simpl_new                    true
% 7.05/1.47  --sup_prop_simpl_given                  true
% 7.05/1.47  --sup_fun_splitting                     true
% 7.05/1.47  --sup_smt_interval                      50000
% 7.05/1.47  
% 7.05/1.47  ------ Superposition Simplification Setup
% 7.05/1.47  
% 7.05/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.05/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.05/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.05/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.05/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.05/1.47  --sup_immed_triv                        [TrivRules]
% 7.05/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.47  --sup_immed_bw_main                     []
% 7.05/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.05/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.47  --sup_input_bw                          []
% 7.05/1.47  
% 7.05/1.47  ------ Combination Options
% 7.05/1.47  
% 7.05/1.47  --comb_res_mult                         3
% 7.05/1.47  --comb_sup_mult                         2
% 7.05/1.47  --comb_inst_mult                        10
% 7.05/1.47  
% 7.05/1.47  ------ Debug Options
% 7.05/1.47  
% 7.05/1.47  --dbg_backtrace                         false
% 7.05/1.47  --dbg_dump_prop_clauses                 false
% 7.05/1.47  --dbg_dump_prop_clauses_file            -
% 7.05/1.47  --dbg_out_stat                          false
% 7.05/1.47  
% 7.05/1.47  
% 7.05/1.47  
% 7.05/1.47  
% 7.05/1.47  ------ Proving...
% 7.05/1.47  
% 7.05/1.47  
% 7.05/1.47  % SZS status Theorem for theBenchmark.p
% 7.05/1.47  
% 7.05/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.05/1.47  
% 7.05/1.47  fof(f11,axiom,(
% 7.05/1.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f92,plain,(
% 7.05/1.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 7.05/1.47    inference(cnf_transformation,[],[f11])).
% 7.05/1.47  
% 7.05/1.47  fof(f27,axiom,(
% 7.05/1.47    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f116,plain,(
% 7.05/1.47    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.05/1.47    inference(cnf_transformation,[],[f27])).
% 7.05/1.47  
% 7.05/1.47  fof(f133,plain,(
% 7.05/1.47    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 7.05/1.47    inference(definition_unfolding,[],[f92,f116])).
% 7.05/1.47  
% 7.05/1.47  fof(f14,axiom,(
% 7.05/1.47    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f96,plain,(
% 7.05/1.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.05/1.47    inference(cnf_transformation,[],[f14])).
% 7.05/1.47  
% 7.05/1.47  fof(f137,plain,(
% 7.05/1.47    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 7.05/1.47    inference(definition_unfolding,[],[f96,f116])).
% 7.05/1.47  
% 7.05/1.47  fof(f10,axiom,(
% 7.05/1.47    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f38,plain,(
% 7.05/1.47    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.05/1.47    inference(ennf_transformation,[],[f10])).
% 7.05/1.47  
% 7.05/1.47  fof(f91,plain,(
% 7.05/1.47    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.05/1.47    inference(cnf_transformation,[],[f38])).
% 7.05/1.47  
% 7.05/1.47  fof(f132,plain,(
% 7.05/1.47    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.05/1.47    inference(definition_unfolding,[],[f91,f116])).
% 7.05/1.47  
% 7.05/1.47  fof(f9,axiom,(
% 7.05/1.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f89,plain,(
% 7.05/1.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.05/1.47    inference(cnf_transformation,[],[f9])).
% 7.05/1.47  
% 7.05/1.47  fof(f131,plain,(
% 7.05/1.47    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.05/1.47    inference(definition_unfolding,[],[f89,f116])).
% 7.05/1.47  
% 7.05/1.47  fof(f15,axiom,(
% 7.05/1.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f41,plain,(
% 7.05/1.47    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.05/1.47    inference(ennf_transformation,[],[f15])).
% 7.05/1.47  
% 7.05/1.47  fof(f42,plain,(
% 7.05/1.47    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.05/1.47    inference(flattening,[],[f41])).
% 7.05/1.47  
% 7.05/1.47  fof(f98,plain,(
% 7.05/1.47    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.05/1.47    inference(cnf_transformation,[],[f42])).
% 7.05/1.47  
% 7.05/1.47  fof(f138,plain,(
% 7.05/1.47    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.05/1.47    inference(definition_unfolding,[],[f98,f116])).
% 7.05/1.47  
% 7.05/1.47  fof(f90,plain,(
% 7.05/1.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.05/1.47    inference(cnf_transformation,[],[f9])).
% 7.05/1.47  
% 7.05/1.47  fof(f130,plain,(
% 7.05/1.47    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 7.05/1.47    inference(definition_unfolding,[],[f90,f116])).
% 7.05/1.47  
% 7.05/1.47  fof(f97,plain,(
% 7.05/1.47    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.05/1.47    inference(cnf_transformation,[],[f14])).
% 7.05/1.47  
% 7.05/1.47  fof(f136,plain,(
% 7.05/1.47    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.05/1.47    inference(definition_unfolding,[],[f97,f116])).
% 7.05/1.47  
% 7.05/1.47  fof(f13,axiom,(
% 7.05/1.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f95,plain,(
% 7.05/1.47    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.05/1.47    inference(cnf_transformation,[],[f13])).
% 7.05/1.47  
% 7.05/1.47  fof(f134,plain,(
% 7.05/1.47    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 7.05/1.47    inference(definition_unfolding,[],[f95,f116])).
% 7.05/1.47  
% 7.05/1.47  fof(f30,conjecture,(
% 7.05/1.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f31,negated_conjecture,(
% 7.05/1.47    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 7.05/1.47    inference(negated_conjecture,[],[f30])).
% 7.05/1.47  
% 7.05/1.47  fof(f62,plain,(
% 7.05/1.47    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 7.05/1.47    inference(ennf_transformation,[],[f31])).
% 7.05/1.47  
% 7.05/1.47  fof(f63,plain,(
% 7.05/1.47    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 7.05/1.47    inference(flattening,[],[f62])).
% 7.05/1.47  
% 7.05/1.47  fof(f74,plain,(
% 7.05/1.47    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK3,X0,X0) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 7.05/1.47    introduced(choice_axiom,[])).
% 7.05/1.47  
% 7.05/1.47  fof(f73,plain,(
% 7.05/1.47    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(X2,sK1,sK1) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 7.05/1.47    introduced(choice_axiom,[])).
% 7.05/1.47  
% 7.05/1.47  fof(f75,plain,(
% 7.05/1.47    (~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 7.05/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f63,f74,f73])).
% 7.05/1.47  
% 7.05/1.47  fof(f128,plain,(
% 7.05/1.47    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))),
% 7.05/1.47    inference(cnf_transformation,[],[f75])).
% 7.05/1.47  
% 7.05/1.47  fof(f123,plain,(
% 7.05/1.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 7.05/1.47    inference(cnf_transformation,[],[f75])).
% 7.05/1.47  
% 7.05/1.47  fof(f20,axiom,(
% 7.05/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f47,plain,(
% 7.05/1.47    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.47    inference(ennf_transformation,[],[f20])).
% 7.05/1.47  
% 7.05/1.47  fof(f104,plain,(
% 7.05/1.47    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.47    inference(cnf_transformation,[],[f47])).
% 7.05/1.47  
% 7.05/1.47  fof(f18,axiom,(
% 7.05/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f45,plain,(
% 7.05/1.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.47    inference(ennf_transformation,[],[f18])).
% 7.05/1.47  
% 7.05/1.47  fof(f102,plain,(
% 7.05/1.47    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.47    inference(cnf_transformation,[],[f45])).
% 7.05/1.47  
% 7.05/1.47  fof(f23,axiom,(
% 7.05/1.47    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f52,plain,(
% 7.05/1.47    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.05/1.47    inference(ennf_transformation,[],[f23])).
% 7.05/1.47  
% 7.05/1.47  fof(f53,plain,(
% 7.05/1.47    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.05/1.47    inference(flattening,[],[f52])).
% 7.05/1.47  
% 7.05/1.47  fof(f72,plain,(
% 7.05/1.47    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.05/1.47    inference(nnf_transformation,[],[f53])).
% 7.05/1.47  
% 7.05/1.47  fof(f110,plain,(
% 7.05/1.47    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.05/1.47    inference(cnf_transformation,[],[f72])).
% 7.05/1.47  
% 7.05/1.47  fof(f17,axiom,(
% 7.05/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f44,plain,(
% 7.05/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.47    inference(ennf_transformation,[],[f17])).
% 7.05/1.47  
% 7.05/1.47  fof(f100,plain,(
% 7.05/1.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.47    inference(cnf_transformation,[],[f44])).
% 7.05/1.47  
% 7.05/1.47  fof(f22,axiom,(
% 7.05/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f50,plain,(
% 7.05/1.47    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.47    inference(ennf_transformation,[],[f22])).
% 7.05/1.47  
% 7.05/1.47  fof(f51,plain,(
% 7.05/1.47    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.47    inference(flattening,[],[f50])).
% 7.05/1.47  
% 7.05/1.47  fof(f109,plain,(
% 7.05/1.47    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.47    inference(cnf_transformation,[],[f51])).
% 7.05/1.47  
% 7.05/1.47  fof(f122,plain,(
% 7.05/1.47    v3_funct_2(sK2,sK1,sK1)),
% 7.05/1.47    inference(cnf_transformation,[],[f75])).
% 7.05/1.47  
% 7.05/1.47  fof(f120,plain,(
% 7.05/1.47    v1_funct_1(sK2)),
% 7.05/1.47    inference(cnf_transformation,[],[f75])).
% 7.05/1.47  
% 7.05/1.47  fof(f29,axiom,(
% 7.05/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f60,plain,(
% 7.05/1.47    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.05/1.47    inference(ennf_transformation,[],[f29])).
% 7.05/1.47  
% 7.05/1.47  fof(f61,plain,(
% 7.05/1.47    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.05/1.47    inference(flattening,[],[f60])).
% 7.05/1.47  
% 7.05/1.47  fof(f119,plain,(
% 7.05/1.47    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.05/1.47    inference(cnf_transformation,[],[f61])).
% 7.05/1.47  
% 7.05/1.47  fof(f28,axiom,(
% 7.05/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f58,plain,(
% 7.05/1.47    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.05/1.47    inference(ennf_transformation,[],[f28])).
% 7.05/1.47  
% 7.05/1.47  fof(f59,plain,(
% 7.05/1.47    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.05/1.47    inference(flattening,[],[f58])).
% 7.05/1.47  
% 7.05/1.47  fof(f117,plain,(
% 7.05/1.47    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.05/1.47    inference(cnf_transformation,[],[f59])).
% 7.05/1.47  
% 7.05/1.47  fof(f121,plain,(
% 7.05/1.47    v1_funct_2(sK2,sK1,sK1)),
% 7.05/1.47    inference(cnf_transformation,[],[f75])).
% 7.05/1.47  
% 7.05/1.47  fof(f124,plain,(
% 7.05/1.47    v1_funct_1(sK3)),
% 7.05/1.47    inference(cnf_transformation,[],[f75])).
% 7.05/1.47  
% 7.05/1.47  fof(f125,plain,(
% 7.05/1.47    v1_funct_2(sK3,sK1,sK1)),
% 7.05/1.47    inference(cnf_transformation,[],[f75])).
% 7.05/1.47  
% 7.05/1.47  fof(f127,plain,(
% 7.05/1.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 7.05/1.47    inference(cnf_transformation,[],[f75])).
% 7.05/1.47  
% 7.05/1.47  fof(f129,plain,(
% 7.05/1.47    ~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))),
% 7.05/1.47    inference(cnf_transformation,[],[f75])).
% 7.05/1.47  
% 7.05/1.47  fof(f26,axiom,(
% 7.05/1.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f56,plain,(
% 7.05/1.47    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.05/1.47    inference(ennf_transformation,[],[f26])).
% 7.05/1.47  
% 7.05/1.47  fof(f57,plain,(
% 7.05/1.47    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.05/1.47    inference(flattening,[],[f56])).
% 7.05/1.47  
% 7.05/1.47  fof(f115,plain,(
% 7.05/1.47    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.05/1.47    inference(cnf_transformation,[],[f57])).
% 7.05/1.47  
% 7.05/1.47  fof(f21,axiom,(
% 7.05/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f48,plain,(
% 7.05/1.47    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.05/1.47    inference(ennf_transformation,[],[f21])).
% 7.05/1.47  
% 7.05/1.47  fof(f49,plain,(
% 7.05/1.47    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.47    inference(flattening,[],[f48])).
% 7.05/1.47  
% 7.05/1.47  fof(f71,plain,(
% 7.05/1.47    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.47    inference(nnf_transformation,[],[f49])).
% 7.05/1.47  
% 7.05/1.47  fof(f106,plain,(
% 7.05/1.47    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.47    inference(cnf_transformation,[],[f71])).
% 7.05/1.47  
% 7.05/1.47  fof(f141,plain,(
% 7.05/1.47    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.47    inference(equality_resolution,[],[f106])).
% 7.05/1.47  
% 7.05/1.47  fof(f5,axiom,(
% 7.05/1.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f68,plain,(
% 7.05/1.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.05/1.47    inference(nnf_transformation,[],[f5])).
% 7.05/1.47  
% 7.05/1.47  fof(f69,plain,(
% 7.05/1.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.05/1.47    inference(flattening,[],[f68])).
% 7.05/1.47  
% 7.05/1.47  fof(f83,plain,(
% 7.05/1.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.05/1.47    inference(cnf_transformation,[],[f69])).
% 7.05/1.47  
% 7.05/1.47  fof(f140,plain,(
% 7.05/1.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.05/1.47    inference(equality_resolution,[],[f83])).
% 7.05/1.47  
% 7.05/1.47  fof(f84,plain,(
% 7.05/1.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.05/1.47    inference(cnf_transformation,[],[f69])).
% 7.05/1.47  
% 7.05/1.47  fof(f139,plain,(
% 7.05/1.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.05/1.47    inference(equality_resolution,[],[f84])).
% 7.05/1.47  
% 7.05/1.47  fof(f19,axiom,(
% 7.05/1.47    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f46,plain,(
% 7.05/1.47    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.05/1.47    inference(ennf_transformation,[],[f19])).
% 7.05/1.47  
% 7.05/1.47  fof(f103,plain,(
% 7.05/1.47    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.05/1.47    inference(cnf_transformation,[],[f46])).
% 7.05/1.47  
% 7.05/1.47  fof(f2,axiom,(
% 7.05/1.47    v1_xboole_0(k1_xboole_0)),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f79,plain,(
% 7.05/1.47    v1_xboole_0(k1_xboole_0)),
% 7.05/1.47    inference(cnf_transformation,[],[f2])).
% 7.05/1.47  
% 7.05/1.47  fof(f4,axiom,(
% 7.05/1.47    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.05/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.47  
% 7.05/1.47  fof(f34,plain,(
% 7.05/1.47    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.05/1.47    inference(ennf_transformation,[],[f4])).
% 7.05/1.47  
% 7.05/1.47  fof(f81,plain,(
% 7.05/1.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.05/1.47    inference(cnf_transformation,[],[f34])).
% 7.05/1.47  
% 7.05/1.47  cnf(c_16,plain,
% 7.05/1.47      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 7.05/1.47      inference(cnf_transformation,[],[f133]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_21,plain,
% 7.05/1.47      ( v1_relat_1(k6_partfun1(X0)) ),
% 7.05/1.47      inference(cnf_transformation,[],[f137]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3599,plain,
% 7.05/1.47      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_5177,plain,
% 7.05/1.47      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_16,c_3599]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_15,plain,
% 7.05/1.47      ( ~ v1_relat_1(X0)
% 7.05/1.47      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.05/1.47      inference(cnf_transformation,[],[f132]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3602,plain,
% 7.05/1.47      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.05/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_5703,plain,
% 7.05/1.47      ( k5_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_5177,c_3602]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_14,plain,
% 7.05/1.47      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.05/1.47      inference(cnf_transformation,[],[f131]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_4442,plain,
% 7.05/1.47      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_16,c_14]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_5704,plain,
% 7.05/1.47      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.05/1.47      inference(light_normalisation,[status(thm)],[c_5703,c_16,c_4442]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_22,plain,
% 7.05/1.47      ( ~ v2_funct_1(X0)
% 7.05/1.47      | ~ v1_funct_1(X1)
% 7.05/1.47      | ~ v1_funct_1(X0)
% 7.05/1.47      | ~ v1_relat_1(X1)
% 7.05/1.47      | ~ v1_relat_1(X0)
% 7.05/1.47      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 7.05/1.47      | k2_funct_1(X0) = X1
% 7.05/1.47      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 7.05/1.47      inference(cnf_transformation,[],[f138]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3597,plain,
% 7.05/1.47      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.05/1.47      | k2_funct_1(X1) = X0
% 7.05/1.47      | k1_relat_1(X1) != k2_relat_1(X0)
% 7.05/1.47      | v2_funct_1(X1) != iProver_top
% 7.05/1.47      | v1_funct_1(X1) != iProver_top
% 7.05/1.47      | v1_funct_1(X0) != iProver_top
% 7.05/1.47      | v1_relat_1(X1) != iProver_top
% 7.05/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12747,plain,
% 7.05/1.47      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 7.05/1.47      | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
% 7.05/1.47      | k6_partfun1(k2_relat_1(k1_xboole_0)) != k1_xboole_0
% 7.05/1.47      | v2_funct_1(k1_xboole_0) != iProver_top
% 7.05/1.47      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.05/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_5704,c_3597]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_13,plain,
% 7.05/1.47      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 7.05/1.47      inference(cnf_transformation,[],[f130]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_4235,plain,
% 7.05/1.47      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_16,c_13]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12751,plain,
% 7.05/1.47      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 7.05/1.47      | k1_xboole_0 != k1_xboole_0
% 7.05/1.47      | v2_funct_1(k1_xboole_0) != iProver_top
% 7.05/1.47      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.05/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.05/1.47      inference(light_normalisation,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_12747,c_16,c_4235,c_4442]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12752,plain,
% 7.05/1.47      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 7.05/1.47      | v2_funct_1(k1_xboole_0) != iProver_top
% 7.05/1.47      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.05/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.05/1.47      inference(equality_resolution_simp,[status(thm)],[c_12751]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_20,plain,
% 7.05/1.47      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.05/1.47      inference(cnf_transformation,[],[f136]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3598,plain,
% 7.05/1.47      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_5083,plain,
% 7.05/1.47      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_16,c_3598]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_18,plain,
% 7.05/1.47      ( v1_funct_1(k6_partfun1(X0)) ),
% 7.05/1.47      inference(cnf_transformation,[],[f134]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3600,plain,
% 7.05/1.47      ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_5545,plain,
% 7.05/1.47      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_16,c_3600]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_15158,plain,
% 7.05/1.47      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_12752,c_5083,c_5177,c_5545]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_44,negated_conjecture,
% 7.05/1.47      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 7.05/1.47      inference(cnf_transformation,[],[f128]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3584,plain,
% 7.05/1.47      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_49,negated_conjecture,
% 7.05/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 7.05/1.47      inference(cnf_transformation,[],[f123]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3580,plain,
% 7.05/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_28,plain,
% 7.05/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.47      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.05/1.47      inference(cnf_transformation,[],[f104]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3593,plain,
% 7.05/1.47      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.05/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8278,plain,
% 7.05/1.47      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_3580,c_3593]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_25,plain,
% 7.05/1.47      ( v5_relat_1(X0,X1)
% 7.05/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.05/1.47      inference(cnf_transformation,[],[f102]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_35,plain,
% 7.05/1.47      ( ~ v2_funct_2(X0,X1)
% 7.05/1.47      | ~ v5_relat_1(X0,X1)
% 7.05/1.47      | ~ v1_relat_1(X0)
% 7.05/1.47      | k2_relat_1(X0) = X1 ),
% 7.05/1.47      inference(cnf_transformation,[],[f110]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_640,plain,
% 7.05/1.47      ( ~ v2_funct_2(X0,X1)
% 7.05/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.05/1.47      | ~ v1_relat_1(X0)
% 7.05/1.47      | k2_relat_1(X0) = X1 ),
% 7.05/1.47      inference(resolution,[status(thm)],[c_25,c_35]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_24,plain,
% 7.05/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.47      | v1_relat_1(X0) ),
% 7.05/1.47      inference(cnf_transformation,[],[f100]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_652,plain,
% 7.05/1.47      ( ~ v2_funct_2(X0,X1)
% 7.05/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.05/1.47      | k2_relat_1(X0) = X1 ),
% 7.05/1.47      inference(forward_subsumption_resolution,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_640,c_24]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3575,plain,
% 7.05/1.47      ( k2_relat_1(X0) = X1
% 7.05/1.47      | v2_funct_2(X0,X1) != iProver_top
% 7.05/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_6312,plain,
% 7.05/1.47      ( k2_relat_1(sK2) = sK1 | v2_funct_2(sK2,sK1) != iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_3580,c_3575]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_31,plain,
% 7.05/1.47      ( ~ v3_funct_2(X0,X1,X2)
% 7.05/1.47      | v2_funct_2(X0,X2)
% 7.05/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.47      | ~ v1_funct_1(X0) ),
% 7.05/1.47      inference(cnf_transformation,[],[f109]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_50,negated_conjecture,
% 7.05/1.47      ( v3_funct_2(sK2,sK1,sK1) ),
% 7.05/1.47      inference(cnf_transformation,[],[f122]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_786,plain,
% 7.05/1.47      ( v2_funct_2(X0,X1)
% 7.05/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.05/1.47      | ~ v1_funct_1(X0)
% 7.05/1.47      | sK2 != X0
% 7.05/1.47      | sK1 != X1
% 7.05/1.47      | sK1 != X2 ),
% 7.05/1.47      inference(resolution_lifted,[status(thm)],[c_31,c_50]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_787,plain,
% 7.05/1.47      ( v2_funct_2(sK2,sK1)
% 7.05/1.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.05/1.47      | ~ v1_funct_1(sK2) ),
% 7.05/1.47      inference(unflattening,[status(thm)],[c_786]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_52,negated_conjecture,
% 7.05/1.47      ( v1_funct_1(sK2) ),
% 7.05/1.47      inference(cnf_transformation,[],[f120]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_789,plain,
% 7.05/1.47      ( v2_funct_2(sK2,sK1) ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_787,c_52,c_49]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_866,plain,
% 7.05/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.47      | k2_relat_1(X0) = X2
% 7.05/1.47      | sK2 != X0
% 7.05/1.47      | sK1 != X2 ),
% 7.05/1.47      inference(resolution_lifted,[status(thm)],[c_652,c_789]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_867,plain,
% 7.05/1.47      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.05/1.47      | k2_relat_1(sK2) = sK1 ),
% 7.05/1.47      inference(unflattening,[status(thm)],[c_866]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_869,plain,
% 7.05/1.47      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.05/1.47      | k2_relat_1(sK2) = sK1 ),
% 7.05/1.47      inference(instantiation,[status(thm)],[c_867]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_6533,plain,
% 7.05/1.47      ( k2_relat_1(sK2) = sK1 ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_6312,c_49,c_869]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8281,plain,
% 7.05/1.47      ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
% 7.05/1.47      inference(light_normalisation,[status(thm)],[c_8278,c_6533]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_42,plain,
% 7.05/1.47      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.05/1.47      | ~ v1_funct_2(X3,X1,X0)
% 7.05/1.47      | ~ v1_funct_2(X2,X0,X1)
% 7.05/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.05/1.47      | ~ v2_funct_1(X2)
% 7.05/1.47      | ~ v1_funct_1(X2)
% 7.05/1.47      | ~ v1_funct_1(X3)
% 7.05/1.47      | k2_relset_1(X0,X1,X2) != X1
% 7.05/1.47      | k2_funct_1(X2) = X3
% 7.05/1.47      | k1_xboole_0 = X1
% 7.05/1.47      | k1_xboole_0 = X0 ),
% 7.05/1.47      inference(cnf_transformation,[],[f119]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_41,plain,
% 7.05/1.47      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.05/1.47      | ~ v1_funct_2(X3,X1,X0)
% 7.05/1.47      | ~ v1_funct_2(X2,X0,X1)
% 7.05/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.05/1.47      | v2_funct_1(X2)
% 7.05/1.47      | ~ v1_funct_1(X2)
% 7.05/1.47      | ~ v1_funct_1(X3) ),
% 7.05/1.47      inference(cnf_transformation,[],[f117]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_272,plain,
% 7.05/1.47      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.05/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.47      | ~ v1_funct_2(X2,X0,X1)
% 7.05/1.47      | ~ v1_funct_2(X3,X1,X0)
% 7.05/1.47      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.05/1.47      | ~ v1_funct_1(X2)
% 7.05/1.47      | ~ v1_funct_1(X3)
% 7.05/1.47      | k2_relset_1(X0,X1,X2) != X1
% 7.05/1.47      | k2_funct_1(X2) = X3
% 7.05/1.47      | k1_xboole_0 = X1
% 7.05/1.47      | k1_xboole_0 = X0 ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_42,c_41]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_273,plain,
% 7.05/1.47      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.05/1.47      | ~ v1_funct_2(X3,X1,X0)
% 7.05/1.47      | ~ v1_funct_2(X2,X0,X1)
% 7.05/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.05/1.47      | ~ v1_funct_1(X3)
% 7.05/1.47      | ~ v1_funct_1(X2)
% 7.05/1.47      | k2_relset_1(X0,X1,X2) != X1
% 7.05/1.47      | k2_funct_1(X2) = X3
% 7.05/1.47      | k1_xboole_0 = X1
% 7.05/1.47      | k1_xboole_0 = X0 ),
% 7.05/1.47      inference(renaming,[status(thm)],[c_272]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3577,plain,
% 7.05/1.47      ( k2_relset_1(X0,X1,X2) != X1
% 7.05/1.47      | k2_funct_1(X2) = X3
% 7.05/1.47      | k1_xboole_0 = X1
% 7.05/1.47      | k1_xboole_0 = X0
% 7.05/1.47      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 7.05/1.47      | v1_funct_2(X3,X1,X0) != iProver_top
% 7.05/1.47      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.05/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.05/1.47      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 7.05/1.47      | v1_funct_1(X2) != iProver_top
% 7.05/1.47      | v1_funct_1(X3) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8623,plain,
% 7.05/1.47      ( k2_funct_1(sK2) = X0
% 7.05/1.47      | sK1 = k1_xboole_0
% 7.05/1.47      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 7.05/1.47      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 7.05/1.47      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 7.05/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.05/1.47      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.05/1.47      | v1_funct_1(X0) != iProver_top
% 7.05/1.47      | v1_funct_1(sK2) != iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_8281,c_3577]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_53,plain,
% 7.05/1.47      ( v1_funct_1(sK2) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_51,negated_conjecture,
% 7.05/1.47      ( v1_funct_2(sK2,sK1,sK1) ),
% 7.05/1.47      inference(cnf_transformation,[],[f121]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_54,plain,
% 7.05/1.47      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_56,plain,
% 7.05/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8949,plain,
% 7.05/1.47      ( v1_funct_1(X0) != iProver_top
% 7.05/1.47      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 7.05/1.47      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 7.05/1.47      | sK1 = k1_xboole_0
% 7.05/1.47      | k2_funct_1(sK2) = X0
% 7.05/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_8623,c_53,c_54,c_56]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8950,plain,
% 7.05/1.47      ( k2_funct_1(sK2) = X0
% 7.05/1.47      | sK1 = k1_xboole_0
% 7.05/1.47      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 7.05/1.47      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 7.05/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.05/1.47      | v1_funct_1(X0) != iProver_top ),
% 7.05/1.47      inference(renaming,[status(thm)],[c_8949]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8955,plain,
% 7.05/1.47      ( k2_funct_1(sK2) = sK3
% 7.05/1.47      | sK1 = k1_xboole_0
% 7.05/1.47      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 7.05/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.05/1.47      | v1_funct_1(sK3) != iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_3584,c_8950]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_48,negated_conjecture,
% 7.05/1.47      ( v1_funct_1(sK3) ),
% 7.05/1.47      inference(cnf_transformation,[],[f124]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_47,negated_conjecture,
% 7.05/1.47      ( v1_funct_2(sK3,sK1,sK1) ),
% 7.05/1.47      inference(cnf_transformation,[],[f125]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_45,negated_conjecture,
% 7.05/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 7.05/1.47      inference(cnf_transformation,[],[f127]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8956,plain,
% 7.05/1.47      ( ~ v1_funct_2(sK3,sK1,sK1)
% 7.05/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.05/1.47      | ~ v1_funct_1(sK3)
% 7.05/1.47      | k2_funct_1(sK2) = sK3
% 7.05/1.47      | sK1 = k1_xboole_0 ),
% 7.05/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_8955]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8958,plain,
% 7.05/1.47      ( sK1 = k1_xboole_0 | k2_funct_1(sK2) = sK3 ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_8955,c_57,c_58,c_60]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8959,plain,
% 7.05/1.47      ( k2_funct_1(sK2) = sK3 | sK1 = k1_xboole_0 ),
% 7.05/1.47      inference(renaming,[status(thm)],[c_8958]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_43,negated_conjecture,
% 7.05/1.47      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 7.05/1.47      inference(cnf_transformation,[],[f129]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3585,plain,
% 7.05/1.47      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_39,plain,
% 7.05/1.47      ( ~ v1_funct_2(X0,X1,X1)
% 7.05/1.47      | ~ v3_funct_2(X0,X1,X1)
% 7.05/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.05/1.47      | ~ v1_funct_1(X0)
% 7.05/1.47      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 7.05/1.47      inference(cnf_transformation,[],[f115]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_805,plain,
% 7.05/1.47      ( ~ v1_funct_2(X0,X1,X1)
% 7.05/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.05/1.47      | ~ v1_funct_1(X0)
% 7.05/1.47      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 7.05/1.47      | sK2 != X0
% 7.05/1.47      | sK1 != X1 ),
% 7.05/1.47      inference(resolution_lifted,[status(thm)],[c_39,c_50]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_806,plain,
% 7.05/1.47      ( ~ v1_funct_2(sK2,sK1,sK1)
% 7.05/1.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.05/1.47      | ~ v1_funct_1(sK2)
% 7.05/1.47      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 7.05/1.47      inference(unflattening,[status(thm)],[c_805]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_808,plain,
% 7.05/1.47      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_806,c_52,c_51,c_49]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3611,plain,
% 7.05/1.47      ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
% 7.05/1.47      inference(light_normalisation,[status(thm)],[c_3585,c_808]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_8960,plain,
% 7.05/1.47      ( sK1 = k1_xboole_0 | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_8959,c_3611]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_60,plain,
% 7.05/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_29,plain,
% 7.05/1.47      ( r2_relset_1(X0,X1,X2,X2)
% 7.05/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.05/1.47      inference(cnf_transformation,[],[f141]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3689,plain,
% 7.05/1.47      ( r2_relset_1(sK1,sK1,sK3,sK3)
% 7.05/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 7.05/1.47      inference(instantiation,[status(thm)],[c_29]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3690,plain,
% 7.05/1.47      ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
% 7.05/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_3689]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_9098,plain,
% 7.05/1.47      ( sK1 = k1_xboole_0 ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_8960,c_60,c_3690]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_9116,plain,
% 7.05/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.05/1.47      inference(demodulation,[status(thm)],[c_9098,c_3580]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_7,plain,
% 7.05/1.47      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.05/1.47      inference(cnf_transformation,[],[f140]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_9121,plain,
% 7.05/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.05/1.47      inference(demodulation,[status(thm)],[c_9116,c_7]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_6,plain,
% 7.05/1.47      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.05/1.47      inference(cnf_transformation,[],[f139]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_27,plain,
% 7.05/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.47      | ~ v1_xboole_0(X1)
% 7.05/1.47      | v1_xboole_0(X0) ),
% 7.05/1.47      inference(cnf_transformation,[],[f103]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3594,plain,
% 7.05/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.05/1.47      | v1_xboole_0(X1) != iProver_top
% 7.05/1.47      | v1_xboole_0(X0) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_11788,plain,
% 7.05/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.05/1.47      | v1_xboole_0(X1) != iProver_top
% 7.05/1.47      | v1_xboole_0(X0) = iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_6,c_3594]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_11868,plain,
% 7.05/1.47      ( v1_xboole_0(X0) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_9121,c_11788]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3,plain,
% 7.05/1.47      ( v1_xboole_0(k1_xboole_0) ),
% 7.05/1.47      inference(cnf_transformation,[],[f79]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_159,plain,
% 7.05/1.47      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_2592,plain,
% 7.05/1.47      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.05/1.47      theory(equality) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_4659,plain,
% 7.05/1.47      ( v1_xboole_0(X0)
% 7.05/1.47      | ~ v1_xboole_0(k1_xboole_0)
% 7.05/1.47      | X0 != k1_xboole_0 ),
% 7.05/1.47      inference(instantiation,[status(thm)],[c_2592]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_4660,plain,
% 7.05/1.47      ( X0 != k1_xboole_0
% 7.05/1.47      | v1_xboole_0(X0) = iProver_top
% 7.05/1.47      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_4659]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_4662,plain,
% 7.05/1.47      ( sK1 != k1_xboole_0
% 7.05/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.05/1.47      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.05/1.47      inference(instantiation,[status(thm)],[c_4660]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_11872,plain,
% 7.05/1.47      ( v1_xboole_0(sK2) = iProver_top
% 7.05/1.47      | v1_xboole_0(sK1) != iProver_top ),
% 7.05/1.47      inference(instantiation,[status(thm)],[c_11868]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12147,plain,
% 7.05/1.47      ( v1_xboole_0(sK2) = iProver_top ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_11868,c_60,c_159,c_3690,c_4662,c_8960,c_11872]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3607,plain,
% 7.05/1.47      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_5,plain,
% 7.05/1.47      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 7.05/1.47      inference(cnf_transformation,[],[f81]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3605,plain,
% 7.05/1.47      ( X0 = X1
% 7.05/1.47      | v1_xboole_0(X1) != iProver_top
% 7.05/1.47      | v1_xboole_0(X0) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_6838,plain,
% 7.05/1.47      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_3607,c_3605]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12152,plain,
% 7.05/1.47      ( sK2 = k1_xboole_0 ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_12147,c_6838]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_9111,plain,
% 7.05/1.47      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
% 7.05/1.47      inference(demodulation,[status(thm)],[c_9098,c_3611]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12198,plain,
% 7.05/1.47      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 7.05/1.47      inference(demodulation,[status(thm)],[c_12152,c_9111]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3583,plain,
% 7.05/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_9115,plain,
% 7.05/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.05/1.47      inference(demodulation,[status(thm)],[c_9098,c_3583]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_9122,plain,
% 7.05/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.05/1.47      inference(demodulation,[status(thm)],[c_9115,c_7]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_11869,plain,
% 7.05/1.47      ( v1_xboole_0(X0) != iProver_top | v1_xboole_0(sK3) = iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_9122,c_11788]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_11875,plain,
% 7.05/1.47      ( v1_xboole_0(sK3) = iProver_top
% 7.05/1.47      | v1_xboole_0(sK1) != iProver_top ),
% 7.05/1.47      inference(instantiation,[status(thm)],[c_11869]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12184,plain,
% 7.05/1.47      ( v1_xboole_0(sK3) = iProver_top ),
% 7.05/1.47      inference(global_propositional_subsumption,
% 7.05/1.47                [status(thm)],
% 7.05/1.47                [c_11869,c_60,c_159,c_3690,c_4662,c_8960,c_11875]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12189,plain,
% 7.05/1.47      ( sK3 = k1_xboole_0 ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_12184,c_6838]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12212,plain,
% 7.05/1.47      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 7.05/1.47      inference(light_normalisation,[status(thm)],[c_12198,c_12189]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_15160,plain,
% 7.05/1.47      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.05/1.47      inference(demodulation,[status(thm)],[c_15158,c_12212]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_3592,plain,
% 7.05/1.47      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 7.05/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_6955,plain,
% 7.05/1.47      ( r2_relset_1(sK1,sK1,sK2,sK2) = iProver_top ),
% 7.05/1.47      inference(superposition,[status(thm)],[c_3580,c_3592]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_9103,plain,
% 7.05/1.47      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
% 7.05/1.47      inference(demodulation,[status(thm)],[c_9098,c_6955]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(c_12200,plain,
% 7.05/1.47      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.05/1.47      inference(demodulation,[status(thm)],[c_12152,c_9103]) ).
% 7.05/1.47  
% 7.05/1.47  cnf(contradiction,plain,
% 7.05/1.47      ( $false ),
% 7.05/1.47      inference(minisat,[status(thm)],[c_15160,c_12200]) ).
% 7.05/1.47  
% 7.05/1.47  
% 7.05/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.05/1.47  
% 7.05/1.47  ------                               Statistics
% 7.05/1.47  
% 7.05/1.47  ------ General
% 7.05/1.47  
% 7.05/1.47  abstr_ref_over_cycles:                  0
% 7.05/1.47  abstr_ref_under_cycles:                 0
% 7.05/1.47  gc_basic_clause_elim:                   0
% 7.05/1.47  forced_gc_time:                         0
% 7.05/1.47  parsing_time:                           0.012
% 7.05/1.47  unif_index_cands_time:                  0.
% 7.05/1.47  unif_index_add_time:                    0.
% 7.05/1.47  orderings_time:                         0.
% 7.05/1.47  out_proof_time:                         0.015
% 7.05/1.47  total_time:                             0.541
% 7.05/1.47  num_of_symbols:                         60
% 7.05/1.47  num_of_terms:                           18190
% 7.05/1.47  
% 7.05/1.47  ------ Preprocessing
% 7.05/1.47  
% 7.05/1.47  num_of_splits:                          0
% 7.05/1.47  num_of_split_atoms:                     0
% 7.05/1.47  num_of_reused_defs:                     0
% 7.05/1.47  num_eq_ax_congr_red:                    32
% 7.05/1.47  num_of_sem_filtered_clauses:            1
% 7.05/1.47  num_of_subtypes:                        0
% 7.05/1.47  monotx_restored_types:                  0
% 7.05/1.47  sat_num_of_epr_types:                   0
% 7.05/1.47  sat_num_of_non_cyclic_types:            0
% 7.05/1.47  sat_guarded_non_collapsed_types:        0
% 7.05/1.47  num_pure_diseq_elim:                    0
% 7.05/1.47  simp_replaced_by:                       0
% 7.05/1.47  res_preprocessed:                       240
% 7.05/1.47  prep_upred:                             0
% 7.05/1.47  prep_unflattend:                        146
% 7.05/1.47  smt_new_axioms:                         0
% 7.05/1.47  pred_elim_cands:                        10
% 7.05/1.47  pred_elim:                              3
% 7.05/1.47  pred_elim_cl:                           1
% 7.05/1.47  pred_elim_cycles:                       12
% 7.05/1.47  merged_defs:                            8
% 7.05/1.47  merged_defs_ncl:                        0
% 7.05/1.47  bin_hyper_res:                          9
% 7.05/1.47  prep_cycles:                            4
% 7.05/1.47  pred_elim_time:                         0.036
% 7.05/1.47  splitting_time:                         0.
% 7.05/1.47  sem_filter_time:                        0.
% 7.05/1.47  monotx_time:                            0.001
% 7.05/1.47  subtype_inf_time:                       0.
% 7.05/1.47  
% 7.05/1.47  ------ Problem properties
% 7.05/1.47  
% 7.05/1.47  clauses:                                49
% 7.05/1.47  conjectures:                            8
% 7.05/1.47  epr:                                    13
% 7.05/1.47  horn:                                   46
% 7.05/1.47  ground:                                 16
% 7.05/1.47  unary:                                  25
% 7.05/1.47  binary:                                 11
% 7.05/1.47  lits:                                   114
% 7.05/1.47  lits_eq:                                24
% 7.05/1.47  fd_pure:                                0
% 7.05/1.47  fd_pseudo:                              0
% 7.05/1.47  fd_cond:                                1
% 7.05/1.47  fd_pseudo_cond:                         5
% 7.05/1.47  ac_symbols:                             0
% 7.05/1.47  
% 7.05/1.47  ------ Propositional Solver
% 7.05/1.47  
% 7.05/1.47  prop_solver_calls:                      28
% 7.05/1.47  prop_fast_solver_calls:                 2101
% 7.05/1.47  smt_solver_calls:                       0
% 7.05/1.47  smt_fast_solver_calls:                  0
% 7.05/1.47  prop_num_of_clauses:                    6033
% 7.05/1.47  prop_preprocess_simplified:             16485
% 7.05/1.47  prop_fo_subsumed:                       63
% 7.05/1.47  prop_solver_time:                       0.
% 7.05/1.47  smt_solver_time:                        0.
% 7.05/1.47  smt_fast_solver_time:                   0.
% 7.05/1.47  prop_fast_solver_time:                  0.
% 7.05/1.47  prop_unsat_core_time:                   0.
% 7.05/1.47  
% 7.05/1.47  ------ QBF
% 7.05/1.47  
% 7.05/1.47  qbf_q_res:                              0
% 7.05/1.47  qbf_num_tautologies:                    0
% 7.05/1.47  qbf_prep_cycles:                        0
% 7.05/1.47  
% 7.05/1.47  ------ BMC1
% 7.05/1.47  
% 7.05/1.47  bmc1_current_bound:                     -1
% 7.05/1.47  bmc1_last_solved_bound:                 -1
% 7.05/1.47  bmc1_unsat_core_size:                   -1
% 7.05/1.47  bmc1_unsat_core_parents_size:           -1
% 7.05/1.47  bmc1_merge_next_fun:                    0
% 7.05/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.05/1.47  
% 7.05/1.47  ------ Instantiation
% 7.05/1.47  
% 7.05/1.47  inst_num_of_clauses:                    1752
% 7.05/1.47  inst_num_in_passive:                    425
% 7.05/1.47  inst_num_in_active:                     854
% 7.05/1.47  inst_num_in_unprocessed:                473
% 7.05/1.47  inst_num_of_loops:                      1010
% 7.05/1.47  inst_num_of_learning_restarts:          0
% 7.05/1.47  inst_num_moves_active_passive:          152
% 7.05/1.47  inst_lit_activity:                      0
% 7.05/1.47  inst_lit_activity_moves:                0
% 7.05/1.47  inst_num_tautologies:                   0
% 7.05/1.47  inst_num_prop_implied:                  0
% 7.05/1.47  inst_num_existing_simplified:           0
% 7.05/1.47  inst_num_eq_res_simplified:             0
% 7.05/1.47  inst_num_child_elim:                    0
% 7.05/1.47  inst_num_of_dismatching_blockings:      719
% 7.05/1.47  inst_num_of_non_proper_insts:           2238
% 7.05/1.47  inst_num_of_duplicates:                 0
% 7.05/1.47  inst_inst_num_from_inst_to_res:         0
% 7.05/1.47  inst_dismatching_checking_time:         0.
% 7.05/1.47  
% 7.05/1.47  ------ Resolution
% 7.05/1.47  
% 7.05/1.47  res_num_of_clauses:                     0
% 7.05/1.47  res_num_in_passive:                     0
% 7.05/1.47  res_num_in_active:                      0
% 7.05/1.47  res_num_of_loops:                       244
% 7.05/1.47  res_forward_subset_subsumed:            106
% 7.05/1.47  res_backward_subset_subsumed:           0
% 7.05/1.47  res_forward_subsumed:                   0
% 7.05/1.47  res_backward_subsumed:                  1
% 7.05/1.47  res_forward_subsumption_resolution:     8
% 7.05/1.47  res_backward_subsumption_resolution:    0
% 7.05/1.47  res_clause_to_clause_subsumption:       911
% 7.05/1.47  res_orphan_elimination:                 0
% 7.05/1.47  res_tautology_del:                      95
% 7.05/1.47  res_num_eq_res_simplified:              0
% 7.05/1.47  res_num_sel_changes:                    0
% 7.05/1.47  res_moves_from_active_to_pass:          0
% 7.05/1.47  
% 7.05/1.47  ------ Superposition
% 7.05/1.47  
% 7.05/1.47  sup_time_total:                         0.
% 7.05/1.47  sup_time_generating:                    0.
% 7.05/1.47  sup_time_sim_full:                      0.
% 7.05/1.47  sup_time_sim_immed:                     0.
% 7.05/1.47  
% 7.05/1.47  sup_num_of_clauses:                     191
% 7.05/1.47  sup_num_in_active:                      130
% 7.05/1.47  sup_num_in_passive:                     61
% 7.05/1.47  sup_num_of_loops:                       201
% 7.05/1.47  sup_fw_superposition:                   270
% 7.05/1.47  sup_bw_superposition:                   111
% 7.05/1.47  sup_immediate_simplified:               125
% 7.05/1.47  sup_given_eliminated:                   2
% 7.05/1.47  comparisons_done:                       0
% 7.05/1.47  comparisons_avoided:                    3
% 7.05/1.47  
% 7.05/1.47  ------ Simplifications
% 7.05/1.47  
% 7.05/1.47  
% 7.05/1.47  sim_fw_subset_subsumed:                 24
% 7.05/1.47  sim_bw_subset_subsumed:                 5
% 7.05/1.47  sim_fw_subsumed:                        13
% 7.05/1.47  sim_bw_subsumed:                        12
% 7.05/1.47  sim_fw_subsumption_res:                 0
% 7.05/1.47  sim_bw_subsumption_res:                 0
% 7.05/1.47  sim_tautology_del:                      8
% 7.05/1.47  sim_eq_tautology_del:                   32
% 7.05/1.47  sim_eq_res_simp:                        3
% 7.05/1.47  sim_fw_demodulated:                     24
% 7.05/1.47  sim_bw_demodulated:                     58
% 7.05/1.47  sim_light_normalised:                   69
% 7.05/1.47  sim_joinable_taut:                      0
% 7.05/1.47  sim_joinable_simp:                      0
% 7.05/1.47  sim_ac_normalised:                      0
% 7.05/1.47  sim_smt_subsumption:                    0
% 7.05/1.47  
%------------------------------------------------------------------------------
