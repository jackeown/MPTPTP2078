%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:11 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_40)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

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

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f87,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f52,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f88,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f59,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f93,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f59,f73])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f85,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

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
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2288,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2300,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4105,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2288,c_2300])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2305,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4279,plain,
    ( k5_relat_1(sK1,k6_partfun1(k2_relat_1(sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_4105,c_2305])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_366,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_12,c_20])).

cnf(c_378,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_366,c_11])).

cnf(c_2284,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_4378,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2288,c_2284])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_512,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_513,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_515,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_35,c_32])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_378,c_515])).

cnf(c_593,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_595,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_5306,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4378,c_32,c_595])).

cnf(c_5392,plain,
    ( k5_relat_1(sK1,k6_partfun1(sK0)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4279,c_5306])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2301,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6345,plain,
    ( k2_funct_1(k6_partfun1(sK0)) = sK1
    | k6_partfun1(k2_relat_1(k6_partfun1(sK0))) != sK1
    | k1_relat_1(k6_partfun1(sK0)) != k2_relat_1(sK1)
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5392,c_2301])).

cnf(c_6354,plain,
    ( k2_funct_1(k6_partfun1(sK0)) = sK1
    | k6_partfun1(k2_relat_1(k6_partfun1(sK0))) != sK1
    | k1_relat_1(k6_partfun1(sK0)) != sK0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6345,c_5306])).

cnf(c_2,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_6355,plain,
    ( k2_funct_1(k6_partfun1(sK0)) = sK1
    | k6_partfun1(sK0) != sK1
    | sK0 != sK0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6354,c_2,c_3])).

cnf(c_6356,plain,
    ( k2_funct_1(k6_partfun1(sK0)) = sK1
    | k6_partfun1(sK0) != sK1
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6355])).

cnf(c_9,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_93,plain,
    ( v1_relat_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_96,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_100,plain,
    ( v1_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2547,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6406,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK1)
    | k2_funct_1(k6_partfun1(sK0)) = sK1
    | k6_partfun1(sK0) != sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6356])).

cnf(c_8282,plain,
    ( k6_partfun1(sK0) != sK1
    | k2_funct_1(k6_partfun1(sK0)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6356,c_35,c_32,c_93,c_96,c_100,c_2547,c_6406])).

cnf(c_8283,plain,
    ( k2_funct_1(k6_partfun1(sK0)) = sK1
    | k6_partfun1(sK0) != sK1 ),
    inference(renaming,[status(thm)],[c_8282])).

cnf(c_5,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2292,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2299,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5510,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2288,c_2299])).

cnf(c_5516,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_5510,c_5306])).

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
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_190,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_24])).

cnf(c_191,plain,
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
    inference(renaming,[status(thm)],[c_190])).

cnf(c_2285,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_6202,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5516,c_2285])).

cnf(c_36,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_37,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6759,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6202,c_36,c_37,c_39])).

cnf(c_6760,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6759])).

cnf(c_6771,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_6760])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6772,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6771])).

cnf(c_6855,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6771,c_40,c_41,c_43])).

cnf(c_6856,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6855])).

cnf(c_26,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2293,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_531,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_532,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_534,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_35,c_34,c_32])).

cnf(c_2346,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2293,c_534])).

cnf(c_6859,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6856,c_2346])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2590,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2591,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2590])).

cnf(c_6862,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6859,c_43,c_2591])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2307,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5309,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5306,c_2307])).

cnf(c_2548,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2547])).

cnf(c_5408,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5309,c_39,c_2548])).

cnf(c_5409,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5408])).

cnf(c_6874,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6862,c_5409])).

cnf(c_6949,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6874])).

cnf(c_8284,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8283,c_5,c_6862,c_6949])).

cnf(c_8285,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8284])).

cnf(c_2291,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4377,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2291,c_2284])).

cnf(c_29,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_490,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_491,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_493,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_31,c_28])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_378,c_493])).

cnf(c_583,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_585,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_5217,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4377,c_28,c_585])).

cnf(c_5220,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5217,c_2307])).

cnf(c_2544,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5231,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5220])).

cnf(c_5395,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5220,c_28,c_2544,c_5231])).

cnf(c_5396,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5395])).

cnf(c_6875,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6862,c_5396])).

cnf(c_6927,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6875])).

cnf(c_6882,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6862,c_2346])).

cnf(c_6932,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6927,c_6882])).

cnf(c_6951,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6949,c_6932])).

cnf(c_8287,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8285,c_6951])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2296,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3993,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2296])).

cnf(c_2298,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4831,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3993,c_2298])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8287,c_4831])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.64/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.03  
% 1.64/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.64/1.03  
% 1.64/1.03  ------  iProver source info
% 1.64/1.03  
% 1.64/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.64/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.64/1.03  git: non_committed_changes: false
% 1.64/1.03  git: last_make_outside_of_git: false
% 1.64/1.03  
% 1.64/1.03  ------ 
% 1.64/1.03  
% 1.64/1.03  ------ Input Options
% 1.64/1.03  
% 1.64/1.03  --out_options                           all
% 1.64/1.03  --tptp_safe_out                         true
% 1.64/1.03  --problem_path                          ""
% 1.64/1.03  --include_path                          ""
% 1.64/1.03  --clausifier                            res/vclausify_rel
% 1.64/1.03  --clausifier_options                    --mode clausify
% 1.64/1.03  --stdin                                 false
% 1.64/1.03  --stats_out                             all
% 1.64/1.03  
% 1.64/1.03  ------ General Options
% 1.64/1.03  
% 1.64/1.03  --fof                                   false
% 1.64/1.03  --time_out_real                         305.
% 1.64/1.03  --time_out_virtual                      -1.
% 1.64/1.03  --symbol_type_check                     false
% 1.64/1.03  --clausify_out                          false
% 1.64/1.03  --sig_cnt_out                           false
% 1.64/1.03  --trig_cnt_out                          false
% 1.64/1.03  --trig_cnt_out_tolerance                1.
% 1.64/1.03  --trig_cnt_out_sk_spl                   false
% 1.64/1.03  --abstr_cl_out                          false
% 1.64/1.03  
% 1.64/1.03  ------ Global Options
% 1.64/1.03  
% 1.64/1.03  --schedule                              default
% 1.64/1.03  --add_important_lit                     false
% 1.64/1.03  --prop_solver_per_cl                    1000
% 1.64/1.03  --min_unsat_core                        false
% 1.64/1.03  --soft_assumptions                      false
% 1.64/1.03  --soft_lemma_size                       3
% 1.64/1.03  --prop_impl_unit_size                   0
% 1.64/1.03  --prop_impl_unit                        []
% 1.64/1.03  --share_sel_clauses                     true
% 1.64/1.03  --reset_solvers                         false
% 1.64/1.03  --bc_imp_inh                            [conj_cone]
% 1.64/1.03  --conj_cone_tolerance                   3.
% 1.64/1.03  --extra_neg_conj                        none
% 1.64/1.03  --large_theory_mode                     true
% 1.64/1.03  --prolific_symb_bound                   200
% 1.64/1.03  --lt_threshold                          2000
% 1.64/1.03  --clause_weak_htbl                      true
% 1.64/1.03  --gc_record_bc_elim                     false
% 1.64/1.03  
% 1.64/1.03  ------ Preprocessing Options
% 1.64/1.03  
% 1.64/1.03  --preprocessing_flag                    true
% 1.64/1.03  --time_out_prep_mult                    0.1
% 1.64/1.03  --splitting_mode                        input
% 1.64/1.03  --splitting_grd                         true
% 1.64/1.03  --splitting_cvd                         false
% 1.64/1.03  --splitting_cvd_svl                     false
% 1.64/1.03  --splitting_nvd                         32
% 1.64/1.03  --sub_typing                            true
% 1.64/1.03  --prep_gs_sim                           true
% 1.64/1.03  --prep_unflatten                        true
% 1.64/1.03  --prep_res_sim                          true
% 1.64/1.03  --prep_upred                            true
% 1.64/1.03  --prep_sem_filter                       exhaustive
% 1.64/1.03  --prep_sem_filter_out                   false
% 1.64/1.03  --pred_elim                             true
% 1.64/1.03  --res_sim_input                         true
% 1.64/1.03  --eq_ax_congr_red                       true
% 1.64/1.03  --pure_diseq_elim                       true
% 1.64/1.03  --brand_transform                       false
% 1.64/1.03  --non_eq_to_eq                          false
% 1.64/1.03  --prep_def_merge                        true
% 1.64/1.03  --prep_def_merge_prop_impl              false
% 1.64/1.03  --prep_def_merge_mbd                    true
% 1.64/1.03  --prep_def_merge_tr_red                 false
% 1.64/1.03  --prep_def_merge_tr_cl                  false
% 1.64/1.03  --smt_preprocessing                     true
% 1.64/1.03  --smt_ac_axioms                         fast
% 1.64/1.03  --preprocessed_out                      false
% 1.64/1.03  --preprocessed_stats                    false
% 1.64/1.03  
% 1.64/1.03  ------ Abstraction refinement Options
% 1.64/1.03  
% 1.64/1.03  --abstr_ref                             []
% 1.64/1.03  --abstr_ref_prep                        false
% 1.64/1.03  --abstr_ref_until_sat                   false
% 1.64/1.03  --abstr_ref_sig_restrict                funpre
% 1.64/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.64/1.03  --abstr_ref_under                       []
% 1.64/1.03  
% 1.64/1.03  ------ SAT Options
% 1.64/1.03  
% 1.64/1.03  --sat_mode                              false
% 1.64/1.03  --sat_fm_restart_options                ""
% 1.64/1.03  --sat_gr_def                            false
% 1.64/1.03  --sat_epr_types                         true
% 1.64/1.03  --sat_non_cyclic_types                  false
% 1.64/1.03  --sat_finite_models                     false
% 1.64/1.03  --sat_fm_lemmas                         false
% 1.64/1.03  --sat_fm_prep                           false
% 1.64/1.03  --sat_fm_uc_incr                        true
% 1.64/1.03  --sat_out_model                         small
% 1.64/1.03  --sat_out_clauses                       false
% 1.64/1.03  
% 1.64/1.03  ------ QBF Options
% 1.64/1.03  
% 1.64/1.03  --qbf_mode                              false
% 1.64/1.03  --qbf_elim_univ                         false
% 1.64/1.03  --qbf_dom_inst                          none
% 1.64/1.03  --qbf_dom_pre_inst                      false
% 1.64/1.03  --qbf_sk_in                             false
% 1.64/1.03  --qbf_pred_elim                         true
% 1.64/1.03  --qbf_split                             512
% 1.64/1.03  
% 1.64/1.03  ------ BMC1 Options
% 1.64/1.03  
% 1.64/1.03  --bmc1_incremental                      false
% 1.64/1.03  --bmc1_axioms                           reachable_all
% 1.64/1.03  --bmc1_min_bound                        0
% 1.64/1.03  --bmc1_max_bound                        -1
% 1.64/1.03  --bmc1_max_bound_default                -1
% 1.64/1.03  --bmc1_symbol_reachability              true
% 1.64/1.03  --bmc1_property_lemmas                  false
% 1.64/1.03  --bmc1_k_induction                      false
% 1.64/1.03  --bmc1_non_equiv_states                 false
% 1.64/1.03  --bmc1_deadlock                         false
% 1.64/1.03  --bmc1_ucm                              false
% 1.64/1.03  --bmc1_add_unsat_core                   none
% 1.64/1.03  --bmc1_unsat_core_children              false
% 1.64/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.64/1.03  --bmc1_out_stat                         full
% 1.64/1.03  --bmc1_ground_init                      false
% 1.64/1.03  --bmc1_pre_inst_next_state              false
% 1.64/1.03  --bmc1_pre_inst_state                   false
% 1.64/1.03  --bmc1_pre_inst_reach_state             false
% 1.64/1.03  --bmc1_out_unsat_core                   false
% 1.64/1.03  --bmc1_aig_witness_out                  false
% 1.64/1.03  --bmc1_verbose                          false
% 1.64/1.03  --bmc1_dump_clauses_tptp                false
% 1.64/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.64/1.03  --bmc1_dump_file                        -
% 1.64/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.64/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.64/1.03  --bmc1_ucm_extend_mode                  1
% 1.64/1.03  --bmc1_ucm_init_mode                    2
% 1.64/1.03  --bmc1_ucm_cone_mode                    none
% 1.64/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.64/1.03  --bmc1_ucm_relax_model                  4
% 1.64/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.64/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.64/1.03  --bmc1_ucm_layered_model                none
% 1.64/1.03  --bmc1_ucm_max_lemma_size               10
% 1.64/1.03  
% 1.64/1.03  ------ AIG Options
% 1.64/1.03  
% 1.64/1.03  --aig_mode                              false
% 1.64/1.03  
% 1.64/1.03  ------ Instantiation Options
% 1.64/1.03  
% 1.64/1.03  --instantiation_flag                    true
% 1.64/1.03  --inst_sos_flag                         false
% 1.64/1.03  --inst_sos_phase                        true
% 1.64/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.64/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.64/1.03  --inst_lit_sel_side                     num_symb
% 1.64/1.03  --inst_solver_per_active                1400
% 1.64/1.03  --inst_solver_calls_frac                1.
% 1.64/1.03  --inst_passive_queue_type               priority_queues
% 1.64/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.64/1.03  --inst_passive_queues_freq              [25;2]
% 1.64/1.03  --inst_dismatching                      true
% 1.64/1.03  --inst_eager_unprocessed_to_passive     true
% 1.64/1.03  --inst_prop_sim_given                   true
% 1.64/1.03  --inst_prop_sim_new                     false
% 1.64/1.03  --inst_subs_new                         false
% 1.64/1.03  --inst_eq_res_simp                      false
% 1.64/1.03  --inst_subs_given                       false
% 1.64/1.03  --inst_orphan_elimination               true
% 1.64/1.03  --inst_learning_loop_flag               true
% 1.64/1.03  --inst_learning_start                   3000
% 1.64/1.03  --inst_learning_factor                  2
% 1.64/1.03  --inst_start_prop_sim_after_learn       3
% 1.64/1.03  --inst_sel_renew                        solver
% 1.64/1.03  --inst_lit_activity_flag                true
% 1.64/1.03  --inst_restr_to_given                   false
% 1.64/1.03  --inst_activity_threshold               500
% 1.64/1.03  --inst_out_proof                        true
% 1.64/1.03  
% 1.64/1.03  ------ Resolution Options
% 1.64/1.03  
% 1.64/1.03  --resolution_flag                       true
% 1.64/1.03  --res_lit_sel                           adaptive
% 1.64/1.03  --res_lit_sel_side                      none
% 1.64/1.03  --res_ordering                          kbo
% 1.64/1.03  --res_to_prop_solver                    active
% 1.64/1.03  --res_prop_simpl_new                    false
% 1.64/1.03  --res_prop_simpl_given                  true
% 1.64/1.03  --res_passive_queue_type                priority_queues
% 1.64/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.64/1.03  --res_passive_queues_freq               [15;5]
% 1.64/1.03  --res_forward_subs                      full
% 1.64/1.03  --res_backward_subs                     full
% 1.64/1.03  --res_forward_subs_resolution           true
% 1.64/1.03  --res_backward_subs_resolution          true
% 1.64/1.03  --res_orphan_elimination                true
% 1.64/1.03  --res_time_limit                        2.
% 1.64/1.03  --res_out_proof                         true
% 1.64/1.03  
% 1.64/1.03  ------ Superposition Options
% 1.64/1.03  
% 1.64/1.03  --superposition_flag                    true
% 1.64/1.03  --sup_passive_queue_type                priority_queues
% 1.64/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.64/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.64/1.03  --demod_completeness_check              fast
% 1.64/1.03  --demod_use_ground                      true
% 1.64/1.03  --sup_to_prop_solver                    passive
% 1.64/1.03  --sup_prop_simpl_new                    true
% 1.64/1.03  --sup_prop_simpl_given                  true
% 1.64/1.03  --sup_fun_splitting                     false
% 1.64/1.03  --sup_smt_interval                      50000
% 1.64/1.03  
% 1.64/1.03  ------ Superposition Simplification Setup
% 1.64/1.03  
% 1.64/1.03  --sup_indices_passive                   []
% 1.64/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.64/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.03  --sup_full_bw                           [BwDemod]
% 1.64/1.03  --sup_immed_triv                        [TrivRules]
% 1.64/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.64/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.03  --sup_immed_bw_main                     []
% 1.64/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.64/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/1.03  
% 1.64/1.03  ------ Combination Options
% 1.64/1.03  
% 1.64/1.03  --comb_res_mult                         3
% 1.64/1.03  --comb_sup_mult                         2
% 1.64/1.03  --comb_inst_mult                        10
% 1.64/1.03  
% 1.64/1.03  ------ Debug Options
% 1.64/1.03  
% 1.64/1.03  --dbg_backtrace                         false
% 1.64/1.03  --dbg_dump_prop_clauses                 false
% 1.64/1.03  --dbg_dump_prop_clauses_file            -
% 1.64/1.03  --dbg_out_stat                          false
% 1.64/1.03  ------ Parsing...
% 1.64/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.64/1.03  
% 1.64/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.64/1.03  
% 1.64/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.64/1.03  
% 1.64/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.64/1.03  ------ Proving...
% 1.64/1.03  ------ Problem Properties 
% 1.64/1.03  
% 1.64/1.03  
% 1.64/1.03  clauses                                 34
% 1.64/1.03  conjectures                             8
% 1.64/1.03  EPR                                     8
% 1.64/1.03  Horn                                    33
% 1.64/1.03  unary                                   21
% 1.64/1.03  binary                                  5
% 1.64/1.03  lits                                    79
% 1.64/1.03  lits eq                                 20
% 1.64/1.03  fd_pure                                 0
% 1.64/1.03  fd_pseudo                               0
% 1.64/1.03  fd_cond                                 2
% 1.64/1.03  fd_pseudo_cond                          4
% 1.64/1.03  AC symbols                              0
% 1.64/1.03  
% 1.64/1.03  ------ Schedule dynamic 5 is on 
% 1.64/1.03  
% 1.64/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.64/1.03  
% 1.64/1.03  
% 1.64/1.03  ------ 
% 1.64/1.03  Current options:
% 1.64/1.03  ------ 
% 1.64/1.03  
% 1.64/1.03  ------ Input Options
% 1.64/1.03  
% 1.64/1.03  --out_options                           all
% 1.64/1.03  --tptp_safe_out                         true
% 1.64/1.03  --problem_path                          ""
% 1.64/1.03  --include_path                          ""
% 1.64/1.03  --clausifier                            res/vclausify_rel
% 1.64/1.03  --clausifier_options                    --mode clausify
% 1.64/1.03  --stdin                                 false
% 1.64/1.03  --stats_out                             all
% 1.64/1.03  
% 1.64/1.03  ------ General Options
% 1.64/1.03  
% 1.64/1.03  --fof                                   false
% 1.64/1.03  --time_out_real                         305.
% 1.64/1.03  --time_out_virtual                      -1.
% 1.64/1.03  --symbol_type_check                     false
% 1.64/1.03  --clausify_out                          false
% 1.64/1.03  --sig_cnt_out                           false
% 1.64/1.03  --trig_cnt_out                          false
% 1.64/1.03  --trig_cnt_out_tolerance                1.
% 1.64/1.03  --trig_cnt_out_sk_spl                   false
% 1.64/1.03  --abstr_cl_out                          false
% 1.64/1.03  
% 1.64/1.03  ------ Global Options
% 1.64/1.03  
% 1.64/1.03  --schedule                              default
% 1.64/1.03  --add_important_lit                     false
% 1.64/1.03  --prop_solver_per_cl                    1000
% 1.64/1.03  --min_unsat_core                        false
% 1.64/1.03  --soft_assumptions                      false
% 1.64/1.03  --soft_lemma_size                       3
% 1.64/1.03  --prop_impl_unit_size                   0
% 1.64/1.03  --prop_impl_unit                        []
% 1.64/1.03  --share_sel_clauses                     true
% 1.64/1.03  --reset_solvers                         false
% 1.64/1.03  --bc_imp_inh                            [conj_cone]
% 1.64/1.03  --conj_cone_tolerance                   3.
% 1.64/1.03  --extra_neg_conj                        none
% 1.64/1.03  --large_theory_mode                     true
% 1.64/1.03  --prolific_symb_bound                   200
% 1.64/1.03  --lt_threshold                          2000
% 1.64/1.03  --clause_weak_htbl                      true
% 1.64/1.03  --gc_record_bc_elim                     false
% 1.64/1.03  
% 1.64/1.03  ------ Preprocessing Options
% 1.64/1.03  
% 1.64/1.03  --preprocessing_flag                    true
% 1.64/1.03  --time_out_prep_mult                    0.1
% 1.64/1.03  --splitting_mode                        input
% 1.64/1.03  --splitting_grd                         true
% 1.64/1.03  --splitting_cvd                         false
% 1.64/1.03  --splitting_cvd_svl                     false
% 1.64/1.03  --splitting_nvd                         32
% 1.64/1.03  --sub_typing                            true
% 1.64/1.03  --prep_gs_sim                           true
% 1.64/1.03  --prep_unflatten                        true
% 1.64/1.03  --prep_res_sim                          true
% 1.64/1.03  --prep_upred                            true
% 1.64/1.03  --prep_sem_filter                       exhaustive
% 1.64/1.03  --prep_sem_filter_out                   false
% 1.64/1.03  --pred_elim                             true
% 1.64/1.03  --res_sim_input                         true
% 1.64/1.03  --eq_ax_congr_red                       true
% 1.64/1.03  --pure_diseq_elim                       true
% 1.64/1.03  --brand_transform                       false
% 1.64/1.03  --non_eq_to_eq                          false
% 1.64/1.03  --prep_def_merge                        true
% 1.64/1.03  --prep_def_merge_prop_impl              false
% 1.64/1.03  --prep_def_merge_mbd                    true
% 1.64/1.03  --prep_def_merge_tr_red                 false
% 1.64/1.03  --prep_def_merge_tr_cl                  false
% 1.64/1.03  --smt_preprocessing                     true
% 1.64/1.03  --smt_ac_axioms                         fast
% 1.64/1.03  --preprocessed_out                      false
% 1.64/1.03  --preprocessed_stats                    false
% 1.64/1.03  
% 1.64/1.03  ------ Abstraction refinement Options
% 1.64/1.03  
% 1.64/1.03  --abstr_ref                             []
% 1.64/1.03  --abstr_ref_prep                        false
% 1.64/1.03  --abstr_ref_until_sat                   false
% 1.64/1.03  --abstr_ref_sig_restrict                funpre
% 1.64/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.64/1.03  --abstr_ref_under                       []
% 1.64/1.03  
% 1.64/1.03  ------ SAT Options
% 1.64/1.03  
% 1.64/1.03  --sat_mode                              false
% 1.64/1.03  --sat_fm_restart_options                ""
% 1.64/1.03  --sat_gr_def                            false
% 1.64/1.03  --sat_epr_types                         true
% 1.64/1.03  --sat_non_cyclic_types                  false
% 1.64/1.03  --sat_finite_models                     false
% 1.64/1.03  --sat_fm_lemmas                         false
% 1.64/1.03  --sat_fm_prep                           false
% 1.64/1.03  --sat_fm_uc_incr                        true
% 1.64/1.03  --sat_out_model                         small
% 1.64/1.03  --sat_out_clauses                       false
% 1.64/1.03  
% 1.64/1.03  ------ QBF Options
% 1.64/1.03  
% 1.64/1.03  --qbf_mode                              false
% 1.64/1.03  --qbf_elim_univ                         false
% 1.64/1.03  --qbf_dom_inst                          none
% 1.64/1.03  --qbf_dom_pre_inst                      false
% 1.64/1.03  --qbf_sk_in                             false
% 1.64/1.03  --qbf_pred_elim                         true
% 1.64/1.03  --qbf_split                             512
% 1.64/1.03  
% 1.64/1.03  ------ BMC1 Options
% 1.64/1.03  
% 1.64/1.03  --bmc1_incremental                      false
% 1.64/1.03  --bmc1_axioms                           reachable_all
% 1.64/1.03  --bmc1_min_bound                        0
% 1.64/1.03  --bmc1_max_bound                        -1
% 1.64/1.03  --bmc1_max_bound_default                -1
% 1.64/1.03  --bmc1_symbol_reachability              true
% 1.64/1.03  --bmc1_property_lemmas                  false
% 1.64/1.03  --bmc1_k_induction                      false
% 1.64/1.03  --bmc1_non_equiv_states                 false
% 1.64/1.03  --bmc1_deadlock                         false
% 1.64/1.03  --bmc1_ucm                              false
% 1.64/1.03  --bmc1_add_unsat_core                   none
% 1.64/1.03  --bmc1_unsat_core_children              false
% 1.64/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.64/1.03  --bmc1_out_stat                         full
% 1.64/1.03  --bmc1_ground_init                      false
% 1.64/1.03  --bmc1_pre_inst_next_state              false
% 1.64/1.03  --bmc1_pre_inst_state                   false
% 1.64/1.03  --bmc1_pre_inst_reach_state             false
% 1.64/1.03  --bmc1_out_unsat_core                   false
% 1.64/1.03  --bmc1_aig_witness_out                  false
% 1.64/1.03  --bmc1_verbose                          false
% 1.64/1.03  --bmc1_dump_clauses_tptp                false
% 1.64/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.64/1.03  --bmc1_dump_file                        -
% 1.64/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.64/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.64/1.03  --bmc1_ucm_extend_mode                  1
% 1.64/1.03  --bmc1_ucm_init_mode                    2
% 1.64/1.03  --bmc1_ucm_cone_mode                    none
% 1.64/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.64/1.03  --bmc1_ucm_relax_model                  4
% 1.64/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.64/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.64/1.03  --bmc1_ucm_layered_model                none
% 1.64/1.03  --bmc1_ucm_max_lemma_size               10
% 1.64/1.03  
% 1.64/1.03  ------ AIG Options
% 1.64/1.03  
% 1.64/1.03  --aig_mode                              false
% 1.64/1.03  
% 1.64/1.03  ------ Instantiation Options
% 1.64/1.03  
% 1.64/1.03  --instantiation_flag                    true
% 1.64/1.03  --inst_sos_flag                         false
% 1.64/1.03  --inst_sos_phase                        true
% 1.64/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.64/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.64/1.03  --inst_lit_sel_side                     none
% 1.64/1.03  --inst_solver_per_active                1400
% 1.64/1.03  --inst_solver_calls_frac                1.
% 1.64/1.03  --inst_passive_queue_type               priority_queues
% 1.64/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.64/1.03  --inst_passive_queues_freq              [25;2]
% 1.64/1.03  --inst_dismatching                      true
% 1.64/1.03  --inst_eager_unprocessed_to_passive     true
% 1.64/1.03  --inst_prop_sim_given                   true
% 1.64/1.03  --inst_prop_sim_new                     false
% 1.64/1.03  --inst_subs_new                         false
% 1.64/1.03  --inst_eq_res_simp                      false
% 1.64/1.03  --inst_subs_given                       false
% 1.64/1.03  --inst_orphan_elimination               true
% 1.64/1.03  --inst_learning_loop_flag               true
% 1.64/1.03  --inst_learning_start                   3000
% 1.64/1.03  --inst_learning_factor                  2
% 1.64/1.03  --inst_start_prop_sim_after_learn       3
% 1.64/1.03  --inst_sel_renew                        solver
% 1.64/1.03  --inst_lit_activity_flag                true
% 1.64/1.03  --inst_restr_to_given                   false
% 1.64/1.03  --inst_activity_threshold               500
% 1.64/1.03  --inst_out_proof                        true
% 1.64/1.03  
% 1.64/1.03  ------ Resolution Options
% 1.64/1.03  
% 1.64/1.03  --resolution_flag                       false
% 1.64/1.03  --res_lit_sel                           adaptive
% 1.64/1.03  --res_lit_sel_side                      none
% 1.64/1.03  --res_ordering                          kbo
% 1.64/1.03  --res_to_prop_solver                    active
% 1.64/1.03  --res_prop_simpl_new                    false
% 1.64/1.03  --res_prop_simpl_given                  true
% 1.64/1.03  --res_passive_queue_type                priority_queues
% 1.64/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.64/1.03  --res_passive_queues_freq               [15;5]
% 1.64/1.03  --res_forward_subs                      full
% 1.64/1.03  --res_backward_subs                     full
% 1.64/1.03  --res_forward_subs_resolution           true
% 1.64/1.03  --res_backward_subs_resolution          true
% 1.64/1.03  --res_orphan_elimination                true
% 1.64/1.03  --res_time_limit                        2.
% 1.64/1.03  --res_out_proof                         true
% 1.64/1.03  
% 1.64/1.03  ------ Superposition Options
% 1.64/1.03  
% 1.64/1.03  --superposition_flag                    true
% 1.64/1.03  --sup_passive_queue_type                priority_queues
% 1.64/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.64/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.64/1.03  --demod_completeness_check              fast
% 1.64/1.03  --demod_use_ground                      true
% 1.64/1.03  --sup_to_prop_solver                    passive
% 1.64/1.03  --sup_prop_simpl_new                    true
% 1.64/1.03  --sup_prop_simpl_given                  true
% 1.64/1.03  --sup_fun_splitting                     false
% 1.64/1.03  --sup_smt_interval                      50000
% 1.64/1.03  
% 1.64/1.03  ------ Superposition Simplification Setup
% 1.64/1.03  
% 1.64/1.03  --sup_indices_passive                   []
% 1.64/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.64/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.03  --sup_full_bw                           [BwDemod]
% 1.64/1.03  --sup_immed_triv                        [TrivRules]
% 1.64/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.64/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.03  --sup_immed_bw_main                     []
% 1.64/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.64/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/1.03  
% 1.64/1.03  ------ Combination Options
% 1.64/1.03  
% 1.64/1.03  --comb_res_mult                         3
% 1.64/1.03  --comb_sup_mult                         2
% 1.64/1.03  --comb_inst_mult                        10
% 1.64/1.03  
% 1.64/1.03  ------ Debug Options
% 1.64/1.03  
% 1.64/1.03  --dbg_backtrace                         false
% 1.64/1.03  --dbg_dump_prop_clauses                 false
% 1.64/1.03  --dbg_dump_prop_clauses_file            -
% 1.64/1.03  --dbg_out_stat                          false
% 1.64/1.03  
% 1.64/1.03  
% 1.64/1.03  
% 1.64/1.03  
% 1.64/1.03  ------ Proving...
% 1.64/1.03  
% 1.64/1.03  
% 1.64/1.03  % SZS status Theorem for theBenchmark.p
% 1.64/1.03  
% 1.64/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.64/1.03  
% 1.64/1.03  fof(f19,conjecture,(
% 1.64/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f20,negated_conjecture,(
% 1.64/1.03    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.64/1.03    inference(negated_conjecture,[],[f19])).
% 1.64/1.03  
% 1.64/1.03  fof(f43,plain,(
% 1.64/1.03    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.64/1.03    inference(ennf_transformation,[],[f20])).
% 1.64/1.03  
% 1.64/1.03  fof(f44,plain,(
% 1.64/1.03    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.64/1.03    inference(flattening,[],[f43])).
% 1.64/1.03  
% 1.64/1.03  fof(f48,plain,(
% 1.64/1.03    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 1.64/1.03    introduced(choice_axiom,[])).
% 1.64/1.03  
% 1.64/1.03  fof(f47,plain,(
% 1.64/1.03    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.64/1.03    introduced(choice_axiom,[])).
% 1.64/1.03  
% 1.64/1.03  fof(f49,plain,(
% 1.64/1.03    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.64/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f48,f47])).
% 1.64/1.03  
% 1.64/1.03  fof(f80,plain,(
% 1.64/1.03    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f8,axiom,(
% 1.64/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f28,plain,(
% 1.64/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.03    inference(ennf_transformation,[],[f8])).
% 1.64/1.03  
% 1.64/1.03  fof(f61,plain,(
% 1.64/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.03    inference(cnf_transformation,[],[f28])).
% 1.64/1.03  
% 1.64/1.03  fof(f3,axiom,(
% 1.64/1.03    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f25,plain,(
% 1.64/1.03    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.64/1.03    inference(ennf_transformation,[],[f3])).
% 1.64/1.03  
% 1.64/1.03  fof(f54,plain,(
% 1.64/1.03    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.64/1.03    inference(cnf_transformation,[],[f25])).
% 1.64/1.03  
% 1.64/1.03  fof(f16,axiom,(
% 1.64/1.03    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f73,plain,(
% 1.64/1.03    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.64/1.03    inference(cnf_transformation,[],[f16])).
% 1.64/1.03  
% 1.64/1.03  fof(f89,plain,(
% 1.64/1.03    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.64/1.03    inference(definition_unfolding,[],[f54,f73])).
% 1.64/1.03  
% 1.64/1.03  fof(f9,axiom,(
% 1.64/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f22,plain,(
% 1.64/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.64/1.03    inference(pure_predicate_removal,[],[f9])).
% 1.64/1.03  
% 1.64/1.03  fof(f29,plain,(
% 1.64/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.03    inference(ennf_transformation,[],[f22])).
% 1.64/1.03  
% 1.64/1.03  fof(f62,plain,(
% 1.64/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.03    inference(cnf_transformation,[],[f29])).
% 1.64/1.03  
% 1.64/1.03  fof(f13,axiom,(
% 1.64/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f35,plain,(
% 1.64/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.64/1.03    inference(ennf_transformation,[],[f13])).
% 1.64/1.03  
% 1.64/1.03  fof(f36,plain,(
% 1.64/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/1.03    inference(flattening,[],[f35])).
% 1.64/1.03  
% 1.64/1.03  fof(f46,plain,(
% 1.64/1.03    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/1.03    inference(nnf_transformation,[],[f36])).
% 1.64/1.03  
% 1.64/1.03  fof(f69,plain,(
% 1.64/1.03    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.64/1.03    inference(cnf_transformation,[],[f46])).
% 1.64/1.03  
% 1.64/1.03  fof(f12,axiom,(
% 1.64/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f33,plain,(
% 1.64/1.03    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.03    inference(ennf_transformation,[],[f12])).
% 1.64/1.03  
% 1.64/1.03  fof(f34,plain,(
% 1.64/1.03    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.03    inference(flattening,[],[f33])).
% 1.64/1.03  
% 1.64/1.03  fof(f68,plain,(
% 1.64/1.03    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.03    inference(cnf_transformation,[],[f34])).
% 1.64/1.03  
% 1.64/1.03  fof(f79,plain,(
% 1.64/1.03    v3_funct_2(sK1,sK0,sK0)),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f77,plain,(
% 1.64/1.03    v1_funct_1(sK1)),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f7,axiom,(
% 1.64/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f26,plain,(
% 1.64/1.03    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.64/1.03    inference(ennf_transformation,[],[f7])).
% 1.64/1.03  
% 1.64/1.03  fof(f27,plain,(
% 1.64/1.03    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/1.03    inference(flattening,[],[f26])).
% 1.64/1.03  
% 1.64/1.03  fof(f60,plain,(
% 1.64/1.03    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/1.03    inference(cnf_transformation,[],[f27])).
% 1.64/1.03  
% 1.64/1.03  fof(f95,plain,(
% 1.64/1.03    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/1.03    inference(definition_unfolding,[],[f60,f73])).
% 1.64/1.03  
% 1.64/1.03  fof(f2,axiom,(
% 1.64/1.03    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f53,plain,(
% 1.64/1.03    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.64/1.03    inference(cnf_transformation,[],[f2])).
% 1.64/1.03  
% 1.64/1.03  fof(f87,plain,(
% 1.64/1.03    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.64/1.03    inference(definition_unfolding,[],[f53,f73])).
% 1.64/1.03  
% 1.64/1.03  fof(f52,plain,(
% 1.64/1.03    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.64/1.03    inference(cnf_transformation,[],[f2])).
% 1.64/1.03  
% 1.64/1.03  fof(f88,plain,(
% 1.64/1.03    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.64/1.03    inference(definition_unfolding,[],[f52,f73])).
% 1.64/1.03  
% 1.64/1.03  fof(f6,axiom,(
% 1.64/1.03    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f58,plain,(
% 1.64/1.03    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.64/1.03    inference(cnf_transformation,[],[f6])).
% 1.64/1.03  
% 1.64/1.03  fof(f94,plain,(
% 1.64/1.03    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.64/1.03    inference(definition_unfolding,[],[f58,f73])).
% 1.64/1.03  
% 1.64/1.03  fof(f59,plain,(
% 1.64/1.03    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.64/1.03    inference(cnf_transformation,[],[f6])).
% 1.64/1.03  
% 1.64/1.03  fof(f93,plain,(
% 1.64/1.03    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.64/1.03    inference(definition_unfolding,[],[f59,f73])).
% 1.64/1.03  
% 1.64/1.03  fof(f5,axiom,(
% 1.64/1.03    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f57,plain,(
% 1.64/1.03    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.64/1.03    inference(cnf_transformation,[],[f5])).
% 1.64/1.03  
% 1.64/1.03  fof(f91,plain,(
% 1.64/1.03    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 1.64/1.03    inference(definition_unfolding,[],[f57,f73])).
% 1.64/1.03  
% 1.64/1.03  fof(f4,axiom,(
% 1.64/1.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f55,plain,(
% 1.64/1.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.64/1.03    inference(cnf_transformation,[],[f4])).
% 1.64/1.03  
% 1.64/1.03  fof(f90,plain,(
% 1.64/1.03    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.64/1.03    inference(definition_unfolding,[],[f55,f73])).
% 1.64/1.03  
% 1.64/1.03  fof(f85,plain,(
% 1.64/1.03    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f10,axiom,(
% 1.64/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f30,plain,(
% 1.64/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.03    inference(ennf_transformation,[],[f10])).
% 1.64/1.03  
% 1.64/1.03  fof(f63,plain,(
% 1.64/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.03    inference(cnf_transformation,[],[f30])).
% 1.64/1.03  
% 1.64/1.03  fof(f18,axiom,(
% 1.64/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f41,plain,(
% 1.64/1.03    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.64/1.03    inference(ennf_transformation,[],[f18])).
% 1.64/1.03  
% 1.64/1.03  fof(f42,plain,(
% 1.64/1.03    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.64/1.03    inference(flattening,[],[f41])).
% 1.64/1.03  
% 1.64/1.03  fof(f76,plain,(
% 1.64/1.03    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.64/1.03    inference(cnf_transformation,[],[f42])).
% 1.64/1.03  
% 1.64/1.03  fof(f17,axiom,(
% 1.64/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f39,plain,(
% 1.64/1.03    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.64/1.03    inference(ennf_transformation,[],[f17])).
% 1.64/1.03  
% 1.64/1.03  fof(f40,plain,(
% 1.64/1.03    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.64/1.03    inference(flattening,[],[f39])).
% 1.64/1.03  
% 1.64/1.03  fof(f74,plain,(
% 1.64/1.03    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.64/1.03    inference(cnf_transformation,[],[f40])).
% 1.64/1.03  
% 1.64/1.03  fof(f78,plain,(
% 1.64/1.03    v1_funct_2(sK1,sK0,sK0)),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f81,plain,(
% 1.64/1.03    v1_funct_1(sK2)),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f82,plain,(
% 1.64/1.03    v1_funct_2(sK2,sK0,sK0)),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f84,plain,(
% 1.64/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f86,plain,(
% 1.64/1.03    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f15,axiom,(
% 1.64/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f37,plain,(
% 1.64/1.03    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.64/1.03    inference(ennf_transformation,[],[f15])).
% 1.64/1.03  
% 1.64/1.03  fof(f38,plain,(
% 1.64/1.03    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.64/1.03    inference(flattening,[],[f37])).
% 1.64/1.03  
% 1.64/1.03  fof(f72,plain,(
% 1.64/1.03    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.64/1.03    inference(cnf_transformation,[],[f38])).
% 1.64/1.03  
% 1.64/1.03  fof(f11,axiom,(
% 1.64/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f31,plain,(
% 1.64/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.64/1.03    inference(ennf_transformation,[],[f11])).
% 1.64/1.03  
% 1.64/1.03  fof(f32,plain,(
% 1.64/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.03    inference(flattening,[],[f31])).
% 1.64/1.03  
% 1.64/1.03  fof(f45,plain,(
% 1.64/1.03    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.03    inference(nnf_transformation,[],[f32])).
% 1.64/1.03  
% 1.64/1.03  fof(f65,plain,(
% 1.64/1.03    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.03    inference(cnf_transformation,[],[f45])).
% 1.64/1.03  
% 1.64/1.03  fof(f96,plain,(
% 1.64/1.03    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.03    inference(equality_resolution,[],[f65])).
% 1.64/1.03  
% 1.64/1.03  fof(f1,axiom,(
% 1.64/1.03    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f23,plain,(
% 1.64/1.03    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.64/1.03    inference(ennf_transformation,[],[f1])).
% 1.64/1.03  
% 1.64/1.03  fof(f24,plain,(
% 1.64/1.03    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.64/1.03    inference(flattening,[],[f23])).
% 1.64/1.03  
% 1.64/1.03  fof(f51,plain,(
% 1.64/1.03    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/1.03    inference(cnf_transformation,[],[f24])).
% 1.64/1.03  
% 1.64/1.03  fof(f83,plain,(
% 1.64/1.03    v3_funct_2(sK2,sK0,sK0)),
% 1.64/1.03    inference(cnf_transformation,[],[f49])).
% 1.64/1.03  
% 1.64/1.03  fof(f14,axiom,(
% 1.64/1.03    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/1.03  
% 1.64/1.03  fof(f21,plain,(
% 1.64/1.03    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.64/1.03    inference(pure_predicate_removal,[],[f14])).
% 1.64/1.03  
% 1.64/1.03  fof(f71,plain,(
% 1.64/1.03    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.64/1.03    inference(cnf_transformation,[],[f21])).
% 1.64/1.03  
% 1.64/1.03  cnf(c_32,negated_conjecture,
% 1.64/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.64/1.03      inference(cnf_transformation,[],[f80]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2288,plain,
% 1.64/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_11,plain,
% 1.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.03      | v1_relat_1(X0) ),
% 1.64/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2300,plain,
% 1.64/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.64/1.03      | v1_relat_1(X0) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_4105,plain,
% 1.64/1.03      ( v1_relat_1(sK1) = iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_2288,c_2300]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_4,plain,
% 1.64/1.03      ( ~ v1_relat_1(X0)
% 1.64/1.03      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 1.64/1.03      inference(cnf_transformation,[],[f89]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2305,plain,
% 1.64/1.03      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 1.64/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_4279,plain,
% 1.64/1.03      ( k5_relat_1(sK1,k6_partfun1(k2_relat_1(sK1))) = sK1 ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_4105,c_2305]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_12,plain,
% 1.64/1.03      ( v5_relat_1(X0,X1)
% 1.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.64/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_20,plain,
% 1.64/1.03      ( ~ v2_funct_2(X0,X1)
% 1.64/1.03      | ~ v5_relat_1(X0,X1)
% 1.64/1.03      | ~ v1_relat_1(X0)
% 1.64/1.03      | k2_relat_1(X0) = X1 ),
% 1.64/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_366,plain,
% 1.64/1.03      ( ~ v2_funct_2(X0,X1)
% 1.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.64/1.03      | ~ v1_relat_1(X0)
% 1.64/1.03      | k2_relat_1(X0) = X1 ),
% 1.64/1.03      inference(resolution,[status(thm)],[c_12,c_20]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_378,plain,
% 1.64/1.03      ( ~ v2_funct_2(X0,X1)
% 1.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.64/1.03      | k2_relat_1(X0) = X1 ),
% 1.64/1.03      inference(forward_subsumption_resolution,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_366,c_11]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2284,plain,
% 1.64/1.03      ( k2_relat_1(X0) = X1
% 1.64/1.03      | v2_funct_2(X0,X1) != iProver_top
% 1.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_4378,plain,
% 1.64/1.03      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_2288,c_2284]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_16,plain,
% 1.64/1.03      ( ~ v3_funct_2(X0,X1,X2)
% 1.64/1.03      | v2_funct_2(X0,X2)
% 1.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.03      | ~ v1_funct_1(X0) ),
% 1.64/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_33,negated_conjecture,
% 1.64/1.03      ( v3_funct_2(sK1,sK0,sK0) ),
% 1.64/1.03      inference(cnf_transformation,[],[f79]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_512,plain,
% 1.64/1.03      ( v2_funct_2(X0,X1)
% 1.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.64/1.03      | ~ v1_funct_1(X0)
% 1.64/1.03      | sK1 != X0
% 1.64/1.03      | sK0 != X1
% 1.64/1.03      | sK0 != X2 ),
% 1.64/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_513,plain,
% 1.64/1.03      ( v2_funct_2(sK1,sK0)
% 1.64/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/1.03      | ~ v1_funct_1(sK1) ),
% 1.64/1.03      inference(unflattening,[status(thm)],[c_512]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_35,negated_conjecture,
% 1.64/1.03      ( v1_funct_1(sK1) ),
% 1.64/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_515,plain,
% 1.64/1.03      ( v2_funct_2(sK1,sK0) ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_513,c_35,c_32]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_592,plain,
% 1.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.03      | k2_relat_1(X0) = X2
% 1.64/1.03      | sK1 != X0
% 1.64/1.03      | sK0 != X2 ),
% 1.64/1.03      inference(resolution_lifted,[status(thm)],[c_378,c_515]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_593,plain,
% 1.64/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 1.64/1.03      | k2_relat_1(sK1) = sK0 ),
% 1.64/1.03      inference(unflattening,[status(thm)],[c_592]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_595,plain,
% 1.64/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/1.03      | k2_relat_1(sK1) = sK0 ),
% 1.64/1.03      inference(instantiation,[status(thm)],[c_593]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5306,plain,
% 1.64/1.03      ( k2_relat_1(sK1) = sK0 ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_4378,c_32,c_595]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5392,plain,
% 1.64/1.03      ( k5_relat_1(sK1,k6_partfun1(sK0)) = sK1 ),
% 1.64/1.03      inference(light_normalisation,[status(thm)],[c_4279,c_5306]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_10,plain,
% 1.64/1.03      ( ~ v2_funct_1(X0)
% 1.64/1.03      | ~ v1_funct_1(X1)
% 1.64/1.03      | ~ v1_funct_1(X0)
% 1.64/1.03      | ~ v1_relat_1(X0)
% 1.64/1.03      | ~ v1_relat_1(X1)
% 1.64/1.03      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 1.64/1.03      | k2_funct_1(X0) = X1
% 1.64/1.03      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 1.64/1.03      inference(cnf_transformation,[],[f95]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2301,plain,
% 1.64/1.03      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 1.64/1.03      | k2_funct_1(X1) = X0
% 1.64/1.03      | k1_relat_1(X1) != k2_relat_1(X0)
% 1.64/1.03      | v2_funct_1(X1) != iProver_top
% 1.64/1.03      | v1_funct_1(X1) != iProver_top
% 1.64/1.03      | v1_funct_1(X0) != iProver_top
% 1.64/1.03      | v1_relat_1(X1) != iProver_top
% 1.64/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6345,plain,
% 1.64/1.03      ( k2_funct_1(k6_partfun1(sK0)) = sK1
% 1.64/1.03      | k6_partfun1(k2_relat_1(k6_partfun1(sK0))) != sK1
% 1.64/1.03      | k1_relat_1(k6_partfun1(sK0)) != k2_relat_1(sK1)
% 1.64/1.03      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_1(sK1) != iProver_top
% 1.64/1.03      | v1_relat_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_relat_1(sK1) != iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_5392,c_2301]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6354,plain,
% 1.64/1.03      ( k2_funct_1(k6_partfun1(sK0)) = sK1
% 1.64/1.03      | k6_partfun1(k2_relat_1(k6_partfun1(sK0))) != sK1
% 1.64/1.03      | k1_relat_1(k6_partfun1(sK0)) != sK0
% 1.64/1.03      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_1(sK1) != iProver_top
% 1.64/1.03      | v1_relat_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_relat_1(sK1) != iProver_top ),
% 1.64/1.03      inference(light_normalisation,[status(thm)],[c_6345,c_5306]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2,plain,
% 1.64/1.03      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 1.64/1.03      inference(cnf_transformation,[],[f87]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_3,plain,
% 1.64/1.03      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 1.64/1.03      inference(cnf_transformation,[],[f88]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6355,plain,
% 1.64/1.03      ( k2_funct_1(k6_partfun1(sK0)) = sK1
% 1.64/1.03      | k6_partfun1(sK0) != sK1
% 1.64/1.03      | sK0 != sK0
% 1.64/1.03      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_1(sK1) != iProver_top
% 1.64/1.03      | v1_relat_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_relat_1(sK1) != iProver_top ),
% 1.64/1.03      inference(demodulation,[status(thm)],[c_6354,c_2,c_3]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6356,plain,
% 1.64/1.03      ( k2_funct_1(k6_partfun1(sK0)) = sK1
% 1.64/1.03      | k6_partfun1(sK0) != sK1
% 1.64/1.03      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_1(sK1) != iProver_top
% 1.64/1.03      | v1_relat_1(k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_relat_1(sK1) != iProver_top ),
% 1.64/1.03      inference(equality_resolution_simp,[status(thm)],[c_6355]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_9,plain,
% 1.64/1.03      ( v1_relat_1(k6_partfun1(X0)) ),
% 1.64/1.03      inference(cnf_transformation,[],[f94]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_93,plain,
% 1.64/1.03      ( v1_relat_1(k6_partfun1(sK0)) ),
% 1.64/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_8,plain,
% 1.64/1.03      ( v2_funct_1(k6_partfun1(X0)) ),
% 1.64/1.03      inference(cnf_transformation,[],[f93]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_96,plain,
% 1.64/1.03      ( v2_funct_1(k6_partfun1(sK0)) ),
% 1.64/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6,plain,
% 1.64/1.03      ( v1_funct_1(k6_partfun1(X0)) ),
% 1.64/1.03      inference(cnf_transformation,[],[f91]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_100,plain,
% 1.64/1.03      ( v1_funct_1(k6_partfun1(sK0)) ),
% 1.64/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2547,plain,
% 1.64/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/1.03      | v1_relat_1(sK1) ),
% 1.64/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6406,plain,
% 1.64/1.03      ( ~ v2_funct_1(k6_partfun1(sK0))
% 1.64/1.03      | ~ v1_funct_1(k6_partfun1(sK0))
% 1.64/1.03      | ~ v1_funct_1(sK1)
% 1.64/1.03      | ~ v1_relat_1(k6_partfun1(sK0))
% 1.64/1.03      | ~ v1_relat_1(sK1)
% 1.64/1.03      | k2_funct_1(k6_partfun1(sK0)) = sK1
% 1.64/1.03      | k6_partfun1(sK0) != sK1 ),
% 1.64/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_6356]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_8282,plain,
% 1.64/1.03      ( k6_partfun1(sK0) != sK1 | k2_funct_1(k6_partfun1(sK0)) = sK1 ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_6356,c_35,c_32,c_93,c_96,c_100,c_2547,c_6406]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_8283,plain,
% 1.64/1.03      ( k2_funct_1(k6_partfun1(sK0)) = sK1 | k6_partfun1(sK0) != sK1 ),
% 1.64/1.03      inference(renaming,[status(thm)],[c_8282]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5,plain,
% 1.64/1.03      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 1.64/1.03      inference(cnf_transformation,[],[f90]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_27,negated_conjecture,
% 1.64/1.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 1.64/1.03      inference(cnf_transformation,[],[f85]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2292,plain,
% 1.64/1.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_13,plain,
% 1.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.64/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2299,plain,
% 1.64/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.64/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5510,plain,
% 1.64/1.03      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_2288,c_2299]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5516,plain,
% 1.64/1.03      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 1.64/1.03      inference(light_normalisation,[status(thm)],[c_5510,c_5306]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_25,plain,
% 1.64/1.03      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 1.64/1.03      | ~ v1_funct_2(X3,X1,X0)
% 1.64/1.03      | ~ v1_funct_2(X2,X0,X1)
% 1.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.64/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 1.64/1.03      | ~ v2_funct_1(X2)
% 1.64/1.03      | ~ v1_funct_1(X2)
% 1.64/1.03      | ~ v1_funct_1(X3)
% 1.64/1.03      | k2_relset_1(X0,X1,X2) != X1
% 1.64/1.03      | k2_funct_1(X2) = X3
% 1.64/1.03      | k1_xboole_0 = X0
% 1.64/1.03      | k1_xboole_0 = X1 ),
% 1.64/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_24,plain,
% 1.64/1.03      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 1.64/1.03      | ~ v1_funct_2(X3,X1,X0)
% 1.64/1.03      | ~ v1_funct_2(X2,X0,X1)
% 1.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.64/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 1.64/1.03      | v2_funct_1(X2)
% 1.64/1.03      | ~ v1_funct_1(X2)
% 1.64/1.03      | ~ v1_funct_1(X3) ),
% 1.64/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_190,plain,
% 1.64/1.03      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 1.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.64/1.03      | ~ v1_funct_2(X2,X0,X1)
% 1.64/1.03      | ~ v1_funct_2(X3,X1,X0)
% 1.64/1.03      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 1.64/1.03      | ~ v1_funct_1(X2)
% 1.64/1.03      | ~ v1_funct_1(X3)
% 1.64/1.03      | k2_relset_1(X0,X1,X2) != X1
% 1.64/1.03      | k2_funct_1(X2) = X3
% 1.64/1.03      | k1_xboole_0 = X0
% 1.64/1.03      | k1_xboole_0 = X1 ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_25,c_24]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_191,plain,
% 1.64/1.03      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 1.64/1.03      | ~ v1_funct_2(X3,X1,X0)
% 1.64/1.03      | ~ v1_funct_2(X2,X0,X1)
% 1.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.64/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 1.64/1.03      | ~ v1_funct_1(X2)
% 1.64/1.03      | ~ v1_funct_1(X3)
% 1.64/1.03      | k2_relset_1(X0,X1,X2) != X1
% 1.64/1.03      | k2_funct_1(X2) = X3
% 1.64/1.03      | k1_xboole_0 = X0
% 1.64/1.03      | k1_xboole_0 = X1 ),
% 1.64/1.03      inference(renaming,[status(thm)],[c_190]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2285,plain,
% 1.64/1.03      ( k2_relset_1(X0,X1,X2) != X1
% 1.64/1.03      | k2_funct_1(X2) = X3
% 1.64/1.03      | k1_xboole_0 = X0
% 1.64/1.03      | k1_xboole_0 = X1
% 1.64/1.03      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 1.64/1.03      | v1_funct_2(X3,X1,X0) != iProver_top
% 1.64/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.64/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.64/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 1.64/1.03      | v1_funct_1(X2) != iProver_top
% 1.64/1.03      | v1_funct_1(X3) != iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6202,plain,
% 1.64/1.03      ( k2_funct_1(sK1) = X0
% 1.64/1.03      | sK0 = k1_xboole_0
% 1.64/1.03      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 1.64/1.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 1.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 1.64/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 1.64/1.03      | v1_funct_1(X0) != iProver_top
% 1.64/1.03      | v1_funct_1(sK1) != iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_5516,c_2285]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_36,plain,
% 1.64/1.03      ( v1_funct_1(sK1) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_34,negated_conjecture,
% 1.64/1.03      ( v1_funct_2(sK1,sK0,sK0) ),
% 1.64/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_37,plain,
% 1.64/1.03      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_39,plain,
% 1.64/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6759,plain,
% 1.64/1.03      ( v1_funct_1(X0) != iProver_top
% 1.64/1.03      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 1.64/1.03      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | sK0 = k1_xboole_0
% 1.64/1.03      | k2_funct_1(sK1) = X0
% 1.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_6202,c_36,c_37,c_39]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6760,plain,
% 1.64/1.03      ( k2_funct_1(sK1) = X0
% 1.64/1.03      | sK0 = k1_xboole_0
% 1.64/1.03      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 1.64/1.03      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 1.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 1.64/1.03      | v1_funct_1(X0) != iProver_top ),
% 1.64/1.03      inference(renaming,[status(thm)],[c_6759]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6771,plain,
% 1.64/1.03      ( k2_funct_1(sK1) = sK2
% 1.64/1.03      | sK0 = k1_xboole_0
% 1.64/1.03      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 1.64/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 1.64/1.03      | v1_funct_1(sK2) != iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_2292,c_6760]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_31,negated_conjecture,
% 1.64/1.03      ( v1_funct_1(sK2) ),
% 1.64/1.03      inference(cnf_transformation,[],[f81]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_30,negated_conjecture,
% 1.64/1.03      ( v1_funct_2(sK2,sK0,sK0) ),
% 1.64/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_28,negated_conjecture,
% 1.64/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.64/1.03      inference(cnf_transformation,[],[f84]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6772,plain,
% 1.64/1.03      ( ~ v1_funct_2(sK2,sK0,sK0)
% 1.64/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/1.03      | ~ v1_funct_1(sK2)
% 1.64/1.03      | k2_funct_1(sK1) = sK2
% 1.64/1.03      | sK0 = k1_xboole_0 ),
% 1.64/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_6771]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6855,plain,
% 1.64/1.03      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_6771,c_40,c_41,c_43]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6856,plain,
% 1.64/1.03      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 1.64/1.03      inference(renaming,[status(thm)],[c_6855]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_26,negated_conjecture,
% 1.64/1.03      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 1.64/1.03      inference(cnf_transformation,[],[f86]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2293,plain,
% 1.64/1.03      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_22,plain,
% 1.64/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 1.64/1.03      | ~ v3_funct_2(X0,X1,X1)
% 1.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/1.03      | ~ v1_funct_1(X0)
% 1.64/1.03      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 1.64/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_531,plain,
% 1.64/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 1.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/1.03      | ~ v1_funct_1(X0)
% 1.64/1.03      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 1.64/1.03      | sK1 != X0
% 1.64/1.03      | sK0 != X1 ),
% 1.64/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_532,plain,
% 1.64/1.03      ( ~ v1_funct_2(sK1,sK0,sK0)
% 1.64/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/1.03      | ~ v1_funct_1(sK1)
% 1.64/1.03      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 1.64/1.03      inference(unflattening,[status(thm)],[c_531]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_534,plain,
% 1.64/1.03      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_532,c_35,c_34,c_32]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2346,plain,
% 1.64/1.03      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 1.64/1.03      inference(light_normalisation,[status(thm)],[c_2293,c_534]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6859,plain,
% 1.64/1.03      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_6856,c_2346]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_43,plain,
% 1.64/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_14,plain,
% 1.64/1.03      ( r2_relset_1(X0,X1,X2,X2)
% 1.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.64/1.03      inference(cnf_transformation,[],[f96]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2590,plain,
% 1.64/1.03      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 1.64/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.64/1.03      inference(instantiation,[status(thm)],[c_14]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2591,plain,
% 1.64/1.03      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 1.64/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_2590]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6862,plain,
% 1.64/1.03      ( sK0 = k1_xboole_0 ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_6859,c_43,c_2591]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_0,plain,
% 1.64/1.03      ( ~ v1_relat_1(X0)
% 1.64/1.03      | k2_relat_1(X0) != k1_xboole_0
% 1.64/1.03      | k1_xboole_0 = X0 ),
% 1.64/1.03      inference(cnf_transformation,[],[f51]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2307,plain,
% 1.64/1.03      ( k2_relat_1(X0) != k1_xboole_0
% 1.64/1.03      | k1_xboole_0 = X0
% 1.64/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5309,plain,
% 1.64/1.03      ( sK1 = k1_xboole_0
% 1.64/1.03      | sK0 != k1_xboole_0
% 1.64/1.03      | v1_relat_1(sK1) != iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_5306,c_2307]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2548,plain,
% 1.64/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 1.64/1.03      | v1_relat_1(sK1) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_2547]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5408,plain,
% 1.64/1.03      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_5309,c_39,c_2548]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5409,plain,
% 1.64/1.03      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 1.64/1.03      inference(renaming,[status(thm)],[c_5408]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6874,plain,
% 1.64/1.03      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 1.64/1.03      inference(demodulation,[status(thm)],[c_6862,c_5409]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6949,plain,
% 1.64/1.03      ( sK1 = k1_xboole_0 ),
% 1.64/1.03      inference(equality_resolution_simp,[status(thm)],[c_6874]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_8284,plain,
% 1.64/1.03      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 1.64/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 1.64/1.03      inference(light_normalisation,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_8283,c_5,c_6862,c_6949]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_8285,plain,
% 1.64/1.03      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 1.64/1.03      inference(equality_resolution_simp,[status(thm)],[c_8284]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2291,plain,
% 1.64/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_4377,plain,
% 1.64/1.03      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_2291,c_2284]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_29,negated_conjecture,
% 1.64/1.03      ( v3_funct_2(sK2,sK0,sK0) ),
% 1.64/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_490,plain,
% 1.64/1.03      ( v2_funct_2(X0,X1)
% 1.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.64/1.03      | ~ v1_funct_1(X0)
% 1.64/1.03      | sK2 != X0
% 1.64/1.03      | sK0 != X1
% 1.64/1.03      | sK0 != X2 ),
% 1.64/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_491,plain,
% 1.64/1.03      ( v2_funct_2(sK2,sK0)
% 1.64/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/1.03      | ~ v1_funct_1(sK2) ),
% 1.64/1.03      inference(unflattening,[status(thm)],[c_490]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_493,plain,
% 1.64/1.03      ( v2_funct_2(sK2,sK0) ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_491,c_31,c_28]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_582,plain,
% 1.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.03      | k2_relat_1(X0) = X2
% 1.64/1.03      | sK2 != X0
% 1.64/1.03      | sK0 != X2 ),
% 1.64/1.03      inference(resolution_lifted,[status(thm)],[c_378,c_493]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_583,plain,
% 1.64/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 1.64/1.03      | k2_relat_1(sK2) = sK0 ),
% 1.64/1.03      inference(unflattening,[status(thm)],[c_582]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_585,plain,
% 1.64/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/1.03      | k2_relat_1(sK2) = sK0 ),
% 1.64/1.03      inference(instantiation,[status(thm)],[c_583]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5217,plain,
% 1.64/1.03      ( k2_relat_1(sK2) = sK0 ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_4377,c_28,c_585]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5220,plain,
% 1.64/1.03      ( sK2 = k1_xboole_0
% 1.64/1.03      | sK0 != k1_xboole_0
% 1.64/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_5217,c_2307]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2544,plain,
% 1.64/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/1.03      | v1_relat_1(sK2) ),
% 1.64/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5231,plain,
% 1.64/1.03      ( ~ v1_relat_1(sK2) | sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 1.64/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_5220]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5395,plain,
% 1.64/1.03      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 1.64/1.03      inference(global_propositional_subsumption,
% 1.64/1.03                [status(thm)],
% 1.64/1.03                [c_5220,c_28,c_2544,c_5231]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_5396,plain,
% 1.64/1.03      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 1.64/1.03      inference(renaming,[status(thm)],[c_5395]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6875,plain,
% 1.64/1.03      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 1.64/1.03      inference(demodulation,[status(thm)],[c_6862,c_5396]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6927,plain,
% 1.64/1.03      ( sK2 = k1_xboole_0 ),
% 1.64/1.03      inference(equality_resolution_simp,[status(thm)],[c_6875]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6882,plain,
% 1.64/1.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 1.64/1.03      inference(demodulation,[status(thm)],[c_6862,c_2346]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6932,plain,
% 1.64/1.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 1.64/1.03      inference(demodulation,[status(thm)],[c_6927,c_6882]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_6951,plain,
% 1.64/1.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 1.64/1.03      inference(demodulation,[status(thm)],[c_6949,c_6932]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_8287,plain,
% 1.64/1.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.64/1.03      inference(demodulation,[status(thm)],[c_8285,c_6951]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_21,plain,
% 1.64/1.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 1.64/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2296,plain,
% 1.64/1.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_3993,plain,
% 1.64/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_5,c_2296]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_2298,plain,
% 1.64/1.03      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 1.64/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.64/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(c_4831,plain,
% 1.64/1.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.64/1.03      inference(superposition,[status(thm)],[c_3993,c_2298]) ).
% 1.64/1.03  
% 1.64/1.03  cnf(contradiction,plain,
% 1.64/1.03      ( $false ),
% 1.64/1.03      inference(minisat,[status(thm)],[c_8287,c_4831]) ).
% 1.64/1.03  
% 1.64/1.03  
% 1.64/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.64/1.03  
% 1.64/1.03  ------                               Statistics
% 1.64/1.03  
% 1.64/1.03  ------ General
% 1.64/1.03  
% 1.64/1.03  abstr_ref_over_cycles:                  0
% 1.64/1.03  abstr_ref_under_cycles:                 0
% 1.64/1.03  gc_basic_clause_elim:                   0
% 1.64/1.03  forced_gc_time:                         0
% 1.64/1.03  parsing_time:                           0.009
% 1.64/1.03  unif_index_cands_time:                  0.
% 1.64/1.03  unif_index_add_time:                    0.
% 1.64/1.03  orderings_time:                         0.
% 1.64/1.03  out_proof_time:                         0.01
% 1.64/1.03  total_time:                             0.258
% 1.64/1.03  num_of_symbols:                         54
% 1.64/1.03  num_of_terms:                           9117
% 1.64/1.03  
% 1.64/1.03  ------ Preprocessing
% 1.64/1.03  
% 1.64/1.03  num_of_splits:                          0
% 1.64/1.03  num_of_split_atoms:                     0
% 1.64/1.03  num_of_reused_defs:                     0
% 1.64/1.03  num_eq_ax_congr_red:                    15
% 1.64/1.03  num_of_sem_filtered_clauses:            1
% 1.64/1.03  num_of_subtypes:                        0
% 1.64/1.03  monotx_restored_types:                  0
% 1.64/1.03  sat_num_of_epr_types:                   0
% 1.64/1.03  sat_num_of_non_cyclic_types:            0
% 1.64/1.03  sat_guarded_non_collapsed_types:        0
% 1.64/1.03  num_pure_diseq_elim:                    0
% 1.64/1.03  simp_replaced_by:                       0
% 1.64/1.03  res_preprocessed:                       173
% 1.64/1.03  prep_upred:                             0
% 1.64/1.03  prep_unflattend:                        94
% 1.64/1.03  smt_new_axioms:                         0
% 1.64/1.03  pred_elim_cands:                        7
% 1.64/1.03  pred_elim:                              2
% 1.64/1.03  pred_elim_cl:                           0
% 1.64/1.03  pred_elim_cycles:                       9
% 1.64/1.03  merged_defs:                            0
% 1.64/1.03  merged_defs_ncl:                        0
% 1.64/1.03  bin_hyper_res:                          0
% 1.64/1.03  prep_cycles:                            4
% 1.64/1.03  pred_elim_time:                         0.026
% 1.64/1.03  splitting_time:                         0.
% 1.64/1.03  sem_filter_time:                        0.
% 1.64/1.03  monotx_time:                            0.
% 1.64/1.03  subtype_inf_time:                       0.
% 1.64/1.03  
% 1.64/1.03  ------ Problem properties
% 1.64/1.03  
% 1.64/1.03  clauses:                                34
% 1.64/1.03  conjectures:                            8
% 1.64/1.03  epr:                                    8
% 1.64/1.03  horn:                                   33
% 1.64/1.03  ground:                                 15
% 1.64/1.03  unary:                                  21
% 1.64/1.03  binary:                                 5
% 1.64/1.03  lits:                                   79
% 1.64/1.03  lits_eq:                                20
% 1.64/1.03  fd_pure:                                0
% 1.64/1.03  fd_pseudo:                              0
% 1.64/1.03  fd_cond:                                2
% 1.64/1.03  fd_pseudo_cond:                         4
% 1.64/1.03  ac_symbols:                             0
% 1.64/1.03  
% 1.64/1.03  ------ Propositional Solver
% 1.64/1.03  
% 1.64/1.03  prop_solver_calls:                      27
% 1.64/1.03  prop_fast_solver_calls:                 1434
% 1.64/1.03  smt_solver_calls:                       0
% 1.64/1.03  smt_fast_solver_calls:                  0
% 1.64/1.03  prop_num_of_clauses:                    3192
% 1.64/1.03  prop_preprocess_simplified:             9926
% 1.64/1.03  prop_fo_subsumed:                       53
% 1.64/1.03  prop_solver_time:                       0.
% 1.64/1.03  smt_solver_time:                        0.
% 1.64/1.03  smt_fast_solver_time:                   0.
% 1.64/1.03  prop_fast_solver_time:                  0.
% 1.64/1.03  prop_unsat_core_time:                   0.
% 1.64/1.03  
% 1.64/1.03  ------ QBF
% 1.64/1.03  
% 1.64/1.03  qbf_q_res:                              0
% 1.64/1.03  qbf_num_tautologies:                    0
% 1.64/1.03  qbf_prep_cycles:                        0
% 1.64/1.03  
% 1.64/1.03  ------ BMC1
% 1.64/1.03  
% 1.64/1.03  bmc1_current_bound:                     -1
% 1.64/1.03  bmc1_last_solved_bound:                 -1
% 1.64/1.03  bmc1_unsat_core_size:                   -1
% 1.64/1.03  bmc1_unsat_core_parents_size:           -1
% 1.64/1.03  bmc1_merge_next_fun:                    0
% 1.64/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.64/1.03  
% 1.64/1.03  ------ Instantiation
% 1.64/1.03  
% 1.64/1.03  inst_num_of_clauses:                    976
% 1.64/1.03  inst_num_in_passive:                    491
% 1.64/1.03  inst_num_in_active:                     389
% 1.64/1.03  inst_num_in_unprocessed:                96
% 1.64/1.03  inst_num_of_loops:                      400
% 1.64/1.03  inst_num_of_learning_restarts:          0
% 1.64/1.03  inst_num_moves_active_passive:          10
% 1.64/1.03  inst_lit_activity:                      0
% 1.64/1.03  inst_lit_activity_moves:                0
% 1.64/1.03  inst_num_tautologies:                   0
% 1.64/1.03  inst_num_prop_implied:                  0
% 1.64/1.03  inst_num_existing_simplified:           0
% 1.64/1.03  inst_num_eq_res_simplified:             0
% 1.64/1.03  inst_num_child_elim:                    0
% 1.64/1.03  inst_num_of_dismatching_blockings:      52
% 1.64/1.03  inst_num_of_non_proper_insts:           701
% 1.64/1.03  inst_num_of_duplicates:                 0
% 1.64/1.03  inst_inst_num_from_inst_to_res:         0
% 1.64/1.03  inst_dismatching_checking_time:         0.
% 1.64/1.03  
% 1.64/1.03  ------ Resolution
% 1.64/1.03  
% 1.64/1.03  res_num_of_clauses:                     0
% 1.64/1.03  res_num_in_passive:                     0
% 1.64/1.03  res_num_in_active:                      0
% 1.64/1.03  res_num_of_loops:                       177
% 1.64/1.03  res_forward_subset_subsumed:            47
% 1.64/1.03  res_backward_subset_subsumed:           0
% 1.64/1.03  res_forward_subsumed:                   0
% 1.64/1.03  res_backward_subsumed:                  0
% 1.64/1.03  res_forward_subsumption_resolution:     5
% 1.64/1.03  res_backward_subsumption_resolution:    0
% 1.64/1.03  res_clause_to_clause_subsumption:       201
% 1.64/1.03  res_orphan_elimination:                 0
% 1.64/1.03  res_tautology_del:                      40
% 1.64/1.03  res_num_eq_res_simplified:              0
% 1.64/1.03  res_num_sel_changes:                    0
% 1.64/1.03  res_moves_from_active_to_pass:          0
% 1.64/1.03  
% 1.64/1.03  ------ Superposition
% 1.64/1.03  
% 1.64/1.03  sup_time_total:                         0.
% 1.64/1.03  sup_time_generating:                    0.
% 1.64/1.03  sup_time_sim_full:                      0.
% 1.64/1.03  sup_time_sim_immed:                     0.
% 1.64/1.03  
% 1.64/1.03  sup_num_of_clauses:                     49
% 1.64/1.03  sup_num_in_active:                      42
% 1.64/1.03  sup_num_in_passive:                     7
% 1.64/1.03  sup_num_of_loops:                       79
% 1.64/1.03  sup_fw_superposition:                   56
% 1.64/1.03  sup_bw_superposition:                   14
% 1.64/1.03  sup_immediate_simplified:               55
% 1.64/1.03  sup_given_eliminated:                   0
% 1.64/1.03  comparisons_done:                       0
% 1.64/1.03  comparisons_avoided:                    3
% 1.64/1.03  
% 1.64/1.03  ------ Simplifications
% 1.64/1.03  
% 1.64/1.03  
% 1.64/1.03  sim_fw_subset_subsumed:                 7
% 1.64/1.03  sim_bw_subset_subsumed:                 4
% 1.64/1.03  sim_fw_subsumed:                        2
% 1.64/1.03  sim_bw_subsumed:                        0
% 1.64/1.03  sim_fw_subsumption_res:                 0
% 1.64/1.03  sim_bw_subsumption_res:                 0
% 1.64/1.03  sim_tautology_del:                      0
% 1.64/1.03  sim_eq_tautology_del:                   10
% 1.64/1.03  sim_eq_res_simp:                        7
% 1.64/1.03  sim_fw_demodulated:                     5
% 1.64/1.03  sim_bw_demodulated:                     54
% 1.64/1.03  sim_light_normalised:                   33
% 1.64/1.03  sim_joinable_taut:                      0
% 1.64/1.03  sim_joinable_simp:                      0
% 1.64/1.03  sim_ac_normalised:                      0
% 1.64/1.03  sim_smt_subsumption:                    0
% 1.64/1.03  
%------------------------------------------------------------------------------
