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
% DateTime   : Thu Dec  3 12:07:16 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_39)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f92,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f74])).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f88,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f74])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f61,f74])).

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
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f50,f49])).

fof(f86,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f77,plain,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f75,plain,(
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

fof(f79,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f84,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1614,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3084,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1614])).

cnf(c_8,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_91,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3129,plain,
    ( k1_xboole_0 != X0
    | k6_partfun1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3084,c_91])).

cnf(c_3130,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3129])).

cnf(c_3134,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3130])).

cnf(c_1612,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1613,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2845,plain,
    ( k5_relat_1(k6_partfun1(X0),k6_partfun1(k2_relat_1(k6_partfun1(X0)))) = k6_partfun1(X0) ),
    inference(superposition,[status(thm)],[c_1612,c_1613])).

cnf(c_4,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2847,plain,
    ( k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(light_normalisation,[status(thm)],[c_2845,c_4])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_208,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_9])).

cnf(c_209,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_1598,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_3909,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
    | k6_partfun1(k1_relat_1(k6_partfun1(X0))) != k6_partfun1(X0)
    | k1_relat_1(k6_partfun1(X0)) != k2_relat_1(k6_partfun1(X0))
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2847,c_1598])).

cnf(c_3915,plain,
    ( X0 != X0
    | k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
    | k6_partfun1(X0) != k6_partfun1(X0)
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3909,c_4,c_5])).

cnf(c_3916,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3915])).

cnf(c_5568,plain,
    ( v1_funct_1(k6_partfun1(X0)) != iProver_top
    | k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3916,c_91])).

cnf(c_5569,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
    | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5568])).

cnf(c_5576,plain,
    ( k2_funct_1(k6_partfun1(k1_xboole_0)) = k6_partfun1(k1_xboole_0)
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_5569])).

cnf(c_5577,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5576,c_3134])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1606,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1602,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1617,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4050,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_1617])).

cnf(c_38,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_108,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_110,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_1804,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2440,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_2441,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2440])).

cnf(c_4206,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4050,c_38,c_110,c_2441])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_420,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_421,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_423,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_34,c_31])).

cnf(c_506,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_423])).

cnf(c_507,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_507])).

cnf(c_554,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_556,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_558,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_31,c_556])).

cnf(c_1595,plain,
    ( k2_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_4212,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_4206,c_1595])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1611,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3162,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1602,c_1611])).

cnf(c_4344,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_4212,c_3162])).

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
    inference(cnf_transformation,[],[f77])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_189,plain,
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

cnf(c_190,plain,
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
    inference(renaming,[status(thm)],[c_189])).

cnf(c_1599,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_4404,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4344,c_1599])).

cnf(c_35,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5069,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4404,c_35,c_36,c_38])).

cnf(c_5070,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5069])).

cnf(c_5081,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1606,c_5070])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5082,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5081])).

cnf(c_5279,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5081,c_39,c_40,c_42])).

cnf(c_5280,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5279])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1607,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_439,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_440,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_442,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_34,c_33,c_31])).

cnf(c_1652,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1607,c_442])).

cnf(c_5283,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5280,c_1652])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1852,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1853,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1852])).

cnf(c_6809,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5283,c_42,c_1853])).

cnf(c_28,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_409,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_410,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_412,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_30,c_27])).

cnf(c_493,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_412])).

cnf(c_494,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_494])).

cnf(c_538,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_540,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_542,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_27,c_540])).

cnf(c_1596,plain,
    ( k2_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_109,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2437,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_2838,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_27,c_109,c_540,c_2437])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1615,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3120,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2838,c_1615])).

cnf(c_3127,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3120])).

cnf(c_3780,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3120,c_27,c_109,c_2437,c_3127])).

cnf(c_3781,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3780])).

cnf(c_6827,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6809,c_3781])).

cnf(c_6865,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6827])).

cnf(c_1603,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7759,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6865,c_1603])).

cnf(c_8254,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5577,c_7759])).

cnf(c_4345,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_1615])).

cnf(c_4993,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4345,c_38,c_110,c_2441])).

cnf(c_4994,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4993])).

cnf(c_6816,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6809,c_4994])).

cnf(c_6923,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6816])).

cnf(c_6832,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6809,c_1652])).

cnf(c_6870,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6865,c_6832])).

cnf(c_6929,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6923,c_6870])).

cnf(c_8257,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8254,c_6929])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1608,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3788,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_1608])).

cnf(c_1610,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4667,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3788,c_1610])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8257,c_4667])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:02:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.21/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/0.99  
% 3.21/0.99  ------  iProver source info
% 3.21/0.99  
% 3.21/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.21/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/0.99  git: non_committed_changes: false
% 3.21/0.99  git: last_make_outside_of_git: false
% 3.21/0.99  
% 3.21/0.99  ------ 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options
% 3.21/0.99  
% 3.21/0.99  --out_options                           all
% 3.21/0.99  --tptp_safe_out                         true
% 3.21/0.99  --problem_path                          ""
% 3.21/0.99  --include_path                          ""
% 3.21/0.99  --clausifier                            res/vclausify_rel
% 3.21/0.99  --clausifier_options                    --mode clausify
% 3.21/0.99  --stdin                                 false
% 3.21/0.99  --stats_out                             all
% 3.21/0.99  
% 3.21/0.99  ------ General Options
% 3.21/0.99  
% 3.21/0.99  --fof                                   false
% 3.21/0.99  --time_out_real                         305.
% 3.21/0.99  --time_out_virtual                      -1.
% 3.21/0.99  --symbol_type_check                     false
% 3.21/0.99  --clausify_out                          false
% 3.21/0.99  --sig_cnt_out                           false
% 3.21/0.99  --trig_cnt_out                          false
% 3.21/0.99  --trig_cnt_out_tolerance                1.
% 3.21/0.99  --trig_cnt_out_sk_spl                   false
% 3.21/0.99  --abstr_cl_out                          false
% 3.21/0.99  
% 3.21/0.99  ------ Global Options
% 3.21/0.99  
% 3.21/0.99  --schedule                              default
% 3.21/0.99  --add_important_lit                     false
% 3.21/0.99  --prop_solver_per_cl                    1000
% 3.21/0.99  --min_unsat_core                        false
% 3.21/0.99  --soft_assumptions                      false
% 3.21/0.99  --soft_lemma_size                       3
% 3.21/0.99  --prop_impl_unit_size                   0
% 3.21/0.99  --prop_impl_unit                        []
% 3.21/0.99  --share_sel_clauses                     true
% 3.21/0.99  --reset_solvers                         false
% 3.21/0.99  --bc_imp_inh                            [conj_cone]
% 3.21/0.99  --conj_cone_tolerance                   3.
% 3.21/0.99  --extra_neg_conj                        none
% 3.21/0.99  --large_theory_mode                     true
% 3.21/0.99  --prolific_symb_bound                   200
% 3.21/0.99  --lt_threshold                          2000
% 3.21/0.99  --clause_weak_htbl                      true
% 3.21/0.99  --gc_record_bc_elim                     false
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing Options
% 3.21/0.99  
% 3.21/0.99  --preprocessing_flag                    true
% 3.21/0.99  --time_out_prep_mult                    0.1
% 3.21/0.99  --splitting_mode                        input
% 3.21/0.99  --splitting_grd                         true
% 3.21/0.99  --splitting_cvd                         false
% 3.21/0.99  --splitting_cvd_svl                     false
% 3.21/0.99  --splitting_nvd                         32
% 3.21/0.99  --sub_typing                            true
% 3.21/0.99  --prep_gs_sim                           true
% 3.21/0.99  --prep_unflatten                        true
% 3.21/0.99  --prep_res_sim                          true
% 3.21/0.99  --prep_upred                            true
% 3.21/0.99  --prep_sem_filter                       exhaustive
% 3.21/0.99  --prep_sem_filter_out                   false
% 3.21/0.99  --pred_elim                             true
% 3.21/0.99  --res_sim_input                         true
% 3.21/0.99  --eq_ax_congr_red                       true
% 3.21/0.99  --pure_diseq_elim                       true
% 3.21/0.99  --brand_transform                       false
% 3.21/0.99  --non_eq_to_eq                          false
% 3.21/0.99  --prep_def_merge                        true
% 3.21/0.99  --prep_def_merge_prop_impl              false
% 3.21/0.99  --prep_def_merge_mbd                    true
% 3.21/0.99  --prep_def_merge_tr_red                 false
% 3.21/0.99  --prep_def_merge_tr_cl                  false
% 3.21/0.99  --smt_preprocessing                     true
% 3.21/0.99  --smt_ac_axioms                         fast
% 3.21/0.99  --preprocessed_out                      false
% 3.21/0.99  --preprocessed_stats                    false
% 3.21/0.99  
% 3.21/0.99  ------ Abstraction refinement Options
% 3.21/0.99  
% 3.21/0.99  --abstr_ref                             []
% 3.21/0.99  --abstr_ref_prep                        false
% 3.21/0.99  --abstr_ref_until_sat                   false
% 3.21/0.99  --abstr_ref_sig_restrict                funpre
% 3.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/0.99  --abstr_ref_under                       []
% 3.21/0.99  
% 3.21/0.99  ------ SAT Options
% 3.21/0.99  
% 3.21/0.99  --sat_mode                              false
% 3.21/0.99  --sat_fm_restart_options                ""
% 3.21/0.99  --sat_gr_def                            false
% 3.21/0.99  --sat_epr_types                         true
% 3.21/0.99  --sat_non_cyclic_types                  false
% 3.21/0.99  --sat_finite_models                     false
% 3.21/0.99  --sat_fm_lemmas                         false
% 3.21/0.99  --sat_fm_prep                           false
% 3.21/0.99  --sat_fm_uc_incr                        true
% 3.21/0.99  --sat_out_model                         small
% 3.21/0.99  --sat_out_clauses                       false
% 3.21/0.99  
% 3.21/0.99  ------ QBF Options
% 3.21/0.99  
% 3.21/0.99  --qbf_mode                              false
% 3.21/0.99  --qbf_elim_univ                         false
% 3.21/0.99  --qbf_dom_inst                          none
% 3.21/0.99  --qbf_dom_pre_inst                      false
% 3.21/0.99  --qbf_sk_in                             false
% 3.21/0.99  --qbf_pred_elim                         true
% 3.21/0.99  --qbf_split                             512
% 3.21/0.99  
% 3.21/0.99  ------ BMC1 Options
% 3.21/0.99  
% 3.21/0.99  --bmc1_incremental                      false
% 3.21/0.99  --bmc1_axioms                           reachable_all
% 3.21/0.99  --bmc1_min_bound                        0
% 3.21/0.99  --bmc1_max_bound                        -1
% 3.21/0.99  --bmc1_max_bound_default                -1
% 3.21/0.99  --bmc1_symbol_reachability              true
% 3.21/0.99  --bmc1_property_lemmas                  false
% 3.21/0.99  --bmc1_k_induction                      false
% 3.21/0.99  --bmc1_non_equiv_states                 false
% 3.21/0.99  --bmc1_deadlock                         false
% 3.21/0.99  --bmc1_ucm                              false
% 3.21/0.99  --bmc1_add_unsat_core                   none
% 3.21/0.99  --bmc1_unsat_core_children              false
% 3.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/0.99  --bmc1_out_stat                         full
% 3.21/0.99  --bmc1_ground_init                      false
% 3.21/0.99  --bmc1_pre_inst_next_state              false
% 3.21/0.99  --bmc1_pre_inst_state                   false
% 3.21/0.99  --bmc1_pre_inst_reach_state             false
% 3.21/0.99  --bmc1_out_unsat_core                   false
% 3.21/0.99  --bmc1_aig_witness_out                  false
% 3.21/0.99  --bmc1_verbose                          false
% 3.21/0.99  --bmc1_dump_clauses_tptp                false
% 3.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.21/0.99  --bmc1_dump_file                        -
% 3.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.21/0.99  --bmc1_ucm_extend_mode                  1
% 3.21/0.99  --bmc1_ucm_init_mode                    2
% 3.21/0.99  --bmc1_ucm_cone_mode                    none
% 3.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.21/0.99  --bmc1_ucm_relax_model                  4
% 3.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/0.99  --bmc1_ucm_layered_model                none
% 3.21/0.99  --bmc1_ucm_max_lemma_size               10
% 3.21/0.99  
% 3.21/0.99  ------ AIG Options
% 3.21/0.99  
% 3.21/0.99  --aig_mode                              false
% 3.21/0.99  
% 3.21/0.99  ------ Instantiation Options
% 3.21/0.99  
% 3.21/0.99  --instantiation_flag                    true
% 3.21/0.99  --inst_sos_flag                         false
% 3.21/0.99  --inst_sos_phase                        true
% 3.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel_side                     num_symb
% 3.21/0.99  --inst_solver_per_active                1400
% 3.21/0.99  --inst_solver_calls_frac                1.
% 3.21/0.99  --inst_passive_queue_type               priority_queues
% 3.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/0.99  --inst_passive_queues_freq              [25;2]
% 3.21/0.99  --inst_dismatching                      true
% 3.21/0.99  --inst_eager_unprocessed_to_passive     true
% 3.21/0.99  --inst_prop_sim_given                   true
% 3.21/0.99  --inst_prop_sim_new                     false
% 3.21/0.99  --inst_subs_new                         false
% 3.21/0.99  --inst_eq_res_simp                      false
% 3.21/0.99  --inst_subs_given                       false
% 3.21/0.99  --inst_orphan_elimination               true
% 3.21/0.99  --inst_learning_loop_flag               true
% 3.21/0.99  --inst_learning_start                   3000
% 3.21/0.99  --inst_learning_factor                  2
% 3.21/0.99  --inst_start_prop_sim_after_learn       3
% 3.21/0.99  --inst_sel_renew                        solver
% 3.21/0.99  --inst_lit_activity_flag                true
% 3.21/0.99  --inst_restr_to_given                   false
% 3.21/0.99  --inst_activity_threshold               500
% 3.21/0.99  --inst_out_proof                        true
% 3.21/0.99  
% 3.21/0.99  ------ Resolution Options
% 3.21/0.99  
% 3.21/0.99  --resolution_flag                       true
% 3.21/0.99  --res_lit_sel                           adaptive
% 3.21/0.99  --res_lit_sel_side                      none
% 3.21/0.99  --res_ordering                          kbo
% 3.21/0.99  --res_to_prop_solver                    active
% 3.21/0.99  --res_prop_simpl_new                    false
% 3.21/0.99  --res_prop_simpl_given                  true
% 3.21/0.99  --res_passive_queue_type                priority_queues
% 3.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/0.99  --res_passive_queues_freq               [15;5]
% 3.21/0.99  --res_forward_subs                      full
% 3.21/0.99  --res_backward_subs                     full
% 3.21/0.99  --res_forward_subs_resolution           true
% 3.21/0.99  --res_backward_subs_resolution          true
% 3.21/0.99  --res_orphan_elimination                true
% 3.21/0.99  --res_time_limit                        2.
% 3.21/0.99  --res_out_proof                         true
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Options
% 3.21/0.99  
% 3.21/0.99  --superposition_flag                    true
% 3.21/0.99  --sup_passive_queue_type                priority_queues
% 3.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.21/0.99  --demod_completeness_check              fast
% 3.21/0.99  --demod_use_ground                      true
% 3.21/0.99  --sup_to_prop_solver                    passive
% 3.21/0.99  --sup_prop_simpl_new                    true
% 3.21/0.99  --sup_prop_simpl_given                  true
% 3.21/0.99  --sup_fun_splitting                     false
% 3.21/0.99  --sup_smt_interval                      50000
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Simplification Setup
% 3.21/0.99  
% 3.21/0.99  --sup_indices_passive                   []
% 3.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_full_bw                           [BwDemod]
% 3.21/0.99  --sup_immed_triv                        [TrivRules]
% 3.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_immed_bw_main                     []
% 3.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  
% 3.21/0.99  ------ Combination Options
% 3.21/0.99  
% 3.21/0.99  --comb_res_mult                         3
% 3.21/0.99  --comb_sup_mult                         2
% 3.21/0.99  --comb_inst_mult                        10
% 3.21/0.99  
% 3.21/0.99  ------ Debug Options
% 3.21/0.99  
% 3.21/0.99  --dbg_backtrace                         false
% 3.21/0.99  --dbg_dump_prop_clauses                 false
% 3.21/0.99  --dbg_dump_prop_clauses_file            -
% 3.21/0.99  --dbg_out_stat                          false
% 3.21/0.99  ------ Parsing...
% 3.21/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/0.99  ------ Proving...
% 3.21/0.99  ------ Problem Properties 
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  clauses                                 27
% 3.21/0.99  conjectures                             8
% 3.21/0.99  EPR                                     4
% 3.21/0.99  Horn                                    26
% 3.21/0.99  unary                                   15
% 3.21/0.99  binary                                  5
% 3.21/0.99  lits                                    65
% 3.21/0.99  lits eq                                 21
% 3.21/0.99  fd_pure                                 0
% 3.21/0.99  fd_pseudo                               0
% 3.21/0.99  fd_cond                                 2
% 3.21/0.99  fd_pseudo_cond                          4
% 3.21/0.99  AC symbols                              0
% 3.21/0.99  
% 3.21/0.99  ------ Schedule dynamic 5 is on 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  ------ 
% 3.21/0.99  Current options:
% 3.21/0.99  ------ 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options
% 3.21/0.99  
% 3.21/0.99  --out_options                           all
% 3.21/0.99  --tptp_safe_out                         true
% 3.21/0.99  --problem_path                          ""
% 3.21/0.99  --include_path                          ""
% 3.21/0.99  --clausifier                            res/vclausify_rel
% 3.21/0.99  --clausifier_options                    --mode clausify
% 3.21/0.99  --stdin                                 false
% 3.21/0.99  --stats_out                             all
% 3.21/0.99  
% 3.21/0.99  ------ General Options
% 3.21/0.99  
% 3.21/0.99  --fof                                   false
% 3.21/0.99  --time_out_real                         305.
% 3.21/0.99  --time_out_virtual                      -1.
% 3.21/0.99  --symbol_type_check                     false
% 3.21/0.99  --clausify_out                          false
% 3.21/0.99  --sig_cnt_out                           false
% 3.21/0.99  --trig_cnt_out                          false
% 3.21/0.99  --trig_cnt_out_tolerance                1.
% 3.21/0.99  --trig_cnt_out_sk_spl                   false
% 3.21/0.99  --abstr_cl_out                          false
% 3.21/0.99  
% 3.21/0.99  ------ Global Options
% 3.21/0.99  
% 3.21/0.99  --schedule                              default
% 3.21/0.99  --add_important_lit                     false
% 3.21/0.99  --prop_solver_per_cl                    1000
% 3.21/0.99  --min_unsat_core                        false
% 3.21/0.99  --soft_assumptions                      false
% 3.21/0.99  --soft_lemma_size                       3
% 3.21/0.99  --prop_impl_unit_size                   0
% 3.21/0.99  --prop_impl_unit                        []
% 3.21/0.99  --share_sel_clauses                     true
% 3.21/0.99  --reset_solvers                         false
% 3.21/0.99  --bc_imp_inh                            [conj_cone]
% 3.21/0.99  --conj_cone_tolerance                   3.
% 3.21/0.99  --extra_neg_conj                        none
% 3.21/0.99  --large_theory_mode                     true
% 3.21/0.99  --prolific_symb_bound                   200
% 3.21/0.99  --lt_threshold                          2000
% 3.21/0.99  --clause_weak_htbl                      true
% 3.21/0.99  --gc_record_bc_elim                     false
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing Options
% 3.21/0.99  
% 3.21/0.99  --preprocessing_flag                    true
% 3.21/0.99  --time_out_prep_mult                    0.1
% 3.21/0.99  --splitting_mode                        input
% 3.21/0.99  --splitting_grd                         true
% 3.21/0.99  --splitting_cvd                         false
% 3.21/0.99  --splitting_cvd_svl                     false
% 3.21/0.99  --splitting_nvd                         32
% 3.21/0.99  --sub_typing                            true
% 3.21/0.99  --prep_gs_sim                           true
% 3.21/0.99  --prep_unflatten                        true
% 3.21/0.99  --prep_res_sim                          true
% 3.21/0.99  --prep_upred                            true
% 3.21/0.99  --prep_sem_filter                       exhaustive
% 3.21/0.99  --prep_sem_filter_out                   false
% 3.21/0.99  --pred_elim                             true
% 3.21/0.99  --res_sim_input                         true
% 3.21/0.99  --eq_ax_congr_red                       true
% 3.21/0.99  --pure_diseq_elim                       true
% 3.21/0.99  --brand_transform                       false
% 3.21/0.99  --non_eq_to_eq                          false
% 3.21/0.99  --prep_def_merge                        true
% 3.21/0.99  --prep_def_merge_prop_impl              false
% 3.21/0.99  --prep_def_merge_mbd                    true
% 3.21/0.99  --prep_def_merge_tr_red                 false
% 3.21/0.99  --prep_def_merge_tr_cl                  false
% 3.21/0.99  --smt_preprocessing                     true
% 3.21/0.99  --smt_ac_axioms                         fast
% 3.21/0.99  --preprocessed_out                      false
% 3.21/0.99  --preprocessed_stats                    false
% 3.21/0.99  
% 3.21/0.99  ------ Abstraction refinement Options
% 3.21/0.99  
% 3.21/0.99  --abstr_ref                             []
% 3.21/0.99  --abstr_ref_prep                        false
% 3.21/0.99  --abstr_ref_until_sat                   false
% 3.21/0.99  --abstr_ref_sig_restrict                funpre
% 3.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/0.99  --abstr_ref_under                       []
% 3.21/0.99  
% 3.21/0.99  ------ SAT Options
% 3.21/0.99  
% 3.21/0.99  --sat_mode                              false
% 3.21/0.99  --sat_fm_restart_options                ""
% 3.21/0.99  --sat_gr_def                            false
% 3.21/0.99  --sat_epr_types                         true
% 3.21/0.99  --sat_non_cyclic_types                  false
% 3.21/0.99  --sat_finite_models                     false
% 3.21/0.99  --sat_fm_lemmas                         false
% 3.21/0.99  --sat_fm_prep                           false
% 3.21/0.99  --sat_fm_uc_incr                        true
% 3.21/0.99  --sat_out_model                         small
% 3.21/0.99  --sat_out_clauses                       false
% 3.21/0.99  
% 3.21/0.99  ------ QBF Options
% 3.21/0.99  
% 3.21/0.99  --qbf_mode                              false
% 3.21/0.99  --qbf_elim_univ                         false
% 3.21/0.99  --qbf_dom_inst                          none
% 3.21/0.99  --qbf_dom_pre_inst                      false
% 3.21/0.99  --qbf_sk_in                             false
% 3.21/0.99  --qbf_pred_elim                         true
% 3.21/0.99  --qbf_split                             512
% 3.21/0.99  
% 3.21/0.99  ------ BMC1 Options
% 3.21/0.99  
% 3.21/0.99  --bmc1_incremental                      false
% 3.21/0.99  --bmc1_axioms                           reachable_all
% 3.21/0.99  --bmc1_min_bound                        0
% 3.21/0.99  --bmc1_max_bound                        -1
% 3.21/0.99  --bmc1_max_bound_default                -1
% 3.21/0.99  --bmc1_symbol_reachability              true
% 3.21/0.99  --bmc1_property_lemmas                  false
% 3.21/0.99  --bmc1_k_induction                      false
% 3.21/0.99  --bmc1_non_equiv_states                 false
% 3.21/0.99  --bmc1_deadlock                         false
% 3.21/0.99  --bmc1_ucm                              false
% 3.21/0.99  --bmc1_add_unsat_core                   none
% 3.21/0.99  --bmc1_unsat_core_children              false
% 3.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/0.99  --bmc1_out_stat                         full
% 3.21/0.99  --bmc1_ground_init                      false
% 3.21/0.99  --bmc1_pre_inst_next_state              false
% 3.21/0.99  --bmc1_pre_inst_state                   false
% 3.21/0.99  --bmc1_pre_inst_reach_state             false
% 3.21/0.99  --bmc1_out_unsat_core                   false
% 3.21/0.99  --bmc1_aig_witness_out                  false
% 3.21/0.99  --bmc1_verbose                          false
% 3.21/0.99  --bmc1_dump_clauses_tptp                false
% 3.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.21/0.99  --bmc1_dump_file                        -
% 3.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.21/0.99  --bmc1_ucm_extend_mode                  1
% 3.21/0.99  --bmc1_ucm_init_mode                    2
% 3.21/0.99  --bmc1_ucm_cone_mode                    none
% 3.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.21/0.99  --bmc1_ucm_relax_model                  4
% 3.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/0.99  --bmc1_ucm_layered_model                none
% 3.21/0.99  --bmc1_ucm_max_lemma_size               10
% 3.21/0.99  
% 3.21/0.99  ------ AIG Options
% 3.21/0.99  
% 3.21/0.99  --aig_mode                              false
% 3.21/0.99  
% 3.21/0.99  ------ Instantiation Options
% 3.21/0.99  
% 3.21/0.99  --instantiation_flag                    true
% 3.21/0.99  --inst_sos_flag                         false
% 3.21/0.99  --inst_sos_phase                        true
% 3.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel_side                     none
% 3.21/0.99  --inst_solver_per_active                1400
% 3.21/0.99  --inst_solver_calls_frac                1.
% 3.21/0.99  --inst_passive_queue_type               priority_queues
% 3.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/0.99  --inst_passive_queues_freq              [25;2]
% 3.21/0.99  --inst_dismatching                      true
% 3.21/0.99  --inst_eager_unprocessed_to_passive     true
% 3.21/0.99  --inst_prop_sim_given                   true
% 3.21/0.99  --inst_prop_sim_new                     false
% 3.21/0.99  --inst_subs_new                         false
% 3.21/0.99  --inst_eq_res_simp                      false
% 3.21/0.99  --inst_subs_given                       false
% 3.21/0.99  --inst_orphan_elimination               true
% 3.21/0.99  --inst_learning_loop_flag               true
% 3.21/0.99  --inst_learning_start                   3000
% 3.21/0.99  --inst_learning_factor                  2
% 3.21/0.99  --inst_start_prop_sim_after_learn       3
% 3.21/0.99  --inst_sel_renew                        solver
% 3.21/0.99  --inst_lit_activity_flag                true
% 3.21/0.99  --inst_restr_to_given                   false
% 3.21/0.99  --inst_activity_threshold               500
% 3.21/0.99  --inst_out_proof                        true
% 3.21/0.99  
% 3.21/0.99  ------ Resolution Options
% 3.21/0.99  
% 3.21/0.99  --resolution_flag                       false
% 3.21/0.99  --res_lit_sel                           adaptive
% 3.21/0.99  --res_lit_sel_side                      none
% 3.21/0.99  --res_ordering                          kbo
% 3.21/0.99  --res_to_prop_solver                    active
% 3.21/0.99  --res_prop_simpl_new                    false
% 3.21/0.99  --res_prop_simpl_given                  true
% 3.21/0.99  --res_passive_queue_type                priority_queues
% 3.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/0.99  --res_passive_queues_freq               [15;5]
% 3.21/0.99  --res_forward_subs                      full
% 3.21/0.99  --res_backward_subs                     full
% 3.21/0.99  --res_forward_subs_resolution           true
% 3.21/0.99  --res_backward_subs_resolution          true
% 3.21/0.99  --res_orphan_elimination                true
% 3.21/0.99  --res_time_limit                        2.
% 3.21/0.99  --res_out_proof                         true
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Options
% 3.21/0.99  
% 3.21/0.99  --superposition_flag                    true
% 3.21/0.99  --sup_passive_queue_type                priority_queues
% 3.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.21/0.99  --demod_completeness_check              fast
% 3.21/0.99  --demod_use_ground                      true
% 3.21/0.99  --sup_to_prop_solver                    passive
% 3.21/0.99  --sup_prop_simpl_new                    true
% 3.21/0.99  --sup_prop_simpl_given                  true
% 3.21/0.99  --sup_fun_splitting                     false
% 3.21/0.99  --sup_smt_interval                      50000
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Simplification Setup
% 3.21/0.99  
% 3.21/0.99  --sup_indices_passive                   []
% 3.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_full_bw                           [BwDemod]
% 3.21/0.99  --sup_immed_triv                        [TrivRules]
% 3.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_immed_bw_main                     []
% 3.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  
% 3.21/0.99  ------ Combination Options
% 3.21/0.99  
% 3.21/0.99  --comb_res_mult                         3
% 3.21/0.99  --comb_sup_mult                         2
% 3.21/0.99  --comb_inst_mult                        10
% 3.21/0.99  
% 3.21/0.99  ------ Debug Options
% 3.21/0.99  
% 3.21/0.99  --dbg_backtrace                         false
% 3.21/0.99  --dbg_dump_prop_clauses                 false
% 3.21/0.99  --dbg_dump_prop_clauses_file            -
% 3.21/0.99  --dbg_out_stat                          false
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  ------ Proving...
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  % SZS status Theorem for theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  fof(f4,axiom,(
% 3.21/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f56,plain,(
% 3.21/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.21/0.99    inference(cnf_transformation,[],[f4])).
% 3.21/0.99  
% 3.21/0.99  fof(f16,axiom,(
% 3.21/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f74,plain,(
% 3.21/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f16])).
% 3.21/0.99  
% 3.21/0.99  fof(f89,plain,(
% 3.21/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.21/0.99    inference(definition_unfolding,[],[f56,f74])).
% 3.21/0.99  
% 3.21/0.99  fof(f3,axiom,(
% 3.21/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f24,plain,(
% 3.21/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.21/0.99    inference(ennf_transformation,[],[f3])).
% 3.21/0.99  
% 3.21/0.99  fof(f25,plain,(
% 3.21/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.21/0.99    inference(flattening,[],[f24])).
% 3.21/0.99  
% 3.21/0.99  fof(f54,plain,(
% 3.21/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f25])).
% 3.21/0.99  
% 3.21/0.99  fof(f6,axiom,(
% 3.21/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f59,plain,(
% 3.21/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f6])).
% 3.21/0.99  
% 3.21/0.99  fof(f92,plain,(
% 3.21/0.99    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.21/0.99    inference(definition_unfolding,[],[f59,f74])).
% 3.21/0.99  
% 3.21/0.99  fof(f5,axiom,(
% 3.21/0.99    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f26,plain,(
% 3.21/0.99    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.21/0.99    inference(ennf_transformation,[],[f5])).
% 3.21/0.99  
% 3.21/0.99  fof(f58,plain,(
% 3.21/0.99    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f26])).
% 3.21/0.99  
% 3.21/0.99  fof(f90,plain,(
% 3.21/0.99    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(definition_unfolding,[],[f58,f74])).
% 3.21/0.99  
% 3.21/0.99  fof(f57,plain,(
% 3.21/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.21/0.99    inference(cnf_transformation,[],[f4])).
% 3.21/0.99  
% 3.21/0.99  fof(f88,plain,(
% 3.21/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.21/0.99    inference(definition_unfolding,[],[f57,f74])).
% 3.21/0.99  
% 3.21/0.99  fof(f8,axiom,(
% 3.21/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f29,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f8])).
% 3.21/0.99  
% 3.21/0.99  fof(f30,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.21/0.99    inference(flattening,[],[f29])).
% 3.21/0.99  
% 3.21/0.99  fof(f62,plain,(
% 3.21/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f30])).
% 3.21/0.99  
% 3.21/0.99  fof(f94,plain,(
% 3.21/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(definition_unfolding,[],[f62,f74])).
% 3.21/0.99  
% 3.21/0.99  fof(f7,axiom,(
% 3.21/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f27,plain,(
% 3.21/0.99    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f7])).
% 3.21/0.99  
% 3.21/0.99  fof(f28,plain,(
% 3.21/0.99    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.21/0.99    inference(flattening,[],[f27])).
% 3.21/0.99  
% 3.21/0.99  fof(f61,plain,(
% 3.21/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f28])).
% 3.21/0.99  
% 3.21/0.99  fof(f93,plain,(
% 3.21/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(definition_unfolding,[],[f61,f74])).
% 3.21/0.99  
% 3.21/0.99  fof(f19,conjecture,(
% 3.21/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f20,negated_conjecture,(
% 3.21/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.21/0.99    inference(negated_conjecture,[],[f19])).
% 3.21/0.99  
% 3.21/0.99  fof(f45,plain,(
% 3.21/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.21/0.99    inference(ennf_transformation,[],[f20])).
% 3.21/0.99  
% 3.21/0.99  fof(f46,plain,(
% 3.21/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.21/0.99    inference(flattening,[],[f45])).
% 3.21/0.99  
% 3.21/0.99  fof(f50,plain,(
% 3.21/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f49,plain,(
% 3.21/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f51,plain,(
% 3.21/0.99    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f50,f49])).
% 3.21/0.99  
% 3.21/0.99  fof(f86,plain,(
% 3.21/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f81,plain,(
% 3.21/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f1,axiom,(
% 3.21/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f23,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.21/0.99    inference(ennf_transformation,[],[f1])).
% 3.21/0.99  
% 3.21/0.99  fof(f52,plain,(
% 3.21/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f23])).
% 3.21/0.99  
% 3.21/0.99  fof(f2,axiom,(
% 3.21/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f53,plain,(
% 3.21/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f2])).
% 3.21/0.99  
% 3.21/0.99  fof(f9,axiom,(
% 3.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f22,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.21/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.21/0.99  
% 3.21/0.99  fof(f31,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(ennf_transformation,[],[f22])).
% 3.21/0.99  
% 3.21/0.99  fof(f63,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f31])).
% 3.21/0.99  
% 3.21/0.99  fof(f13,axiom,(
% 3.21/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f37,plain,(
% 3.21/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.21/0.99    inference(ennf_transformation,[],[f13])).
% 3.21/0.99  
% 3.21/0.99  fof(f38,plain,(
% 3.21/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.21/0.99    inference(flattening,[],[f37])).
% 3.21/0.99  
% 3.21/0.99  fof(f48,plain,(
% 3.21/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.21/0.99    inference(nnf_transformation,[],[f38])).
% 3.21/0.99  
% 3.21/0.99  fof(f70,plain,(
% 3.21/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f48])).
% 3.21/0.99  
% 3.21/0.99  fof(f12,axiom,(
% 3.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f35,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(ennf_transformation,[],[f12])).
% 3.21/0.99  
% 3.21/0.99  fof(f36,plain,(
% 3.21/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(flattening,[],[f35])).
% 3.21/0.99  
% 3.21/0.99  fof(f69,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f36])).
% 3.21/0.99  
% 3.21/0.99  fof(f80,plain,(
% 3.21/0.99    v3_funct_2(sK1,sK0,sK0)),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f78,plain,(
% 3.21/0.99    v1_funct_1(sK1)),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f10,axiom,(
% 3.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f32,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(ennf_transformation,[],[f10])).
% 3.21/0.99  
% 3.21/0.99  fof(f64,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f32])).
% 3.21/0.99  
% 3.21/0.99  fof(f18,axiom,(
% 3.21/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f43,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.21/0.99    inference(ennf_transformation,[],[f18])).
% 3.21/0.99  
% 3.21/0.99  fof(f44,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.21/0.99    inference(flattening,[],[f43])).
% 3.21/0.99  
% 3.21/0.99  fof(f77,plain,(
% 3.21/0.99    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f44])).
% 3.21/0.99  
% 3.21/0.99  fof(f17,axiom,(
% 3.21/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f41,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.21/0.99    inference(ennf_transformation,[],[f17])).
% 3.21/0.99  
% 3.21/0.99  fof(f42,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.21/0.99    inference(flattening,[],[f41])).
% 3.21/0.99  
% 3.21/0.99  fof(f75,plain,(
% 3.21/0.99    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f42])).
% 3.21/0.99  
% 3.21/0.99  fof(f79,plain,(
% 3.21/0.99    v1_funct_2(sK1,sK0,sK0)),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f82,plain,(
% 3.21/0.99    v1_funct_1(sK2)),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f83,plain,(
% 3.21/0.99    v1_funct_2(sK2,sK0,sK0)),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f85,plain,(
% 3.21/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f87,plain,(
% 3.21/0.99    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f15,axiom,(
% 3.21/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f39,plain,(
% 3.21/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.21/0.99    inference(ennf_transformation,[],[f15])).
% 3.21/0.99  
% 3.21/0.99  fof(f40,plain,(
% 3.21/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.21/0.99    inference(flattening,[],[f39])).
% 3.21/0.99  
% 3.21/0.99  fof(f73,plain,(
% 3.21/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f40])).
% 3.21/0.99  
% 3.21/0.99  fof(f11,axiom,(
% 3.21/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f33,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.21/0.99    inference(ennf_transformation,[],[f11])).
% 3.21/0.99  
% 3.21/0.99  fof(f34,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(flattening,[],[f33])).
% 3.21/0.99  
% 3.21/0.99  fof(f47,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(nnf_transformation,[],[f34])).
% 3.21/0.99  
% 3.21/0.99  fof(f66,plain,(
% 3.21/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f47])).
% 3.21/0.99  
% 3.21/0.99  fof(f95,plain,(
% 3.21/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(equality_resolution,[],[f66])).
% 3.21/0.99  
% 3.21/0.99  fof(f84,plain,(
% 3.21/0.99    v3_funct_2(sK2,sK0,sK0)),
% 3.21/0.99    inference(cnf_transformation,[],[f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f55,plain,(
% 3.21/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f25])).
% 3.21/0.99  
% 3.21/0.99  fof(f14,axiom,(
% 3.21/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f21,plain,(
% 3.21/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.21/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.21/0.99  
% 3.21/0.99  fof(f72,plain,(
% 3.21/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f21])).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5,plain,
% 3.21/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.21/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3,plain,
% 3.21/0.99      ( ~ v1_relat_1(X0)
% 3.21/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.21/0.99      | k1_xboole_0 = X0 ),
% 3.21/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1614,plain,
% 3.21/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.21/0.99      | k1_xboole_0 = X0
% 3.21/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3084,plain,
% 3.21/0.99      ( k6_partfun1(X0) = k1_xboole_0
% 3.21/0.99      | k1_xboole_0 != X0
% 3.21/0.99      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_5,c_1614]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_8,plain,
% 3.21/0.99      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_91,plain,
% 3.21/0.99      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3129,plain,
% 3.21/0.99      ( k1_xboole_0 != X0 | k6_partfun1(X0) = k1_xboole_0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_3084,c_91]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3130,plain,
% 3.21/0.99      ( k6_partfun1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.21/0.99      inference(renaming,[status(thm)],[c_3129]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3134,plain,
% 3.21/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.21/0.99      inference(equality_resolution,[status(thm)],[c_3130]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1612,plain,
% 3.21/0.99      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6,plain,
% 3.21/0.99      ( ~ v1_relat_1(X0)
% 3.21/0.99      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 3.21/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1613,plain,
% 3.21/0.99      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 3.21/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2845,plain,
% 3.21/0.99      ( k5_relat_1(k6_partfun1(X0),k6_partfun1(k2_relat_1(k6_partfun1(X0)))) = k6_partfun1(X0) ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1612,c_1613]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4,plain,
% 3.21/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.21/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2847,plain,
% 3.21/0.99      ( k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_2845,c_4]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_10,plain,
% 3.21/0.99      ( ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_funct_1(X1)
% 3.21/0.99      | ~ v2_funct_1(X1)
% 3.21/0.99      | ~ v1_relat_1(X1)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.21/0.99      | k2_funct_1(X1) = X0
% 3.21/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.21/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_9,plain,
% 3.21/0.99      ( ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_funct_1(X1)
% 3.21/0.99      | v2_funct_1(X1)
% 3.21/0.99      | ~ v1_relat_1(X1)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_208,plain,
% 3.21/0.99      ( ~ v1_funct_1(X1)
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_relat_1(X1)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.21/0.99      | k2_funct_1(X1) = X0
% 3.21/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_10,c_9]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_209,plain,
% 3.21/0.99      ( ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_funct_1(X1)
% 3.21/0.99      | ~ v1_relat_1(X1)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.21/0.99      | k2_funct_1(X1) = X0
% 3.21/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.21/0.99      inference(renaming,[status(thm)],[c_208]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1598,plain,
% 3.21/0.99      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.21/0.99      | k2_funct_1(X0) = X1
% 3.21/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.21/0.99      | v1_funct_1(X1) != iProver_top
% 3.21/0.99      | v1_funct_1(X0) != iProver_top
% 3.21/0.99      | v1_relat_1(X1) != iProver_top
% 3.21/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3909,plain,
% 3.21/0.99      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
% 3.21/0.99      | k6_partfun1(k1_relat_1(k6_partfun1(X0))) != k6_partfun1(X0)
% 3.21/0.99      | k1_relat_1(k6_partfun1(X0)) != k2_relat_1(k6_partfun1(X0))
% 3.21/0.99      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 3.21/0.99      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_2847,c_1598]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3915,plain,
% 3.21/0.99      ( X0 != X0
% 3.21/0.99      | k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
% 3.21/0.99      | k6_partfun1(X0) != k6_partfun1(X0)
% 3.21/0.99      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 3.21/0.99      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_3909,c_4,c_5]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3916,plain,
% 3.21/0.99      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
% 3.21/0.99      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 3.21/0.99      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.21/0.99      inference(equality_resolution_simp,[status(thm)],[c_3915]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5568,plain,
% 3.21/0.99      ( v1_funct_1(k6_partfun1(X0)) != iProver_top
% 3.21/0.99      | k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_3916,c_91]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5569,plain,
% 3.21/0.99      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
% 3.21/0.99      | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
% 3.21/0.99      inference(renaming,[status(thm)],[c_5568]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5576,plain,
% 3.21/0.99      ( k2_funct_1(k6_partfun1(k1_xboole_0)) = k6_partfun1(k1_xboole_0)
% 3.21/0.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3134,c_5569]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5577,plain,
% 3.21/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 3.21/0.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_5576,c_3134]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_26,negated_conjecture,
% 3.21/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1606,plain,
% 3.21/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_31,negated_conjecture,
% 3.21/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.21/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1602,plain,
% 3.21/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_0,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/0.99      | ~ v1_relat_1(X1)
% 3.21/0.99      | v1_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1617,plain,
% 3.21/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.21/0.99      | v1_relat_1(X1) != iProver_top
% 3.21/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4050,plain,
% 3.21/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.21/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1602,c_1617]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_38,plain,
% 3.21/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1,plain,
% 3.21/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_108,plain,
% 3.21/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_110,plain,
% 3.21/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_108]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1804,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | v1_relat_1(X0)
% 3.21/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2440,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.21/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.21/0.99      | v1_relat_1(sK1) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_1804]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2441,plain,
% 3.21/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.21/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.21/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_2440]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4206,plain,
% 3.21/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_4050,c_38,c_110,c_2441]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_11,plain,
% 3.21/0.99      ( v5_relat_1(X0,X1)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.21/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_19,plain,
% 3.21/0.99      ( ~ v2_funct_2(X0,X1)
% 3.21/0.99      | ~ v5_relat_1(X0,X1)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k2_relat_1(X0) = X1 ),
% 3.21/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_15,plain,
% 3.21/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.21/0.99      | v2_funct_2(X0,X2)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | ~ v1_funct_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_32,negated_conjecture,
% 3.21/0.99      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_420,plain,
% 3.21/0.99      ( v2_funct_2(X0,X1)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | sK1 != X0
% 3.21/0.99      | sK0 != X1
% 3.21/0.99      | sK0 != X2 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_421,plain,
% 3.21/0.99      ( v2_funct_2(sK1,sK0)
% 3.21/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.21/0.99      | ~ v1_funct_1(sK1) ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_34,negated_conjecture,
% 3.21/0.99      ( v1_funct_1(sK1) ),
% 3.21/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_423,plain,
% 3.21/0.99      ( v2_funct_2(sK1,sK0) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_421,c_34,c_31]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_506,plain,
% 3.21/0.99      ( ~ v5_relat_1(X0,X1)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k2_relat_1(X0) = X1
% 3.21/0.99      | sK1 != X0
% 3.21/0.99      | sK0 != X1 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_423]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_507,plain,
% 3.21/0.99      ( ~ v5_relat_1(sK1,sK0)
% 3.21/0.99      | ~ v1_relat_1(sK1)
% 3.21/0.99      | k2_relat_1(sK1) = sK0 ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_506]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_553,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | ~ v1_relat_1(sK1)
% 3.21/0.99      | k2_relat_1(sK1) = sK0
% 3.21/0.99      | sK1 != X0
% 3.21/0.99      | sK0 != X2 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_507]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_554,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.21/0.99      | ~ v1_relat_1(sK1)
% 3.21/0.99      | k2_relat_1(sK1) = sK0 ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_553]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_556,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.21/0.99      | ~ v1_relat_1(sK1)
% 3.21/0.99      | k2_relat_1(sK1) = sK0 ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_554]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_558,plain,
% 3.21/0.99      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_554,c_31,c_556]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1595,plain,
% 3.21/0.99      ( k2_relat_1(sK1) = sK0 | v1_relat_1(sK1) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4212,plain,
% 3.21/0.99      ( k2_relat_1(sK1) = sK0 ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_4206,c_1595]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_12,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1611,plain,
% 3.21/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.21/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3162,plain,
% 3.21/0.99      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1602,c_1611]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4344,plain,
% 3.21/0.99      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_4212,c_3162]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_24,plain,
% 3.21/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.21/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.21/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.21/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.21/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.21/0.99      | ~ v1_funct_1(X2)
% 3.21/0.99      | ~ v1_funct_1(X3)
% 3.21/0.99      | ~ v2_funct_1(X2)
% 3.21/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.21/0.99      | k2_funct_1(X2) = X3
% 3.21/0.99      | k1_xboole_0 = X0
% 3.21/0.99      | k1_xboole_0 = X1 ),
% 3.21/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_23,plain,
% 3.21/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.21/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.21/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.21/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.21/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.21/0.99      | ~ v1_funct_1(X2)
% 3.21/0.99      | ~ v1_funct_1(X3)
% 3.21/0.99      | v2_funct_1(X2) ),
% 3.21/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_189,plain,
% 3.21/0.99      ( ~ v1_funct_1(X3)
% 3.21/0.99      | ~ v1_funct_1(X2)
% 3.21/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.21/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.21/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.21/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.21/0.99      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.21/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.21/0.99      | k2_funct_1(X2) = X3
% 3.21/0.99      | k1_xboole_0 = X0
% 3.21/0.99      | k1_xboole_0 = X1 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_24,c_23]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_190,plain,
% 3.21/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.21/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.21/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.21/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.21/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.21/0.99      | ~ v1_funct_1(X2)
% 3.21/0.99      | ~ v1_funct_1(X3)
% 3.21/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.21/0.99      | k2_funct_1(X2) = X3
% 3.21/0.99      | k1_xboole_0 = X1
% 3.21/0.99      | k1_xboole_0 = X0 ),
% 3.21/0.99      inference(renaming,[status(thm)],[c_189]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1599,plain,
% 3.21/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.21/0.99      | k2_funct_1(X2) = X3
% 3.21/0.99      | k1_xboole_0 = X1
% 3.21/0.99      | k1_xboole_0 = X0
% 3.21/0.99      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.21/0.99      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.21/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.21/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.21/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.21/0.99      | v1_funct_1(X2) != iProver_top
% 3.21/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4404,plain,
% 3.21/0.99      ( k2_funct_1(sK1) = X0
% 3.21/0.99      | sK0 = k1_xboole_0
% 3.21/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.21/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.21/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.21/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.21/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.21/0.99      | v1_funct_1(X0) != iProver_top
% 3.21/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_4344,c_1599]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_35,plain,
% 3.21/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_33,negated_conjecture,
% 3.21/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_36,plain,
% 3.21/0.99      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5069,plain,
% 3.21/0.99      ( v1_funct_1(X0) != iProver_top
% 3.21/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.21/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.21/0.99      | sK0 = k1_xboole_0
% 3.21/0.99      | k2_funct_1(sK1) = X0
% 3.21/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_4404,c_35,c_36,c_38]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5070,plain,
% 3.21/0.99      ( k2_funct_1(sK1) = X0
% 3.21/0.99      | sK0 = k1_xboole_0
% 3.21/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.21/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.21/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.21/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.21/0.99      inference(renaming,[status(thm)],[c_5069]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5081,plain,
% 3.21/0.99      ( k2_funct_1(sK1) = sK2
% 3.21/0.99      | sK0 = k1_xboole_0
% 3.21/0.99      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.21/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.21/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1606,c_5070]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_30,negated_conjecture,
% 3.21/0.99      ( v1_funct_1(sK2) ),
% 3.21/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_29,negated_conjecture,
% 3.21/0.99      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_27,negated_conjecture,
% 3.21/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.21/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5082,plain,
% 3.21/0.99      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.21/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.21/0.99      | ~ v1_funct_1(sK2)
% 3.21/0.99      | k2_funct_1(sK1) = sK2
% 3.21/0.99      | sK0 = k1_xboole_0 ),
% 3.21/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5081]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5279,plain,
% 3.21/0.99      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_5081,c_39,c_40,c_42]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5280,plain,
% 3.21/0.99      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.21/0.99      inference(renaming,[status(thm)],[c_5279]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_25,negated_conjecture,
% 3.21/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1607,plain,
% 3.21/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_21,plain,
% 3.21/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.21/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_439,plain,
% 3.21/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.21/0.99      | sK1 != X0
% 3.21/0.99      | sK0 != X1 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_440,plain,
% 3.21/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.21/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.21/0.99      | ~ v1_funct_1(sK1)
% 3.21/0.99      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_439]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_442,plain,
% 3.21/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_440,c_34,c_33,c_31]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1652,plain,
% 3.21/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_1607,c_442]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5283,plain,
% 3.21/0.99      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_5280,c_1652]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_42,plain,
% 3.21/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_13,plain,
% 3.21/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.21/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.21/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1852,plain,
% 3.21/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.21/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1853,plain,
% 3.21/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.21/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1852]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6809,plain,
% 3.21/0.99      ( sK0 = k1_xboole_0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_5283,c_42,c_1853]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_28,negated_conjecture,
% 3.21/0.99      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_409,plain,
% 3.21/0.99      ( v2_funct_2(X0,X1)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | sK2 != X0
% 3.21/0.99      | sK0 != X1
% 3.21/0.99      | sK0 != X2 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_410,plain,
% 3.21/0.99      ( v2_funct_2(sK2,sK0)
% 3.21/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.21/0.99      | ~ v1_funct_1(sK2) ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_409]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_412,plain,
% 3.21/0.99      ( v2_funct_2(sK2,sK0) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_410,c_30,c_27]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_493,plain,
% 3.21/0.99      ( ~ v5_relat_1(X0,X1)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k2_relat_1(X0) = X1
% 3.21/0.99      | sK2 != X0
% 3.21/0.99      | sK0 != X1 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_412]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_494,plain,
% 3.21/0.99      ( ~ v5_relat_1(sK2,sK0)
% 3.21/0.99      | ~ v1_relat_1(sK2)
% 3.21/0.99      | k2_relat_1(sK2) = sK0 ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_493]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_537,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | ~ v1_relat_1(sK2)
% 3.21/0.99      | k2_relat_1(sK2) = sK0
% 3.21/0.99      | sK2 != X0
% 3.21/0.99      | sK0 != X2 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_494]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_538,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.21/0.99      | ~ v1_relat_1(sK2)
% 3.21/0.99      | k2_relat_1(sK2) = sK0 ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_537]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_540,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.21/0.99      | ~ v1_relat_1(sK2)
% 3.21/0.99      | k2_relat_1(sK2) = sK0 ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_538]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_542,plain,
% 3.21/0.99      ( ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_538,c_27,c_540]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1596,plain,
% 3.21/0.99      ( k2_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_109,plain,
% 3.21/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2437,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.21/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.21/0.99      | v1_relat_1(sK2) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_1804]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2838,plain,
% 3.21/0.99      ( k2_relat_1(sK2) = sK0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_1596,c_27,c_109,c_540,c_2437]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2,plain,
% 3.21/0.99      ( ~ v1_relat_1(X0)
% 3.21/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.21/0.99      | k1_xboole_0 = X0 ),
% 3.21/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1615,plain,
% 3.21/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.21/0.99      | k1_xboole_0 = X0
% 3.21/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3120,plain,
% 3.21/0.99      ( sK2 = k1_xboole_0
% 3.21/0.99      | sK0 != k1_xboole_0
% 3.21/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_2838,c_1615]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3127,plain,
% 3.21/0.99      ( ~ v1_relat_1(sK2) | sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.21/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3120]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3780,plain,
% 3.21/0.99      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_3120,c_27,c_109,c_2437,c_3127]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3781,plain,
% 3.21/0.99      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.21/0.99      inference(renaming,[status(thm)],[c_3780]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6827,plain,
% 3.21/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_6809,c_3781]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6865,plain,
% 3.21/0.99      ( sK2 = k1_xboole_0 ),
% 3.21/0.99      inference(equality_resolution_simp,[status(thm)],[c_6827]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1603,plain,
% 3.21/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_7759,plain,
% 3.21/0.99      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_6865,c_1603]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_8254,plain,
% 3.21/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_5577,c_7759]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4345,plain,
% 3.21/0.99      ( sK1 = k1_xboole_0
% 3.21/0.99      | sK0 != k1_xboole_0
% 3.21/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_4212,c_1615]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4993,plain,
% 3.21/0.99      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_4345,c_38,c_110,c_2441]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4994,plain,
% 3.21/0.99      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.21/0.99      inference(renaming,[status(thm)],[c_4993]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6816,plain,
% 3.21/0.99      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_6809,c_4994]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6923,plain,
% 3.21/0.99      ( sK1 = k1_xboole_0 ),
% 3.21/0.99      inference(equality_resolution_simp,[status(thm)],[c_6816]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6832,plain,
% 3.21/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_6809,c_1652]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6870,plain,
% 3.21/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_6865,c_6832]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6929,plain,
% 3.21/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_6923,c_6870]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_8257,plain,
% 3.21/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_8254,c_6929]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_20,plain,
% 3.21/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.21/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1608,plain,
% 3.21/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3788,plain,
% 3.21/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3134,c_1608]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1610,plain,
% 3.21/0.99      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.21/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4667,plain,
% 3.21/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3788,c_1610]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(contradiction,plain,
% 3.21/0.99      ( $false ),
% 3.21/0.99      inference(minisat,[status(thm)],[c_8257,c_4667]) ).
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  ------                               Statistics
% 3.21/0.99  
% 3.21/0.99  ------ General
% 3.21/0.99  
% 3.21/0.99  abstr_ref_over_cycles:                  0
% 3.21/0.99  abstr_ref_under_cycles:                 0
% 3.21/0.99  gc_basic_clause_elim:                   0
% 3.21/0.99  forced_gc_time:                         0
% 3.21/0.99  parsing_time:                           0.008
% 3.21/0.99  unif_index_cands_time:                  0.
% 3.21/0.99  unif_index_add_time:                    0.
% 3.21/0.99  orderings_time:                         0.
% 3.21/0.99  out_proof_time:                         0.014
% 3.21/0.99  total_time:                             0.289
% 3.21/0.99  num_of_symbols:                         54
% 3.21/0.99  num_of_terms:                           10452
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing
% 3.21/0.99  
% 3.21/0.99  num_of_splits:                          0
% 3.21/0.99  num_of_split_atoms:                     0
% 3.21/0.99  num_of_reused_defs:                     0
% 3.21/0.99  num_eq_ax_congr_red:                    15
% 3.21/0.99  num_of_sem_filtered_clauses:            5
% 3.21/0.99  num_of_subtypes:                        0
% 3.21/0.99  monotx_restored_types:                  0
% 3.21/0.99  sat_num_of_epr_types:                   0
% 3.21/0.99  sat_num_of_non_cyclic_types:            0
% 3.21/0.99  sat_guarded_non_collapsed_types:        0
% 3.21/0.99  num_pure_diseq_elim:                    0
% 3.21/0.99  simp_replaced_by:                       0
% 3.21/0.99  res_preprocessed:                       148
% 3.21/0.99  prep_upred:                             0
% 3.21/0.99  prep_unflattend:                        62
% 3.21/0.99  smt_new_axioms:                         0
% 3.21/0.99  pred_elim_cands:                        5
% 3.21/0.99  pred_elim:                              3
% 3.21/0.99  pred_elim_cl:                           3
% 3.21/0.99  pred_elim_cycles:                       6
% 3.21/0.99  merged_defs:                            0
% 3.21/0.99  merged_defs_ncl:                        0
% 3.21/0.99  bin_hyper_res:                          0
% 3.21/0.99  prep_cycles:                            4
% 3.21/0.99  pred_elim_time:                         0.009
% 3.21/0.99  splitting_time:                         0.
% 3.21/0.99  sem_filter_time:                        0.
% 3.21/0.99  monotx_time:                            0.
% 3.21/0.99  subtype_inf_time:                       0.
% 3.21/0.99  
% 3.21/0.99  ------ Problem properties
% 3.21/0.99  
% 3.21/0.99  clauses:                                27
% 3.21/0.99  conjectures:                            8
% 3.21/0.99  epr:                                    4
% 3.21/0.99  horn:                                   26
% 3.21/0.99  ground:                                 12
% 3.21/0.99  unary:                                  15
% 3.21/0.99  binary:                                 5
% 3.21/0.99  lits:                                   65
% 3.21/0.99  lits_eq:                                21
% 3.21/0.99  fd_pure:                                0
% 3.21/0.99  fd_pseudo:                              0
% 3.21/0.99  fd_cond:                                2
% 3.21/0.99  fd_pseudo_cond:                         4
% 3.21/0.99  ac_symbols:                             0
% 3.21/0.99  
% 3.21/0.99  ------ Propositional Solver
% 3.21/0.99  
% 3.21/0.99  prop_solver_calls:                      27
% 3.21/0.99  prop_fast_solver_calls:                 1211
% 3.21/0.99  smt_solver_calls:                       0
% 3.21/0.99  smt_fast_solver_calls:                  0
% 3.21/0.99  prop_num_of_clauses:                    3353
% 3.21/0.99  prop_preprocess_simplified:             9020
% 3.21/0.99  prop_fo_subsumed:                       42
% 3.21/0.99  prop_solver_time:                       0.
% 3.21/0.99  smt_solver_time:                        0.
% 3.21/0.99  smt_fast_solver_time:                   0.
% 3.21/0.99  prop_fast_solver_time:                  0.
% 3.21/0.99  prop_unsat_core_time:                   0.
% 3.21/0.99  
% 3.21/0.99  ------ QBF
% 3.21/0.99  
% 3.21/0.99  qbf_q_res:                              0
% 3.21/0.99  qbf_num_tautologies:                    0
% 3.21/0.99  qbf_prep_cycles:                        0
% 3.21/0.99  
% 3.21/0.99  ------ BMC1
% 3.21/0.99  
% 3.21/0.99  bmc1_current_bound:                     -1
% 3.21/0.99  bmc1_last_solved_bound:                 -1
% 3.21/0.99  bmc1_unsat_core_size:                   -1
% 3.21/0.99  bmc1_unsat_core_parents_size:           -1
% 3.21/0.99  bmc1_merge_next_fun:                    0
% 3.21/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.21/0.99  
% 3.21/0.99  ------ Instantiation
% 3.21/0.99  
% 3.21/0.99  inst_num_of_clauses:                    963
% 3.21/0.99  inst_num_in_passive:                    356
% 3.21/0.99  inst_num_in_active:                     377
% 3.21/0.99  inst_num_in_unprocessed:                230
% 3.21/0.99  inst_num_of_loops:                      390
% 3.21/0.99  inst_num_of_learning_restarts:          0
% 3.21/0.99  inst_num_moves_active_passive:          12
% 3.21/0.99  inst_lit_activity:                      0
% 3.21/0.99  inst_lit_activity_moves:                0
% 3.21/0.99  inst_num_tautologies:                   0
% 3.21/0.99  inst_num_prop_implied:                  0
% 3.21/0.99  inst_num_existing_simplified:           0
% 3.21/0.99  inst_num_eq_res_simplified:             0
% 3.21/0.99  inst_num_child_elim:                    0
% 3.21/0.99  inst_num_of_dismatching_blockings:      128
% 3.21/0.99  inst_num_of_non_proper_insts:           711
% 3.21/0.99  inst_num_of_duplicates:                 0
% 3.21/0.99  inst_inst_num_from_inst_to_res:         0
% 3.21/0.99  inst_dismatching_checking_time:         0.
% 3.21/0.99  
% 3.21/0.99  ------ Resolution
% 3.21/0.99  
% 3.21/0.99  res_num_of_clauses:                     0
% 3.21/0.99  res_num_in_passive:                     0
% 3.21/0.99  res_num_in_active:                      0
% 3.21/0.99  res_num_of_loops:                       152
% 3.21/0.99  res_forward_subset_subsumed:            28
% 3.21/0.99  res_backward_subset_subsumed:           0
% 3.21/0.99  res_forward_subsumed:                   0
% 3.21/0.99  res_backward_subsumed:                  0
% 3.21/0.99  res_forward_subsumption_resolution:     1
% 3.21/0.99  res_backward_subsumption_resolution:    0
% 3.21/0.99  res_clause_to_clause_subsumption:       187
% 3.21/0.99  res_orphan_elimination:                 0
% 3.21/0.99  res_tautology_del:                      33
% 3.21/0.99  res_num_eq_res_simplified:              0
% 3.21/0.99  res_num_sel_changes:                    0
% 3.21/0.99  res_moves_from_active_to_pass:          0
% 3.21/0.99  
% 3.21/0.99  ------ Superposition
% 3.21/0.99  
% 3.21/0.99  sup_time_total:                         0.
% 3.21/0.99  sup_time_generating:                    0.
% 3.21/0.99  sup_time_sim_full:                      0.
% 3.21/0.99  sup_time_sim_immed:                     0.
% 3.21/0.99  
% 3.21/0.99  sup_num_of_clauses:                     44
% 3.21/0.99  sup_num_in_active:                      40
% 3.21/0.99  sup_num_in_passive:                     4
% 3.21/0.99  sup_num_of_loops:                       77
% 3.21/0.99  sup_fw_superposition:                   42
% 3.21/0.99  sup_bw_superposition:                   24
% 3.21/0.99  sup_immediate_simplified:               57
% 3.21/0.99  sup_given_eliminated:                   0
% 3.21/0.99  comparisons_done:                       0
% 3.21/0.99  comparisons_avoided:                    3
% 3.21/0.99  
% 3.21/0.99  ------ Simplifications
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  sim_fw_subset_subsumed:                 8
% 3.21/0.99  sim_bw_subset_subsumed:                 3
% 3.21/0.99  sim_fw_subsumed:                        1
% 3.21/0.99  sim_bw_subsumed:                        0
% 3.21/0.99  sim_fw_subsumption_res:                 1
% 3.21/0.99  sim_bw_subsumption_res:                 0
% 3.21/0.99  sim_tautology_del:                      0
% 3.21/0.99  sim_eq_tautology_del:                   12
% 3.21/0.99  sim_eq_res_simp:                        9
% 3.21/0.99  sim_fw_demodulated:                     6
% 3.21/0.99  sim_bw_demodulated:                     54
% 3.21/0.99  sim_light_normalised:                   31
% 3.21/0.99  sim_joinable_taut:                      0
% 3.21/0.99  sim_joinable_simp:                      0
% 3.21/0.99  sim_ac_normalised:                      0
% 3.21/0.99  sim_smt_subsumption:                    0
% 3.21/0.99  
%------------------------------------------------------------------------------
