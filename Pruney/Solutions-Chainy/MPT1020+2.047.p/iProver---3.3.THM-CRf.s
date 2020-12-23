%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:14 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_43)

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

fof(f38,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f49,f48])).

fof(f89,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f37])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f94,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f66,f77,f77])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1890,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1886,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1896,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3390,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_1896])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_253,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_321,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_254])).

cnf(c_1882,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_3886,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3390,c_1882])).

cnf(c_42,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_89,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_91,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_2252,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2956,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_2957,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2956])).

cnf(c_2177,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_3109,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2177])).

cnf(c_3111,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3109])).

cnf(c_4098,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_42,c_91,c_2957,c_3111])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_441,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_442,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_444,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_38,c_35])).

cnf(c_527,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_444])).

cnf(c_528,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_528])).

cnf(c_592,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_594,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_596,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_35,c_594])).

cnf(c_1878,plain,
    ( k2_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_4103,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_4098,c_1878])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1894,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4645,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1886,c_1894])).

cnf(c_7624,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_4103,c_4645])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_27,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f78])).

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
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_27])).

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
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_1883,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_7715,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7624,c_1883])).

cnf(c_39,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_40,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9840,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7715,c_39,c_40,c_42])).

cnf(c_9841,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9840])).

cnf(c_9852,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1890,c_9841])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_9853,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9852])).

cnf(c_9855,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9852,c_43,c_44,c_46])).

cnf(c_9856,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9855])).

cnf(c_29,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1891,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_461,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_463,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_38,c_37,c_35])).

cnf(c_1940,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1891,c_463])).

cnf(c_9859,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9856,c_1940])).

cnf(c_46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2120,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2121,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2120])).

cnf(c_9912,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9859,c_46,c_2121])).

cnf(c_9938,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9912,c_1886])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_9952,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9938,c_4])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_10])).

cnf(c_1880,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_4169,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1880])).

cnf(c_10308,plain,
    ( r1_tarski(k2_relat_1(sK1),X0) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9952,c_4169])).

cnf(c_10877,plain,
    ( r1_tarski(k2_relat_1(sK1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10308,c_42,c_91,c_2957,c_3111])).

cnf(c_9926,plain,
    ( k2_relat_1(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9912,c_4103])).

cnf(c_10881,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10877,c_9926])).

cnf(c_1889,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3389,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_1896])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1899,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7407,plain,
    ( k2_zfmisc_1(sK0,sK0) = sK2
    | r1_tarski(k2_zfmisc_1(sK0,sK0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3389,c_1899])).

cnf(c_9930,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK2
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9912,c_7407])).

cnf(c_9974,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9930,c_4])).

cnf(c_10891,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10881,c_9974])).

cnf(c_9935,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9912,c_1940])).

cnf(c_11760,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10891,c_9935])).

cnf(c_14,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_15,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3116,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_3117,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3116,c_14])).

cnf(c_7408,plain,
    ( k2_zfmisc_1(sK0,sK0) = sK1
    | r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3390,c_1899])).

cnf(c_9929,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK1
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9912,c_7408])).

cnf(c_9979,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9929,c_4])).

cnf(c_10892,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10881,c_9979])).

cnf(c_11977,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11760,c_3117,c_10892])).

cnf(c_1893,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4202,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_1893])).

cnf(c_9932,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9912,c_4202])).

cnf(c_11761,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10891,c_9932])).

cnf(c_11979,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11977,c_11761])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.04/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/1.00  
% 4.04/1.00  ------  iProver source info
% 4.04/1.00  
% 4.04/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.04/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/1.00  git: non_committed_changes: false
% 4.04/1.00  git: last_make_outside_of_git: false
% 4.04/1.00  
% 4.04/1.00  ------ 
% 4.04/1.00  
% 4.04/1.00  ------ Input Options
% 4.04/1.00  
% 4.04/1.00  --out_options                           all
% 4.04/1.00  --tptp_safe_out                         true
% 4.04/1.00  --problem_path                          ""
% 4.04/1.00  --include_path                          ""
% 4.04/1.00  --clausifier                            res/vclausify_rel
% 4.04/1.00  --clausifier_options                    --mode clausify
% 4.04/1.00  --stdin                                 false
% 4.04/1.00  --stats_out                             all
% 4.04/1.00  
% 4.04/1.00  ------ General Options
% 4.04/1.00  
% 4.04/1.00  --fof                                   false
% 4.04/1.00  --time_out_real                         305.
% 4.04/1.00  --time_out_virtual                      -1.
% 4.04/1.00  --symbol_type_check                     false
% 4.04/1.00  --clausify_out                          false
% 4.04/1.00  --sig_cnt_out                           false
% 4.04/1.00  --trig_cnt_out                          false
% 4.04/1.00  --trig_cnt_out_tolerance                1.
% 4.04/1.00  --trig_cnt_out_sk_spl                   false
% 4.04/1.00  --abstr_cl_out                          false
% 4.04/1.00  
% 4.04/1.00  ------ Global Options
% 4.04/1.00  
% 4.04/1.00  --schedule                              default
% 4.04/1.00  --add_important_lit                     false
% 4.04/1.00  --prop_solver_per_cl                    1000
% 4.04/1.00  --min_unsat_core                        false
% 4.04/1.00  --soft_assumptions                      false
% 4.04/1.00  --soft_lemma_size                       3
% 4.04/1.00  --prop_impl_unit_size                   0
% 4.04/1.00  --prop_impl_unit                        []
% 4.04/1.00  --share_sel_clauses                     true
% 4.04/1.00  --reset_solvers                         false
% 4.04/1.00  --bc_imp_inh                            [conj_cone]
% 4.04/1.00  --conj_cone_tolerance                   3.
% 4.04/1.00  --extra_neg_conj                        none
% 4.04/1.00  --large_theory_mode                     true
% 4.04/1.00  --prolific_symb_bound                   200
% 4.04/1.00  --lt_threshold                          2000
% 4.04/1.00  --clause_weak_htbl                      true
% 4.04/1.00  --gc_record_bc_elim                     false
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing Options
% 4.04/1.00  
% 4.04/1.00  --preprocessing_flag                    true
% 4.04/1.00  --time_out_prep_mult                    0.1
% 4.04/1.00  --splitting_mode                        input
% 4.04/1.00  --splitting_grd                         true
% 4.04/1.00  --splitting_cvd                         false
% 4.04/1.00  --splitting_cvd_svl                     false
% 4.04/1.00  --splitting_nvd                         32
% 4.04/1.00  --sub_typing                            true
% 4.04/1.00  --prep_gs_sim                           true
% 4.04/1.00  --prep_unflatten                        true
% 4.04/1.00  --prep_res_sim                          true
% 4.04/1.00  --prep_upred                            true
% 4.04/1.00  --prep_sem_filter                       exhaustive
% 4.04/1.00  --prep_sem_filter_out                   false
% 4.04/1.00  --pred_elim                             true
% 4.04/1.00  --res_sim_input                         true
% 4.04/1.00  --eq_ax_congr_red                       true
% 4.04/1.00  --pure_diseq_elim                       true
% 4.04/1.00  --brand_transform                       false
% 4.04/1.00  --non_eq_to_eq                          false
% 4.04/1.00  --prep_def_merge                        true
% 4.04/1.00  --prep_def_merge_prop_impl              false
% 4.04/1.00  --prep_def_merge_mbd                    true
% 4.04/1.00  --prep_def_merge_tr_red                 false
% 4.04/1.00  --prep_def_merge_tr_cl                  false
% 4.04/1.00  --smt_preprocessing                     true
% 4.04/1.00  --smt_ac_axioms                         fast
% 4.04/1.00  --preprocessed_out                      false
% 4.04/1.00  --preprocessed_stats                    false
% 4.04/1.00  
% 4.04/1.00  ------ Abstraction refinement Options
% 4.04/1.00  
% 4.04/1.00  --abstr_ref                             []
% 4.04/1.00  --abstr_ref_prep                        false
% 4.04/1.00  --abstr_ref_until_sat                   false
% 4.04/1.00  --abstr_ref_sig_restrict                funpre
% 4.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.00  --abstr_ref_under                       []
% 4.04/1.00  
% 4.04/1.00  ------ SAT Options
% 4.04/1.00  
% 4.04/1.00  --sat_mode                              false
% 4.04/1.00  --sat_fm_restart_options                ""
% 4.04/1.00  --sat_gr_def                            false
% 4.04/1.00  --sat_epr_types                         true
% 4.04/1.00  --sat_non_cyclic_types                  false
% 4.04/1.00  --sat_finite_models                     false
% 4.04/1.00  --sat_fm_lemmas                         false
% 4.04/1.00  --sat_fm_prep                           false
% 4.04/1.00  --sat_fm_uc_incr                        true
% 4.04/1.00  --sat_out_model                         small
% 4.04/1.00  --sat_out_clauses                       false
% 4.04/1.00  
% 4.04/1.00  ------ QBF Options
% 4.04/1.00  
% 4.04/1.00  --qbf_mode                              false
% 4.04/1.00  --qbf_elim_univ                         false
% 4.04/1.00  --qbf_dom_inst                          none
% 4.04/1.00  --qbf_dom_pre_inst                      false
% 4.04/1.00  --qbf_sk_in                             false
% 4.04/1.00  --qbf_pred_elim                         true
% 4.04/1.00  --qbf_split                             512
% 4.04/1.00  
% 4.04/1.00  ------ BMC1 Options
% 4.04/1.00  
% 4.04/1.00  --bmc1_incremental                      false
% 4.04/1.00  --bmc1_axioms                           reachable_all
% 4.04/1.00  --bmc1_min_bound                        0
% 4.04/1.00  --bmc1_max_bound                        -1
% 4.04/1.00  --bmc1_max_bound_default                -1
% 4.04/1.00  --bmc1_symbol_reachability              true
% 4.04/1.00  --bmc1_property_lemmas                  false
% 4.04/1.00  --bmc1_k_induction                      false
% 4.04/1.00  --bmc1_non_equiv_states                 false
% 4.04/1.00  --bmc1_deadlock                         false
% 4.04/1.00  --bmc1_ucm                              false
% 4.04/1.00  --bmc1_add_unsat_core                   none
% 4.04/1.00  --bmc1_unsat_core_children              false
% 4.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.00  --bmc1_out_stat                         full
% 4.04/1.00  --bmc1_ground_init                      false
% 4.04/1.00  --bmc1_pre_inst_next_state              false
% 4.04/1.00  --bmc1_pre_inst_state                   false
% 4.04/1.00  --bmc1_pre_inst_reach_state             false
% 4.04/1.00  --bmc1_out_unsat_core                   false
% 4.04/1.00  --bmc1_aig_witness_out                  false
% 4.04/1.00  --bmc1_verbose                          false
% 4.04/1.00  --bmc1_dump_clauses_tptp                false
% 4.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.00  --bmc1_dump_file                        -
% 4.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.00  --bmc1_ucm_extend_mode                  1
% 4.04/1.00  --bmc1_ucm_init_mode                    2
% 4.04/1.00  --bmc1_ucm_cone_mode                    none
% 4.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.00  --bmc1_ucm_relax_model                  4
% 4.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.00  --bmc1_ucm_layered_model                none
% 4.04/1.00  --bmc1_ucm_max_lemma_size               10
% 4.04/1.00  
% 4.04/1.00  ------ AIG Options
% 4.04/1.00  
% 4.04/1.00  --aig_mode                              false
% 4.04/1.00  
% 4.04/1.00  ------ Instantiation Options
% 4.04/1.00  
% 4.04/1.00  --instantiation_flag                    true
% 4.04/1.00  --inst_sos_flag                         false
% 4.04/1.00  --inst_sos_phase                        true
% 4.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel_side                     num_symb
% 4.04/1.00  --inst_solver_per_active                1400
% 4.04/1.00  --inst_solver_calls_frac                1.
% 4.04/1.00  --inst_passive_queue_type               priority_queues
% 4.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.00  --inst_passive_queues_freq              [25;2]
% 4.04/1.00  --inst_dismatching                      true
% 4.04/1.00  --inst_eager_unprocessed_to_passive     true
% 4.04/1.00  --inst_prop_sim_given                   true
% 4.04/1.00  --inst_prop_sim_new                     false
% 4.04/1.00  --inst_subs_new                         false
% 4.04/1.00  --inst_eq_res_simp                      false
% 4.04/1.00  --inst_subs_given                       false
% 4.04/1.00  --inst_orphan_elimination               true
% 4.04/1.00  --inst_learning_loop_flag               true
% 4.04/1.00  --inst_learning_start                   3000
% 4.04/1.00  --inst_learning_factor                  2
% 4.04/1.00  --inst_start_prop_sim_after_learn       3
% 4.04/1.00  --inst_sel_renew                        solver
% 4.04/1.00  --inst_lit_activity_flag                true
% 4.04/1.00  --inst_restr_to_given                   false
% 4.04/1.00  --inst_activity_threshold               500
% 4.04/1.00  --inst_out_proof                        true
% 4.04/1.00  
% 4.04/1.00  ------ Resolution Options
% 4.04/1.00  
% 4.04/1.00  --resolution_flag                       true
% 4.04/1.00  --res_lit_sel                           adaptive
% 4.04/1.00  --res_lit_sel_side                      none
% 4.04/1.00  --res_ordering                          kbo
% 4.04/1.00  --res_to_prop_solver                    active
% 4.04/1.00  --res_prop_simpl_new                    false
% 4.04/1.00  --res_prop_simpl_given                  true
% 4.04/1.00  --res_passive_queue_type                priority_queues
% 4.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.00  --res_passive_queues_freq               [15;5]
% 4.04/1.00  --res_forward_subs                      full
% 4.04/1.00  --res_backward_subs                     full
% 4.04/1.00  --res_forward_subs_resolution           true
% 4.04/1.00  --res_backward_subs_resolution          true
% 4.04/1.00  --res_orphan_elimination                true
% 4.04/1.00  --res_time_limit                        2.
% 4.04/1.00  --res_out_proof                         true
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Options
% 4.04/1.00  
% 4.04/1.00  --superposition_flag                    true
% 4.04/1.00  --sup_passive_queue_type                priority_queues
% 4.04/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.00  --demod_completeness_check              fast
% 4.04/1.00  --demod_use_ground                      true
% 4.04/1.00  --sup_to_prop_solver                    passive
% 4.04/1.00  --sup_prop_simpl_new                    true
% 4.04/1.00  --sup_prop_simpl_given                  true
% 4.04/1.00  --sup_fun_splitting                     false
% 4.04/1.00  --sup_smt_interval                      50000
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Simplification Setup
% 4.04/1.00  
% 4.04/1.00  --sup_indices_passive                   []
% 4.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_full_bw                           [BwDemod]
% 4.04/1.00  --sup_immed_triv                        [TrivRules]
% 4.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_immed_bw_main                     []
% 4.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  
% 4.04/1.00  ------ Combination Options
% 4.04/1.00  
% 4.04/1.00  --comb_res_mult                         3
% 4.04/1.00  --comb_sup_mult                         2
% 4.04/1.00  --comb_inst_mult                        10
% 4.04/1.00  
% 4.04/1.00  ------ Debug Options
% 4.04/1.00  
% 4.04/1.00  --dbg_backtrace                         false
% 4.04/1.00  --dbg_dump_prop_clauses                 false
% 4.04/1.00  --dbg_dump_prop_clauses_file            -
% 4.04/1.00  --dbg_out_stat                          false
% 4.04/1.00  ------ Parsing...
% 4.04/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/1.00  ------ Proving...
% 4.04/1.00  ------ Problem Properties 
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  clauses                                 31
% 4.04/1.00  conjectures                             8
% 4.04/1.00  EPR                                     7
% 4.04/1.00  Horn                                    29
% 4.04/1.00  unary                                   18
% 4.04/1.00  binary                                  6
% 4.04/1.00  lits                                    66
% 4.04/1.00  lits eq                                 21
% 4.04/1.00  fd_pure                                 0
% 4.04/1.00  fd_pseudo                               0
% 4.04/1.00  fd_cond                                 1
% 4.04/1.00  fd_pseudo_cond                          4
% 4.04/1.00  AC symbols                              0
% 4.04/1.00  
% 4.04/1.00  ------ Schedule dynamic 5 is on 
% 4.04/1.00  
% 4.04/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  ------ 
% 4.04/1.00  Current options:
% 4.04/1.00  ------ 
% 4.04/1.00  
% 4.04/1.00  ------ Input Options
% 4.04/1.00  
% 4.04/1.00  --out_options                           all
% 4.04/1.00  --tptp_safe_out                         true
% 4.04/1.00  --problem_path                          ""
% 4.04/1.00  --include_path                          ""
% 4.04/1.00  --clausifier                            res/vclausify_rel
% 4.04/1.00  --clausifier_options                    --mode clausify
% 4.04/1.00  --stdin                                 false
% 4.04/1.00  --stats_out                             all
% 4.04/1.00  
% 4.04/1.00  ------ General Options
% 4.04/1.00  
% 4.04/1.00  --fof                                   false
% 4.04/1.00  --time_out_real                         305.
% 4.04/1.00  --time_out_virtual                      -1.
% 4.04/1.00  --symbol_type_check                     false
% 4.04/1.00  --clausify_out                          false
% 4.04/1.00  --sig_cnt_out                           false
% 4.04/1.00  --trig_cnt_out                          false
% 4.04/1.00  --trig_cnt_out_tolerance                1.
% 4.04/1.00  --trig_cnt_out_sk_spl                   false
% 4.04/1.00  --abstr_cl_out                          false
% 4.04/1.00  
% 4.04/1.00  ------ Global Options
% 4.04/1.00  
% 4.04/1.00  --schedule                              default
% 4.04/1.00  --add_important_lit                     false
% 4.04/1.00  --prop_solver_per_cl                    1000
% 4.04/1.00  --min_unsat_core                        false
% 4.04/1.00  --soft_assumptions                      false
% 4.04/1.00  --soft_lemma_size                       3
% 4.04/1.00  --prop_impl_unit_size                   0
% 4.04/1.00  --prop_impl_unit                        []
% 4.04/1.00  --share_sel_clauses                     true
% 4.04/1.00  --reset_solvers                         false
% 4.04/1.00  --bc_imp_inh                            [conj_cone]
% 4.04/1.00  --conj_cone_tolerance                   3.
% 4.04/1.00  --extra_neg_conj                        none
% 4.04/1.00  --large_theory_mode                     true
% 4.04/1.00  --prolific_symb_bound                   200
% 4.04/1.00  --lt_threshold                          2000
% 4.04/1.00  --clause_weak_htbl                      true
% 4.04/1.00  --gc_record_bc_elim                     false
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing Options
% 4.04/1.00  
% 4.04/1.00  --preprocessing_flag                    true
% 4.04/1.00  --time_out_prep_mult                    0.1
% 4.04/1.00  --splitting_mode                        input
% 4.04/1.00  --splitting_grd                         true
% 4.04/1.00  --splitting_cvd                         false
% 4.04/1.00  --splitting_cvd_svl                     false
% 4.04/1.00  --splitting_nvd                         32
% 4.04/1.00  --sub_typing                            true
% 4.04/1.00  --prep_gs_sim                           true
% 4.04/1.00  --prep_unflatten                        true
% 4.04/1.00  --prep_res_sim                          true
% 4.04/1.00  --prep_upred                            true
% 4.04/1.00  --prep_sem_filter                       exhaustive
% 4.04/1.00  --prep_sem_filter_out                   false
% 4.04/1.00  --pred_elim                             true
% 4.04/1.00  --res_sim_input                         true
% 4.04/1.00  --eq_ax_congr_red                       true
% 4.04/1.00  --pure_diseq_elim                       true
% 4.04/1.00  --brand_transform                       false
% 4.04/1.00  --non_eq_to_eq                          false
% 4.04/1.00  --prep_def_merge                        true
% 4.04/1.00  --prep_def_merge_prop_impl              false
% 4.04/1.00  --prep_def_merge_mbd                    true
% 4.04/1.00  --prep_def_merge_tr_red                 false
% 4.04/1.00  --prep_def_merge_tr_cl                  false
% 4.04/1.00  --smt_preprocessing                     true
% 4.04/1.00  --smt_ac_axioms                         fast
% 4.04/1.00  --preprocessed_out                      false
% 4.04/1.00  --preprocessed_stats                    false
% 4.04/1.00  
% 4.04/1.00  ------ Abstraction refinement Options
% 4.04/1.00  
% 4.04/1.00  --abstr_ref                             []
% 4.04/1.00  --abstr_ref_prep                        false
% 4.04/1.00  --abstr_ref_until_sat                   false
% 4.04/1.00  --abstr_ref_sig_restrict                funpre
% 4.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.00  --abstr_ref_under                       []
% 4.04/1.00  
% 4.04/1.00  ------ SAT Options
% 4.04/1.00  
% 4.04/1.00  --sat_mode                              false
% 4.04/1.00  --sat_fm_restart_options                ""
% 4.04/1.00  --sat_gr_def                            false
% 4.04/1.00  --sat_epr_types                         true
% 4.04/1.00  --sat_non_cyclic_types                  false
% 4.04/1.00  --sat_finite_models                     false
% 4.04/1.00  --sat_fm_lemmas                         false
% 4.04/1.00  --sat_fm_prep                           false
% 4.04/1.00  --sat_fm_uc_incr                        true
% 4.04/1.00  --sat_out_model                         small
% 4.04/1.00  --sat_out_clauses                       false
% 4.04/1.00  
% 4.04/1.00  ------ QBF Options
% 4.04/1.00  
% 4.04/1.00  --qbf_mode                              false
% 4.04/1.00  --qbf_elim_univ                         false
% 4.04/1.00  --qbf_dom_inst                          none
% 4.04/1.00  --qbf_dom_pre_inst                      false
% 4.04/1.00  --qbf_sk_in                             false
% 4.04/1.00  --qbf_pred_elim                         true
% 4.04/1.00  --qbf_split                             512
% 4.04/1.00  
% 4.04/1.00  ------ BMC1 Options
% 4.04/1.00  
% 4.04/1.00  --bmc1_incremental                      false
% 4.04/1.00  --bmc1_axioms                           reachable_all
% 4.04/1.00  --bmc1_min_bound                        0
% 4.04/1.00  --bmc1_max_bound                        -1
% 4.04/1.00  --bmc1_max_bound_default                -1
% 4.04/1.00  --bmc1_symbol_reachability              true
% 4.04/1.00  --bmc1_property_lemmas                  false
% 4.04/1.00  --bmc1_k_induction                      false
% 4.04/1.00  --bmc1_non_equiv_states                 false
% 4.04/1.00  --bmc1_deadlock                         false
% 4.04/1.00  --bmc1_ucm                              false
% 4.04/1.00  --bmc1_add_unsat_core                   none
% 4.04/1.00  --bmc1_unsat_core_children              false
% 4.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.00  --bmc1_out_stat                         full
% 4.04/1.00  --bmc1_ground_init                      false
% 4.04/1.00  --bmc1_pre_inst_next_state              false
% 4.04/1.00  --bmc1_pre_inst_state                   false
% 4.04/1.00  --bmc1_pre_inst_reach_state             false
% 4.04/1.00  --bmc1_out_unsat_core                   false
% 4.04/1.00  --bmc1_aig_witness_out                  false
% 4.04/1.00  --bmc1_verbose                          false
% 4.04/1.00  --bmc1_dump_clauses_tptp                false
% 4.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.00  --bmc1_dump_file                        -
% 4.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.00  --bmc1_ucm_extend_mode                  1
% 4.04/1.00  --bmc1_ucm_init_mode                    2
% 4.04/1.00  --bmc1_ucm_cone_mode                    none
% 4.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.00  --bmc1_ucm_relax_model                  4
% 4.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.00  --bmc1_ucm_layered_model                none
% 4.04/1.00  --bmc1_ucm_max_lemma_size               10
% 4.04/1.00  
% 4.04/1.00  ------ AIG Options
% 4.04/1.00  
% 4.04/1.00  --aig_mode                              false
% 4.04/1.00  
% 4.04/1.00  ------ Instantiation Options
% 4.04/1.00  
% 4.04/1.00  --instantiation_flag                    true
% 4.04/1.00  --inst_sos_flag                         false
% 4.04/1.00  --inst_sos_phase                        true
% 4.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel_side                     none
% 4.04/1.00  --inst_solver_per_active                1400
% 4.04/1.00  --inst_solver_calls_frac                1.
% 4.04/1.00  --inst_passive_queue_type               priority_queues
% 4.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.00  --inst_passive_queues_freq              [25;2]
% 4.04/1.00  --inst_dismatching                      true
% 4.04/1.00  --inst_eager_unprocessed_to_passive     true
% 4.04/1.00  --inst_prop_sim_given                   true
% 4.04/1.00  --inst_prop_sim_new                     false
% 4.04/1.00  --inst_subs_new                         false
% 4.04/1.00  --inst_eq_res_simp                      false
% 4.04/1.00  --inst_subs_given                       false
% 4.04/1.00  --inst_orphan_elimination               true
% 4.04/1.00  --inst_learning_loop_flag               true
% 4.04/1.00  --inst_learning_start                   3000
% 4.04/1.00  --inst_learning_factor                  2
% 4.04/1.00  --inst_start_prop_sim_after_learn       3
% 4.04/1.00  --inst_sel_renew                        solver
% 4.04/1.00  --inst_lit_activity_flag                true
% 4.04/1.00  --inst_restr_to_given                   false
% 4.04/1.00  --inst_activity_threshold               500
% 4.04/1.00  --inst_out_proof                        true
% 4.04/1.00  
% 4.04/1.00  ------ Resolution Options
% 4.04/1.00  
% 4.04/1.00  --resolution_flag                       false
% 4.04/1.00  --res_lit_sel                           adaptive
% 4.04/1.00  --res_lit_sel_side                      none
% 4.04/1.00  --res_ordering                          kbo
% 4.04/1.00  --res_to_prop_solver                    active
% 4.04/1.00  --res_prop_simpl_new                    false
% 4.04/1.00  --res_prop_simpl_given                  true
% 4.04/1.00  --res_passive_queue_type                priority_queues
% 4.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.00  --res_passive_queues_freq               [15;5]
% 4.04/1.00  --res_forward_subs                      full
% 4.04/1.00  --res_backward_subs                     full
% 4.04/1.00  --res_forward_subs_resolution           true
% 4.04/1.00  --res_backward_subs_resolution          true
% 4.04/1.00  --res_orphan_elimination                true
% 4.04/1.00  --res_time_limit                        2.
% 4.04/1.00  --res_out_proof                         true
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Options
% 4.04/1.00  
% 4.04/1.00  --superposition_flag                    true
% 4.04/1.00  --sup_passive_queue_type                priority_queues
% 4.04/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.00  --demod_completeness_check              fast
% 4.04/1.00  --demod_use_ground                      true
% 4.04/1.00  --sup_to_prop_solver                    passive
% 4.04/1.00  --sup_prop_simpl_new                    true
% 4.04/1.00  --sup_prop_simpl_given                  true
% 4.04/1.00  --sup_fun_splitting                     false
% 4.04/1.00  --sup_smt_interval                      50000
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Simplification Setup
% 4.04/1.00  
% 4.04/1.00  --sup_indices_passive                   []
% 4.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_full_bw                           [BwDemod]
% 4.04/1.00  --sup_immed_triv                        [TrivRules]
% 4.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_immed_bw_main                     []
% 4.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  
% 4.04/1.00  ------ Combination Options
% 4.04/1.00  
% 4.04/1.00  --comb_res_mult                         3
% 4.04/1.00  --comb_sup_mult                         2
% 4.04/1.00  --comb_inst_mult                        10
% 4.04/1.00  
% 4.04/1.00  ------ Debug Options
% 4.04/1.00  
% 4.04/1.00  --dbg_backtrace                         false
% 4.04/1.00  --dbg_dump_prop_clauses                 false
% 4.04/1.00  --dbg_dump_prop_clauses_file            -
% 4.04/1.00  --dbg_out_stat                          false
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  ------ Proving...
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  % SZS status Theorem for theBenchmark.p
% 4.04/1.00  
% 4.04/1.00   Resolution empty clause
% 4.04/1.00  
% 4.04/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  fof(f19,conjecture,(
% 4.04/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f20,negated_conjecture,(
% 4.04/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 4.04/1.00    inference(negated_conjecture,[],[f19])).
% 4.04/1.00  
% 4.04/1.00  fof(f38,plain,(
% 4.04/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 4.04/1.00    inference(ennf_transformation,[],[f20])).
% 4.04/1.00  
% 4.04/1.00  fof(f39,plain,(
% 4.04/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 4.04/1.00    inference(flattening,[],[f38])).
% 4.04/1.00  
% 4.04/1.00  fof(f49,plain,(
% 4.04/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f48,plain,(
% 4.04/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f50,plain,(
% 4.04/1.00    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 4.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f49,f48])).
% 4.04/1.00  
% 4.04/1.00  fof(f89,plain,(
% 4.04/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 4.04/1.00    inference(cnf_transformation,[],[f50])).
% 4.04/1.00  
% 4.04/1.00  fof(f84,plain,(
% 4.04/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.04/1.00    inference(cnf_transformation,[],[f50])).
% 4.04/1.00  
% 4.04/1.00  fof(f3,axiom,(
% 4.04/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f44,plain,(
% 4.04/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.04/1.00    inference(nnf_transformation,[],[f3])).
% 4.04/1.00  
% 4.04/1.00  fof(f57,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f44])).
% 4.04/1.00  
% 4.04/1.00  fof(f4,axiom,(
% 4.04/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f22,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f4])).
% 4.04/1.00  
% 4.04/1.00  fof(f59,plain,(
% 4.04/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f22])).
% 4.04/1.00  
% 4.04/1.00  fof(f58,plain,(
% 4.04/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f44])).
% 4.04/1.00  
% 4.04/1.00  fof(f6,axiom,(
% 4.04/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f62,plain,(
% 4.04/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f6])).
% 4.04/1.00  
% 4.04/1.00  fof(f10,axiom,(
% 4.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f21,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.04/1.00    inference(pure_predicate_removal,[],[f10])).
% 4.04/1.00  
% 4.04/1.00  fof(f24,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.00    inference(ennf_transformation,[],[f21])).
% 4.04/1.00  
% 4.04/1.00  fof(f67,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f24])).
% 4.04/1.00  
% 4.04/1.00  fof(f14,axiom,(
% 4.04/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f30,plain,(
% 4.04/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.04/1.00    inference(ennf_transformation,[],[f14])).
% 4.04/1.00  
% 4.04/1.00  fof(f31,plain,(
% 4.04/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.04/1.00    inference(flattening,[],[f30])).
% 4.04/1.00  
% 4.04/1.00  fof(f47,plain,(
% 4.04/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.04/1.00    inference(nnf_transformation,[],[f31])).
% 4.04/1.00  
% 4.04/1.00  fof(f74,plain,(
% 4.04/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f47])).
% 4.04/1.00  
% 4.04/1.00  fof(f13,axiom,(
% 4.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f28,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.00    inference(ennf_transformation,[],[f13])).
% 4.04/1.00  
% 4.04/1.00  fof(f29,plain,(
% 4.04/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.00    inference(flattening,[],[f28])).
% 4.04/1.00  
% 4.04/1.00  fof(f73,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f29])).
% 4.04/1.00  
% 4.04/1.00  fof(f83,plain,(
% 4.04/1.00    v3_funct_2(sK1,sK0,sK0)),
% 4.04/1.00    inference(cnf_transformation,[],[f50])).
% 4.04/1.00  
% 4.04/1.00  fof(f81,plain,(
% 4.04/1.00    v1_funct_1(sK1)),
% 4.04/1.00    inference(cnf_transformation,[],[f50])).
% 4.04/1.00  
% 4.04/1.00  fof(f11,axiom,(
% 4.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f25,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.00    inference(ennf_transformation,[],[f11])).
% 4.04/1.00  
% 4.04/1.00  fof(f68,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f25])).
% 4.04/1.00  
% 4.04/1.00  fof(f18,axiom,(
% 4.04/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f36,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.04/1.00    inference(ennf_transformation,[],[f18])).
% 4.04/1.00  
% 4.04/1.00  fof(f37,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.04/1.00    inference(flattening,[],[f36])).
% 4.04/1.00  
% 4.04/1.00  fof(f80,plain,(
% 4.04/1.00    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f37])).
% 4.04/1.00  
% 4.04/1.00  fof(f17,axiom,(
% 4.04/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f34,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.04/1.00    inference(ennf_transformation,[],[f17])).
% 4.04/1.00  
% 4.04/1.00  fof(f35,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.04/1.00    inference(flattening,[],[f34])).
% 4.04/1.00  
% 4.04/1.00  fof(f78,plain,(
% 4.04/1.00    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f35])).
% 4.04/1.00  
% 4.04/1.00  fof(f82,plain,(
% 4.04/1.00    v1_funct_2(sK1,sK0,sK0)),
% 4.04/1.00    inference(cnf_transformation,[],[f50])).
% 4.04/1.00  
% 4.04/1.00  fof(f85,plain,(
% 4.04/1.00    v1_funct_1(sK2)),
% 4.04/1.00    inference(cnf_transformation,[],[f50])).
% 4.04/1.00  
% 4.04/1.00  fof(f86,plain,(
% 4.04/1.00    v1_funct_2(sK2,sK0,sK0)),
% 4.04/1.00    inference(cnf_transformation,[],[f50])).
% 4.04/1.00  
% 4.04/1.00  fof(f88,plain,(
% 4.04/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.04/1.00    inference(cnf_transformation,[],[f50])).
% 4.04/1.00  
% 4.04/1.00  fof(f90,plain,(
% 4.04/1.00    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 4.04/1.00    inference(cnf_transformation,[],[f50])).
% 4.04/1.00  
% 4.04/1.00  fof(f15,axiom,(
% 4.04/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f32,plain,(
% 4.04/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.04/1.00    inference(ennf_transformation,[],[f15])).
% 4.04/1.00  
% 4.04/1.00  fof(f33,plain,(
% 4.04/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.04/1.00    inference(flattening,[],[f32])).
% 4.04/1.00  
% 4.04/1.00  fof(f76,plain,(
% 4.04/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f33])).
% 4.04/1.00  
% 4.04/1.00  fof(f12,axiom,(
% 4.04/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f26,plain,(
% 4.04/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.04/1.00    inference(ennf_transformation,[],[f12])).
% 4.04/1.00  
% 4.04/1.00  fof(f27,plain,(
% 4.04/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.00    inference(flattening,[],[f26])).
% 4.04/1.00  
% 4.04/1.00  fof(f46,plain,(
% 4.04/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.00    inference(nnf_transformation,[],[f27])).
% 4.04/1.00  
% 4.04/1.00  fof(f70,plain,(
% 4.04/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f46])).
% 4.04/1.00  
% 4.04/1.00  fof(f99,plain,(
% 4.04/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.04/1.00    inference(equality_resolution,[],[f70])).
% 4.04/1.00  
% 4.04/1.00  fof(f2,axiom,(
% 4.04/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f42,plain,(
% 4.04/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 4.04/1.00    inference(nnf_transformation,[],[f2])).
% 4.04/1.00  
% 4.04/1.00  fof(f43,plain,(
% 4.04/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 4.04/1.00    inference(flattening,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f55,plain,(
% 4.04/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 4.04/1.00    inference(cnf_transformation,[],[f43])).
% 4.04/1.00  
% 4.04/1.00  fof(f98,plain,(
% 4.04/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 4.04/1.00    inference(equality_resolution,[],[f55])).
% 4.04/1.00  
% 4.04/1.00  fof(f5,axiom,(
% 4.04/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f23,plain,(
% 4.04/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.04/1.00    inference(ennf_transformation,[],[f5])).
% 4.04/1.00  
% 4.04/1.00  fof(f45,plain,(
% 4.04/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.04/1.00    inference(nnf_transformation,[],[f23])).
% 4.04/1.00  
% 4.04/1.00  fof(f60,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f45])).
% 4.04/1.00  
% 4.04/1.00  fof(f1,axiom,(
% 4.04/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f40,plain,(
% 4.04/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.00    inference(nnf_transformation,[],[f1])).
% 4.04/1.00  
% 4.04/1.00  fof(f41,plain,(
% 4.04/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.00    inference(flattening,[],[f40])).
% 4.04/1.00  
% 4.04/1.00  fof(f53,plain,(
% 4.04/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f41])).
% 4.04/1.00  
% 4.04/1.00  fof(f8,axiom,(
% 4.04/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f65,plain,(
% 4.04/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 4.04/1.00    inference(cnf_transformation,[],[f8])).
% 4.04/1.00  
% 4.04/1.00  fof(f16,axiom,(
% 4.04/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f77,plain,(
% 4.04/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f16])).
% 4.04/1.00  
% 4.04/1.00  fof(f93,plain,(
% 4.04/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 4.04/1.00    inference(definition_unfolding,[],[f65,f77])).
% 4.04/1.00  
% 4.04/1.00  fof(f9,axiom,(
% 4.04/1.00    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f66,plain,(
% 4.04/1.00    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f9])).
% 4.04/1.00  
% 4.04/1.00  fof(f94,plain,(
% 4.04/1.00    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 4.04/1.00    inference(definition_unfolding,[],[f66,f77,f77])).
% 4.04/1.00  
% 4.04/1.00  cnf(c_30,negated_conjecture,
% 4.04/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 4.04/1.00      inference(cnf_transformation,[],[f89]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1890,plain,
% 4.04/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_35,negated_conjecture,
% 4.04/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 4.04/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1886,plain,
% 4.04/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1896,plain,
% 4.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.04/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3390,plain,
% 4.04/1.00      ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1886,c_1896]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_6,plain,
% 4.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f58]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_253,plain,
% 4.04/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.04/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_254,plain,
% 4.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.04/1.00      inference(renaming,[status(thm)],[c_253]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_321,plain,
% 4.04/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 4.04/1.00      inference(bin_hyper_res,[status(thm)],[c_8,c_254]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1882,plain,
% 4.04/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.04/1.00      | v1_relat_1(X1) != iProver_top
% 4.04/1.00      | v1_relat_1(X0) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3886,plain,
% 4.04/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 4.04/1.00      | v1_relat_1(sK1) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_3390,c_1882]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_42,plain,
% 4.04/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_11,plain,
% 4.04/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.04/1.00      inference(cnf_transformation,[],[f62]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_89,plain,
% 4.04/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_91,plain,
% 4.04/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_89]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2252,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2956,plain,
% 4.04/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.04/1.00      | r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_2252]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2957,plain,
% 4.04/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.04/1.00      | r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_2956]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2177,plain,
% 4.04/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 4.04/1.00      | v1_relat_1(X0)
% 4.04/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_321]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3109,plain,
% 4.04/1.00      ( ~ r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
% 4.04/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 4.04/1.00      | v1_relat_1(sK1) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_2177]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3111,plain,
% 4.04/1.00      ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) != iProver_top
% 4.04/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 4.04/1.00      | v1_relat_1(sK1) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_3109]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_4098,plain,
% 4.04/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_3886,c_42,c_91,c_2957,c_3111]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_16,plain,
% 4.04/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.04/1.00      inference(cnf_transformation,[],[f67]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_24,plain,
% 4.04/1.00      ( ~ v2_funct_2(X0,X1)
% 4.04/1.00      | ~ v5_relat_1(X0,X1)
% 4.04/1.00      | ~ v1_relat_1(X0)
% 4.04/1.00      | k2_relat_1(X0) = X1 ),
% 4.04/1.00      inference(cnf_transformation,[],[f74]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_20,plain,
% 4.04/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 4.04/1.00      | v2_funct_2(X0,X2)
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ v1_funct_1(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f73]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_36,negated_conjecture,
% 4.04/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_441,plain,
% 4.04/1.00      ( v2_funct_2(X0,X1)
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | sK1 != X0
% 4.04/1.00      | sK0 != X1
% 4.04/1.00      | sK0 != X2 ),
% 4.04/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_36]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_442,plain,
% 4.04/1.00      ( v2_funct_2(sK1,sK0)
% 4.04/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.04/1.00      | ~ v1_funct_1(sK1) ),
% 4.04/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_38,negated_conjecture,
% 4.04/1.00      ( v1_funct_1(sK1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f81]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_444,plain,
% 4.04/1.00      ( v2_funct_2(sK1,sK0) ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_442,c_38,c_35]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_527,plain,
% 4.04/1.00      ( ~ v5_relat_1(X0,X1)
% 4.04/1.00      | ~ v1_relat_1(X0)
% 4.04/1.00      | k2_relat_1(X0) = X1
% 4.04/1.00      | sK1 != X0
% 4.04/1.00      | sK0 != X1 ),
% 4.04/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_444]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_528,plain,
% 4.04/1.00      ( ~ v5_relat_1(sK1,sK0) | ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 4.04/1.00      inference(unflattening,[status(thm)],[c_527]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_591,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ v1_relat_1(sK1)
% 4.04/1.00      | k2_relat_1(sK1) = sK0
% 4.04/1.00      | sK1 != X0
% 4.04/1.00      | sK0 != X2 ),
% 4.04/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_528]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_592,plain,
% 4.04/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 4.04/1.00      | ~ v1_relat_1(sK1)
% 4.04/1.00      | k2_relat_1(sK1) = sK0 ),
% 4.04/1.00      inference(unflattening,[status(thm)],[c_591]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_594,plain,
% 4.04/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.04/1.00      | ~ v1_relat_1(sK1)
% 4.04/1.00      | k2_relat_1(sK1) = sK0 ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_592]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_596,plain,
% 4.04/1.00      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_592,c_35,c_594]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1878,plain,
% 4.04/1.00      ( k2_relat_1(sK1) = sK0 | v1_relat_1(sK1) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_4103,plain,
% 4.04/1.00      ( k2_relat_1(sK1) = sK0 ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_4098,c_1878]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_17,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1894,plain,
% 4.04/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.04/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_4645,plain,
% 4.04/1.00      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1886,c_1894]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7624,plain,
% 4.04/1.00      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 4.04/1.00      inference(demodulation,[status(thm)],[c_4103,c_4645]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_28,plain,
% 4.04/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 4.04/1.00      | ~ v1_funct_2(X3,X1,X0)
% 4.04/1.00      | ~ v1_funct_2(X2,X0,X1)
% 4.04/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 4.04/1.00      | ~ v2_funct_1(X2)
% 4.04/1.00      | ~ v1_funct_1(X2)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | k2_relset_1(X0,X1,X2) != X1
% 4.04/1.00      | k2_funct_1(X2) = X3
% 4.04/1.00      | k1_xboole_0 = X1
% 4.04/1.00      | k1_xboole_0 = X0 ),
% 4.04/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_27,plain,
% 4.04/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 4.04/1.00      | ~ v1_funct_2(X3,X1,X0)
% 4.04/1.00      | ~ v1_funct_2(X2,X0,X1)
% 4.04/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 4.04/1.00      | v2_funct_1(X2)
% 4.04/1.00      | ~ v1_funct_1(X2)
% 4.04/1.00      | ~ v1_funct_1(X3) ),
% 4.04/1.00      inference(cnf_transformation,[],[f78]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_190,plain,
% 4.04/1.00      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 4.04/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.04/1.00      | ~ v1_funct_2(X2,X0,X1)
% 4.04/1.00      | ~ v1_funct_2(X3,X1,X0)
% 4.04/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 4.04/1.00      | ~ v1_funct_1(X2)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | k2_relset_1(X0,X1,X2) != X1
% 4.04/1.00      | k2_funct_1(X2) = X3
% 4.04/1.00      | k1_xboole_0 = X1
% 4.04/1.00      | k1_xboole_0 = X0 ),
% 4.04/1.00      inference(global_propositional_subsumption,[status(thm)],[c_28,c_27]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_191,plain,
% 4.04/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 4.04/1.00      | ~ v1_funct_2(X3,X1,X0)
% 4.04/1.00      | ~ v1_funct_2(X2,X0,X1)
% 4.04/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 4.04/1.00      | ~ v1_funct_1(X2)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | k2_relset_1(X0,X1,X2) != X1
% 4.04/1.00      | k2_funct_1(X2) = X3
% 4.04/1.01      | k1_xboole_0 = X1
% 4.04/1.01      | k1_xboole_0 = X0 ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_190]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1883,plain,
% 4.04/1.01      ( k2_relset_1(X0,X1,X2) != X1
% 4.04/1.01      | k2_funct_1(X2) = X3
% 4.04/1.01      | k1_xboole_0 = X1
% 4.04/1.01      | k1_xboole_0 = X0
% 4.04/1.01      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 4.04/1.01      | v1_funct_2(X3,X1,X0) != iProver_top
% 4.04/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.04/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 4.04/1.01      | v1_funct_1(X2) != iProver_top
% 4.04/1.01      | v1_funct_1(X3) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_7715,plain,
% 4.04/1.01      ( k2_funct_1(sK1) = X0
% 4.04/1.01      | sK0 = k1_xboole_0
% 4.04/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 4.04/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 4.04/1.01      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.04/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.04/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.04/1.01      | v1_funct_1(X0) != iProver_top
% 4.04/1.01      | v1_funct_1(sK1) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_7624,c_1883]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_39,plain,
% 4.04/1.01      ( v1_funct_1(sK1) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_37,negated_conjecture,
% 4.04/1.01      ( v1_funct_2(sK1,sK0,sK0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f82]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_40,plain,
% 4.04/1.01      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9840,plain,
% 4.04/1.01      ( v1_funct_1(X0) != iProver_top
% 4.04/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 4.04/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 4.04/1.01      | sK0 = k1_xboole_0
% 4.04/1.01      | k2_funct_1(sK1) = X0
% 4.04/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_7715,c_39,c_40,c_42]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9841,plain,
% 4.04/1.01      ( k2_funct_1(sK1) = X0
% 4.04/1.01      | sK0 = k1_xboole_0
% 4.04/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 4.04/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 4.04/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.04/1.01      | v1_funct_1(X0) != iProver_top ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_9840]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9852,plain,
% 4.04/1.01      ( k2_funct_1(sK1) = sK2
% 4.04/1.01      | sK0 = k1_xboole_0
% 4.04/1.01      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 4.04/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.04/1.01      | v1_funct_1(sK2) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1890,c_9841]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_34,negated_conjecture,
% 4.04/1.01      ( v1_funct_1(sK2) ),
% 4.04/1.01      inference(cnf_transformation,[],[f85]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_33,negated_conjecture,
% 4.04/1.01      ( v1_funct_2(sK2,sK0,sK0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f86]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_31,negated_conjecture,
% 4.04/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 4.04/1.01      inference(cnf_transformation,[],[f88]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9853,plain,
% 4.04/1.01      ( ~ v1_funct_2(sK2,sK0,sK0)
% 4.04/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.04/1.01      | ~ v1_funct_1(sK2)
% 4.04/1.01      | k2_funct_1(sK1) = sK2
% 4.04/1.01      | sK0 = k1_xboole_0 ),
% 4.04/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_9852]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9855,plain,
% 4.04/1.01      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_9852,c_43,c_44,c_46]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9856,plain,
% 4.04/1.01      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_9855]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_29,negated_conjecture,
% 4.04/1.01      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 4.04/1.01      inference(cnf_transformation,[],[f90]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1891,plain,
% 4.04/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_25,plain,
% 4.04/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 4.04/1.01      | ~ v3_funct_2(X0,X1,X1)
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f76]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_460,plain,
% 4.04/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 4.04/1.01      | sK1 != X0
% 4.04/1.01      | sK0 != X1 ),
% 4.04/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_461,plain,
% 4.04/1.01      ( ~ v1_funct_2(sK1,sK0,sK0)
% 4.04/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.04/1.01      | ~ v1_funct_1(sK1)
% 4.04/1.01      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 4.04/1.01      inference(unflattening,[status(thm)],[c_460]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_463,plain,
% 4.04/1.01      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_461,c_38,c_37,c_35]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1940,plain,
% 4.04/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 4.04/1.01      inference(light_normalisation,[status(thm)],[c_1891,c_463]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9859,plain,
% 4.04/1.01      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_9856,c_1940]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_46,plain,
% 4.04/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_18,plain,
% 4.04/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 4.04/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 4.04/1.01      inference(cnf_transformation,[],[f99]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2120,plain,
% 4.04/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 4.04/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2121,plain,
% 4.04/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 4.04/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_2120]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9912,plain,
% 4.04/1.01      ( sK0 = k1_xboole_0 ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_9859,c_46,c_2121]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9938,plain,
% 4.04/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_9912,c_1886]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_4,plain,
% 4.04/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f98]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9952,plain,
% 4.04/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_9938,c_4]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10,plain,
% 4.04/1.01      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f60]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_558,plain,
% 4.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 4.04/1.01      | ~ v1_relat_1(X0) ),
% 4.04/1.01      inference(resolution,[status(thm)],[c_16,c_10]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1880,plain,
% 4.04/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.04/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 4.04/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_4169,plain,
% 4.04/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 4.04/1.01      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 4.04/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_4,c_1880]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10308,plain,
% 4.04/1.01      ( r1_tarski(k2_relat_1(sK1),X0) = iProver_top
% 4.04/1.01      | v1_relat_1(sK1) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_9952,c_4169]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10877,plain,
% 4.04/1.01      ( r1_tarski(k2_relat_1(sK1),X0) = iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_10308,c_42,c_91,c_2957,c_3111]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9926,plain,
% 4.04/1.01      ( k2_relat_1(sK1) = k1_xboole_0 ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_9912,c_4103]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10881,plain,
% 4.04/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.04/1.01      inference(light_normalisation,[status(thm)],[c_10877,c_9926]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1889,plain,
% 4.04/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3389,plain,
% 4.04/1.01      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1889,c_1896]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_0,plain,
% 4.04/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.04/1.01      inference(cnf_transformation,[],[f53]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1899,plain,
% 4.04/1.01      ( X0 = X1
% 4.04/1.01      | r1_tarski(X0,X1) != iProver_top
% 4.04/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_7407,plain,
% 4.04/1.01      ( k2_zfmisc_1(sK0,sK0) = sK2
% 4.04/1.01      | r1_tarski(k2_zfmisc_1(sK0,sK0),sK2) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_3389,c_1899]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9930,plain,
% 4.04/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK2
% 4.04/1.01      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_9912,c_7407]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9974,plain,
% 4.04/1.01      ( sK2 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_9930,c_4]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10891,plain,
% 4.04/1.01      ( sK2 = k1_xboole_0 ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_10881,c_9974]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9935,plain,
% 4.04/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_9912,c_1940]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11760,plain,
% 4.04/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_10891,c_9935]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_14,plain,
% 4.04/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f93]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_15,plain,
% 4.04/1.01      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f94]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3116,plain,
% 4.04/1.01      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3117,plain,
% 4.04/1.01      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 4.04/1.01      inference(light_normalisation,[status(thm)],[c_3116,c_14]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_7408,plain,
% 4.04/1.01      ( k2_zfmisc_1(sK0,sK0) = sK1
% 4.04/1.01      | r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_3390,c_1899]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9929,plain,
% 4.04/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK1
% 4.04/1.01      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_9912,c_7408]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9979,plain,
% 4.04/1.01      ( sK1 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_9929,c_4]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10892,plain,
% 4.04/1.01      ( sK1 = k1_xboole_0 ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_10881,c_9979]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11977,plain,
% 4.04/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 4.04/1.01      inference(light_normalisation,[status(thm)],[c_11760,c_3117,c_10892]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1893,plain,
% 4.04/1.01      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 4.04/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_4202,plain,
% 4.04/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1889,c_1893]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9932,plain,
% 4.04/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_9912,c_4202]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11761,plain,
% 4.04/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_10891,c_9932]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11979,plain,
% 4.04/1.01      ( $false ),
% 4.04/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_11977,c_11761]) ).
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/1.01  
% 4.04/1.01  ------                               Statistics
% 4.04/1.01  
% 4.04/1.01  ------ General
% 4.04/1.01  
% 4.04/1.01  abstr_ref_over_cycles:                  0
% 4.04/1.01  abstr_ref_under_cycles:                 0
% 4.04/1.01  gc_basic_clause_elim:                   0
% 4.04/1.01  forced_gc_time:                         0
% 4.04/1.01  parsing_time:                           0.011
% 4.04/1.01  unif_index_cands_time:                  0.
% 4.04/1.01  unif_index_add_time:                    0.
% 4.04/1.01  orderings_time:                         0.
% 4.04/1.01  out_proof_time:                         0.014
% 4.04/1.01  total_time:                             0.423
% 4.04/1.01  num_of_symbols:                         54
% 4.04/1.01  num_of_terms:                           17152
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing
% 4.04/1.01  
% 4.04/1.01  num_of_splits:                          0
% 4.04/1.01  num_of_split_atoms:                     0
% 4.04/1.01  num_of_reused_defs:                     0
% 4.04/1.01  num_eq_ax_congr_red:                    15
% 4.04/1.01  num_of_sem_filtered_clauses:            3
% 4.04/1.01  num_of_subtypes:                        0
% 4.04/1.01  monotx_restored_types:                  0
% 4.04/1.01  sat_num_of_epr_types:                   0
% 4.04/1.01  sat_num_of_non_cyclic_types:            0
% 4.04/1.01  sat_guarded_non_collapsed_types:        0
% 4.04/1.01  num_pure_diseq_elim:                    0
% 4.04/1.01  simp_replaced_by:                       0
% 4.04/1.01  res_preprocessed:                       163
% 4.04/1.01  prep_upred:                             0
% 4.04/1.01  prep_unflattend:                        64
% 4.04/1.01  smt_new_axioms:                         0
% 4.04/1.01  pred_elim_cands:                        6
% 4.04/1.01  pred_elim:                              3
% 4.04/1.01  pred_elim_cl:                           4
% 4.04/1.01  pred_elim_cycles:                       5
% 4.04/1.01  merged_defs:                            8
% 4.04/1.01  merged_defs_ncl:                        0
% 4.04/1.01  bin_hyper_res:                          9
% 4.04/1.01  prep_cycles:                            4
% 4.04/1.01  pred_elim_time:                         0.014
% 4.04/1.01  splitting_time:                         0.
% 4.04/1.01  sem_filter_time:                        0.
% 4.04/1.01  monotx_time:                            0.
% 4.04/1.01  subtype_inf_time:                       0.
% 4.04/1.01  
% 4.04/1.01  ------ Problem properties
% 4.04/1.01  
% 4.04/1.01  clauses:                                31
% 4.04/1.01  conjectures:                            8
% 4.04/1.01  epr:                                    7
% 4.04/1.01  horn:                                   29
% 4.04/1.01  ground:                                 13
% 4.04/1.01  unary:                                  18
% 4.04/1.01  binary:                                 6
% 4.04/1.01  lits:                                   66
% 4.04/1.01  lits_eq:                                21
% 4.04/1.01  fd_pure:                                0
% 4.04/1.01  fd_pseudo:                              0
% 4.04/1.01  fd_cond:                                1
% 4.04/1.01  fd_pseudo_cond:                         4
% 4.04/1.01  ac_symbols:                             0
% 4.04/1.01  
% 4.04/1.01  ------ Propositional Solver
% 4.04/1.01  
% 4.04/1.01  prop_solver_calls:                      27
% 4.04/1.01  prop_fast_solver_calls:                 1260
% 4.04/1.01  smt_solver_calls:                       0
% 4.04/1.01  smt_fast_solver_calls:                  0
% 4.04/1.01  prop_num_of_clauses:                    4066
% 4.04/1.01  prop_preprocess_simplified:             11158
% 4.04/1.01  prop_fo_subsumed:                       36
% 4.04/1.01  prop_solver_time:                       0.
% 4.04/1.01  smt_solver_time:                        0.
% 4.04/1.01  smt_fast_solver_time:                   0.
% 4.04/1.01  prop_fast_solver_time:                  0.
% 4.04/1.01  prop_unsat_core_time:                   0.
% 4.04/1.01  
% 4.04/1.01  ------ QBF
% 4.04/1.01  
% 4.04/1.01  qbf_q_res:                              0
% 4.04/1.01  qbf_num_tautologies:                    0
% 4.04/1.01  qbf_prep_cycles:                        0
% 4.04/1.01  
% 4.04/1.01  ------ BMC1
% 4.04/1.01  
% 4.04/1.01  bmc1_current_bound:                     -1
% 4.04/1.01  bmc1_last_solved_bound:                 -1
% 4.04/1.01  bmc1_unsat_core_size:                   -1
% 4.04/1.01  bmc1_unsat_core_parents_size:           -1
% 4.04/1.01  bmc1_merge_next_fun:                    0
% 4.04/1.01  bmc1_unsat_core_clauses_time:           0.
% 4.04/1.01  
% 4.04/1.01  ------ Instantiation
% 4.04/1.01  
% 4.04/1.01  inst_num_of_clauses:                    1159
% 4.04/1.01  inst_num_in_passive:                    280
% 4.04/1.01  inst_num_in_active:                     633
% 4.04/1.01  inst_num_in_unprocessed:                246
% 4.04/1.01  inst_num_of_loops:                      640
% 4.04/1.01  inst_num_of_learning_restarts:          0
% 4.04/1.01  inst_num_moves_active_passive:          6
% 4.04/1.01  inst_lit_activity:                      0
% 4.04/1.01  inst_lit_activity_moves:                0
% 4.04/1.01  inst_num_tautologies:                   0
% 4.04/1.01  inst_num_prop_implied:                  0
% 4.04/1.01  inst_num_existing_simplified:           0
% 4.04/1.01  inst_num_eq_res_simplified:             0
% 4.04/1.01  inst_num_child_elim:                    0
% 4.04/1.01  inst_num_of_dismatching_blockings:      607
% 4.04/1.01  inst_num_of_non_proper_insts:           1576
% 4.04/1.01  inst_num_of_duplicates:                 0
% 4.04/1.01  inst_inst_num_from_inst_to_res:         0
% 4.04/1.01  inst_dismatching_checking_time:         0.
% 4.04/1.01  
% 4.04/1.01  ------ Resolution
% 4.04/1.01  
% 4.04/1.01  res_num_of_clauses:                     0
% 4.04/1.01  res_num_in_passive:                     0
% 4.04/1.01  res_num_in_active:                      0
% 4.04/1.01  res_num_of_loops:                       167
% 4.04/1.01  res_forward_subset_subsumed:            65
% 4.04/1.01  res_backward_subset_subsumed:           0
% 4.04/1.01  res_forward_subsumed:                   0
% 4.04/1.01  res_backward_subsumed:                  0
% 4.04/1.01  res_forward_subsumption_resolution:     1
% 4.04/1.01  res_backward_subsumption_resolution:    0
% 4.04/1.01  res_clause_to_clause_subsumption:       423
% 4.04/1.01  res_orphan_elimination:                 0
% 4.04/1.01  res_tautology_del:                      49
% 4.04/1.01  res_num_eq_res_simplified:              0
% 4.04/1.01  res_num_sel_changes:                    0
% 4.04/1.01  res_moves_from_active_to_pass:          0
% 4.04/1.01  
% 4.04/1.01  ------ Superposition
% 4.04/1.01  
% 4.04/1.01  sup_time_total:                         0.
% 4.04/1.01  sup_time_generating:                    0.
% 4.04/1.01  sup_time_sim_full:                      0.
% 4.04/1.01  sup_time_sim_immed:                     0.
% 4.04/1.01  
% 4.04/1.01  sup_num_of_clauses:                     82
% 4.04/1.01  sup_num_in_active:                      54
% 4.04/1.01  sup_num_in_passive:                     28
% 4.04/1.01  sup_num_of_loops:                       127
% 4.04/1.01  sup_fw_superposition:                   118
% 4.04/1.01  sup_bw_superposition:                   72
% 4.04/1.01  sup_immediate_simplified:               53
% 4.04/1.01  sup_given_eliminated:                   0
% 4.04/1.01  comparisons_done:                       0
% 4.04/1.01  comparisons_avoided:                    3
% 4.04/1.01  
% 4.04/1.01  ------ Simplifications
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  sim_fw_subset_subsumed:                 10
% 4.04/1.01  sim_bw_subset_subsumed:                 6
% 4.04/1.01  sim_fw_subsumed:                        9
% 4.04/1.01  sim_bw_subsumed:                        0
% 4.04/1.01  sim_fw_subsumption_res:                 3
% 4.04/1.01  sim_bw_subsumption_res:                 0
% 4.04/1.01  sim_tautology_del:                      8
% 4.04/1.01  sim_eq_tautology_del:                   43
% 4.04/1.01  sim_eq_res_simp:                        0
% 4.04/1.01  sim_fw_demodulated:                     21
% 4.04/1.01  sim_bw_demodulated:                     67
% 4.04/1.01  sim_light_normalised:                   23
% 4.04/1.01  sim_joinable_taut:                      0
% 4.04/1.01  sim_joinable_simp:                      0
% 4.04/1.01  sim_ac_normalised:                      0
% 4.04/1.01  sim_smt_subsumption:                    0
% 4.04/1.01  
%------------------------------------------------------------------------------
