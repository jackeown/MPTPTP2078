%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:16 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_34)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f43,f42])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f63,plain,(
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

fof(f67,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f7,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f51,f62,f62])).

cnf(c_21,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1092,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1519,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1088,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1523,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1096,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1515,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_2588,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1523,c_1515])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_355,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_356,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_358,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_29,c_26])).

cnf(c_441,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_358])).

cnf(c_442,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_442])).

cnf(c_489,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_491,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_493,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_26,c_491])).

cnf(c_1080,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_493])).

cnf(c_1529,plain,
    ( k2_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1080])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_82,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1101,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1691,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X1_50,X2_50)) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1924,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_2426,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1529,c_26,c_82,c_1080,c_1924])).

cnf(c_2590,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2588,c_2426])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f65])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_156,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_18])).

cnf(c_157,plain,
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
    inference(renaming,[status(thm)],[c_156])).

cnf(c_1085,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
    | ~ v1_funct_2(X3_50,X1_50,X0_50)
    | ~ v1_funct_2(X2_50,X0_50,X1_50)
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X2_50)
    | ~ v1_funct_1(X3_50)
    | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | k2_funct_1(X2_50) = X3_50
    | k1_xboole_0 = X0_50
    | k1_xboole_0 = X1_50 ),
    inference(subtyping,[status(esa)],[c_157])).

cnf(c_1526,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | k2_funct_1(X2_50) = X3_50
    | k1_xboole_0 = X0_50
    | k1_xboole_0 = X1_50
    | r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50)) != iProver_top
    | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(X3_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_3045,plain,
    ( k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2590,c_1526])).

cnf(c_30,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_33,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3286,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0_50
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3045,c_30,c_31,c_33])).

cnf(c_3287,plain,
    ( k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3286])).

cnf(c_3298,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_3287])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3299,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3298])).

cnf(c_3325,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3298,c_34,c_35,c_37])).

cnf(c_3326,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3325])).

cnf(c_20,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1093,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1518,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_374,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_375,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_377,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_29,c_28,c_26])).

cnf(c_1083,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_377])).

cnf(c_1554,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1518,c_1083])).

cnf(c_3329,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3326,c_1554])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1095,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1706,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_1707,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1706])).

cnf(c_3332,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3329,c_37,c_1707])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1099,plain,
    ( ~ v1_relat_1(X0_50)
    | v1_xboole_0(X0_50)
    | ~ v1_xboole_0(k2_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1514,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(k2_relat_1(X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_2498,plain,
    ( v1_relat_1(sK1) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2426,c_1514])).

cnf(c_81,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_83,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_1925,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_3119,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2498,c_33,c_83,c_1925])).

cnf(c_3337,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3332,c_3119])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_88,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1108,plain,
    ( ~ v1_xboole_0(X0_50)
    | v1_xboole_0(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1774,plain,
    ( v1_xboole_0(X0_50)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_50 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_1775,plain,
    ( X0_50 != k1_xboole_0
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_1777,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_4361,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3337,c_33,c_37,c_83,c_88,c_1707,c_1777,c_1925,c_2498,c_3329])).

cnf(c_1091,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1520,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1094,plain,
    ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | X3_50 = X2_50 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1517,plain,
    ( X0_50 = X1_50
    | r2_relset_1(X2_50,X3_50,X1_50,X0_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1094])).

cnf(c_2666,plain,
    ( sK1 = X0_50
    | r2_relset_1(sK0,sK0,sK1,X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_1517])).

cnf(c_2954,plain,
    ( sK1 = sK2
    | r2_relset_1(sK0,sK0,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_2666])).

cnf(c_3340,plain,
    ( sK1 = sK2
    | r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3332,c_2954])).

cnf(c_1776,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_1921,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_23,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_344,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_345,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_347,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_25,c_22])).

cnf(c_428,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_347])).

cnf(c_429,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_429])).

cnf(c_473,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_475,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_477,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_22,c_475])).

cnf(c_1081,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_1528,plain,
    ( k2_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_2090,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1528,c_22,c_82,c_1081,c_1921])).

cnf(c_2497,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2090,c_1514])).

cnf(c_2511,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2497])).

cnf(c_2512,plain,
    ( ~ v1_relat_1(sK1)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2498])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1102,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(X1_50)
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1803,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(sK2)
    | X0_50 = sK2 ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_3923,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK2)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_4178,plain,
    ( sK1 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3340,c_26,c_22,c_37,c_82,c_0,c_1707,c_1776,c_1921,c_1924,c_2511,c_2512,c_3329,c_3923])).

cnf(c_4365,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4361,c_4178])).

cnf(c_1103,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1510,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1103])).

cnf(c_1511,plain,
    ( X0_50 = X1_50
    | v1_xboole_0(X1_50) != iProver_top
    | v1_xboole_0(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1102])).

cnf(c_2433,plain,
    ( k1_xboole_0 = X0_50
    | v1_xboole_0(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1511])).

cnf(c_4368,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4365,c_2433])).

cnf(c_3348,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3332,c_1554])).

cnf(c_4181,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4178,c_3348])).

cnf(c_4382,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4368,c_4181])).

cnf(c_5,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1098,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_6,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1097,plain,
    ( k2_funct_1(k6_partfun1(X0_50)) = k6_partfun1(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1849,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1098,c_1097])).

cnf(c_1850,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1849,c_1098])).

cnf(c_4419,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4382,c_1850])).

cnf(c_1516,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1095])).

cnf(c_2652,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_1516])).

cnf(c_3345,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3332,c_2652])).

cnf(c_4387,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4368,c_3345])).

cnf(c_4421,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4419,c_4387])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:03:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.68/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.00  
% 2.68/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.68/1.00  
% 2.68/1.00  ------  iProver source info
% 2.68/1.00  
% 2.68/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.68/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.68/1.00  git: non_committed_changes: false
% 2.68/1.00  git: last_make_outside_of_git: false
% 2.68/1.00  
% 2.68/1.00  ------ 
% 2.68/1.00  
% 2.68/1.00  ------ Input Options
% 2.68/1.00  
% 2.68/1.00  --out_options                           all
% 2.68/1.00  --tptp_safe_out                         true
% 2.68/1.00  --problem_path                          ""
% 2.68/1.00  --include_path                          ""
% 2.68/1.00  --clausifier                            res/vclausify_rel
% 2.68/1.00  --clausifier_options                    --mode clausify
% 2.68/1.00  --stdin                                 false
% 2.68/1.00  --stats_out                             all
% 2.68/1.00  
% 2.68/1.00  ------ General Options
% 2.68/1.00  
% 2.68/1.00  --fof                                   false
% 2.68/1.00  --time_out_real                         305.
% 2.68/1.00  --time_out_virtual                      -1.
% 2.68/1.00  --symbol_type_check                     false
% 2.68/1.00  --clausify_out                          false
% 2.68/1.00  --sig_cnt_out                           false
% 2.68/1.00  --trig_cnt_out                          false
% 2.68/1.00  --trig_cnt_out_tolerance                1.
% 2.68/1.00  --trig_cnt_out_sk_spl                   false
% 2.68/1.00  --abstr_cl_out                          false
% 2.68/1.00  
% 2.68/1.00  ------ Global Options
% 2.68/1.00  
% 2.68/1.00  --schedule                              default
% 2.68/1.00  --add_important_lit                     false
% 2.68/1.00  --prop_solver_per_cl                    1000
% 2.68/1.00  --min_unsat_core                        false
% 2.68/1.00  --soft_assumptions                      false
% 2.68/1.00  --soft_lemma_size                       3
% 2.68/1.00  --prop_impl_unit_size                   0
% 2.68/1.00  --prop_impl_unit                        []
% 2.68/1.00  --share_sel_clauses                     true
% 2.68/1.00  --reset_solvers                         false
% 2.68/1.00  --bc_imp_inh                            [conj_cone]
% 2.68/1.00  --conj_cone_tolerance                   3.
% 2.68/1.00  --extra_neg_conj                        none
% 2.68/1.00  --large_theory_mode                     true
% 2.68/1.00  --prolific_symb_bound                   200
% 2.68/1.00  --lt_threshold                          2000
% 2.68/1.00  --clause_weak_htbl                      true
% 2.68/1.00  --gc_record_bc_elim                     false
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing Options
% 2.68/1.00  
% 2.68/1.00  --preprocessing_flag                    true
% 2.68/1.00  --time_out_prep_mult                    0.1
% 2.68/1.00  --splitting_mode                        input
% 2.68/1.00  --splitting_grd                         true
% 2.68/1.00  --splitting_cvd                         false
% 2.68/1.00  --splitting_cvd_svl                     false
% 2.68/1.00  --splitting_nvd                         32
% 2.68/1.00  --sub_typing                            true
% 2.68/1.00  --prep_gs_sim                           true
% 2.68/1.00  --prep_unflatten                        true
% 2.68/1.00  --prep_res_sim                          true
% 2.68/1.00  --prep_upred                            true
% 2.68/1.00  --prep_sem_filter                       exhaustive
% 2.68/1.00  --prep_sem_filter_out                   false
% 2.68/1.00  --pred_elim                             true
% 2.68/1.00  --res_sim_input                         true
% 2.68/1.00  --eq_ax_congr_red                       true
% 2.68/1.00  --pure_diseq_elim                       true
% 2.68/1.00  --brand_transform                       false
% 2.68/1.00  --non_eq_to_eq                          false
% 2.68/1.00  --prep_def_merge                        true
% 2.68/1.00  --prep_def_merge_prop_impl              false
% 2.68/1.00  --prep_def_merge_mbd                    true
% 2.68/1.00  --prep_def_merge_tr_red                 false
% 2.68/1.00  --prep_def_merge_tr_cl                  false
% 2.68/1.00  --smt_preprocessing                     true
% 2.68/1.00  --smt_ac_axioms                         fast
% 2.68/1.00  --preprocessed_out                      false
% 2.68/1.00  --preprocessed_stats                    false
% 2.68/1.00  
% 2.68/1.00  ------ Abstraction refinement Options
% 2.68/1.00  
% 2.68/1.00  --abstr_ref                             []
% 2.68/1.00  --abstr_ref_prep                        false
% 2.68/1.00  --abstr_ref_until_sat                   false
% 2.68/1.00  --abstr_ref_sig_restrict                funpre
% 2.68/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/1.00  --abstr_ref_under                       []
% 2.68/1.00  
% 2.68/1.00  ------ SAT Options
% 2.68/1.00  
% 2.68/1.00  --sat_mode                              false
% 2.68/1.00  --sat_fm_restart_options                ""
% 2.68/1.00  --sat_gr_def                            false
% 2.68/1.00  --sat_epr_types                         true
% 2.68/1.00  --sat_non_cyclic_types                  false
% 2.68/1.00  --sat_finite_models                     false
% 2.68/1.00  --sat_fm_lemmas                         false
% 2.68/1.00  --sat_fm_prep                           false
% 2.68/1.00  --sat_fm_uc_incr                        true
% 2.68/1.00  --sat_out_model                         small
% 2.68/1.00  --sat_out_clauses                       false
% 2.68/1.00  
% 2.68/1.00  ------ QBF Options
% 2.68/1.00  
% 2.68/1.00  --qbf_mode                              false
% 2.68/1.00  --qbf_elim_univ                         false
% 2.68/1.00  --qbf_dom_inst                          none
% 2.68/1.00  --qbf_dom_pre_inst                      false
% 2.68/1.00  --qbf_sk_in                             false
% 2.68/1.00  --qbf_pred_elim                         true
% 2.68/1.00  --qbf_split                             512
% 2.68/1.00  
% 2.68/1.00  ------ BMC1 Options
% 2.68/1.00  
% 2.68/1.00  --bmc1_incremental                      false
% 2.68/1.00  --bmc1_axioms                           reachable_all
% 2.68/1.00  --bmc1_min_bound                        0
% 2.68/1.00  --bmc1_max_bound                        -1
% 2.68/1.00  --bmc1_max_bound_default                -1
% 2.68/1.00  --bmc1_symbol_reachability              true
% 2.68/1.00  --bmc1_property_lemmas                  false
% 2.68/1.00  --bmc1_k_induction                      false
% 2.68/1.00  --bmc1_non_equiv_states                 false
% 2.68/1.00  --bmc1_deadlock                         false
% 2.68/1.00  --bmc1_ucm                              false
% 2.68/1.00  --bmc1_add_unsat_core                   none
% 2.68/1.00  --bmc1_unsat_core_children              false
% 2.68/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/1.00  --bmc1_out_stat                         full
% 2.68/1.00  --bmc1_ground_init                      false
% 2.68/1.00  --bmc1_pre_inst_next_state              false
% 2.68/1.00  --bmc1_pre_inst_state                   false
% 2.68/1.00  --bmc1_pre_inst_reach_state             false
% 2.68/1.00  --bmc1_out_unsat_core                   false
% 2.68/1.00  --bmc1_aig_witness_out                  false
% 2.68/1.00  --bmc1_verbose                          false
% 2.68/1.00  --bmc1_dump_clauses_tptp                false
% 2.68/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.68/1.00  --bmc1_dump_file                        -
% 2.68/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.68/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.68/1.00  --bmc1_ucm_extend_mode                  1
% 2.68/1.00  --bmc1_ucm_init_mode                    2
% 2.68/1.00  --bmc1_ucm_cone_mode                    none
% 2.68/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.68/1.00  --bmc1_ucm_relax_model                  4
% 2.68/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.68/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/1.00  --bmc1_ucm_layered_model                none
% 2.68/1.00  --bmc1_ucm_max_lemma_size               10
% 2.68/1.00  
% 2.68/1.00  ------ AIG Options
% 2.68/1.00  
% 2.68/1.00  --aig_mode                              false
% 2.68/1.00  
% 2.68/1.00  ------ Instantiation Options
% 2.68/1.00  
% 2.68/1.00  --instantiation_flag                    true
% 2.68/1.00  --inst_sos_flag                         false
% 2.68/1.00  --inst_sos_phase                        true
% 2.68/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/1.00  --inst_lit_sel_side                     num_symb
% 2.68/1.00  --inst_solver_per_active                1400
% 2.68/1.00  --inst_solver_calls_frac                1.
% 2.68/1.00  --inst_passive_queue_type               priority_queues
% 2.68/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/1.00  --inst_passive_queues_freq              [25;2]
% 2.68/1.00  --inst_dismatching                      true
% 2.68/1.00  --inst_eager_unprocessed_to_passive     true
% 2.68/1.00  --inst_prop_sim_given                   true
% 2.68/1.00  --inst_prop_sim_new                     false
% 2.68/1.00  --inst_subs_new                         false
% 2.68/1.00  --inst_eq_res_simp                      false
% 2.68/1.00  --inst_subs_given                       false
% 2.68/1.00  --inst_orphan_elimination               true
% 2.68/1.00  --inst_learning_loop_flag               true
% 2.68/1.00  --inst_learning_start                   3000
% 2.68/1.00  --inst_learning_factor                  2
% 2.68/1.00  --inst_start_prop_sim_after_learn       3
% 2.68/1.00  --inst_sel_renew                        solver
% 2.68/1.00  --inst_lit_activity_flag                true
% 2.68/1.00  --inst_restr_to_given                   false
% 2.68/1.00  --inst_activity_threshold               500
% 2.68/1.00  --inst_out_proof                        true
% 2.68/1.00  
% 2.68/1.00  ------ Resolution Options
% 2.68/1.00  
% 2.68/1.00  --resolution_flag                       true
% 2.68/1.00  --res_lit_sel                           adaptive
% 2.68/1.00  --res_lit_sel_side                      none
% 2.68/1.00  --res_ordering                          kbo
% 2.68/1.00  --res_to_prop_solver                    active
% 2.68/1.00  --res_prop_simpl_new                    false
% 2.68/1.00  --res_prop_simpl_given                  true
% 2.68/1.00  --res_passive_queue_type                priority_queues
% 2.68/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/1.00  --res_passive_queues_freq               [15;5]
% 2.68/1.00  --res_forward_subs                      full
% 2.68/1.00  --res_backward_subs                     full
% 2.68/1.00  --res_forward_subs_resolution           true
% 2.68/1.00  --res_backward_subs_resolution          true
% 2.68/1.00  --res_orphan_elimination                true
% 2.68/1.00  --res_time_limit                        2.
% 2.68/1.00  --res_out_proof                         true
% 2.68/1.00  
% 2.68/1.00  ------ Superposition Options
% 2.68/1.00  
% 2.68/1.00  --superposition_flag                    true
% 2.68/1.00  --sup_passive_queue_type                priority_queues
% 2.68/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.68/1.00  --demod_completeness_check              fast
% 2.68/1.00  --demod_use_ground                      true
% 2.68/1.00  --sup_to_prop_solver                    passive
% 2.68/1.00  --sup_prop_simpl_new                    true
% 2.68/1.00  --sup_prop_simpl_given                  true
% 2.68/1.00  --sup_fun_splitting                     false
% 2.68/1.00  --sup_smt_interval                      50000
% 2.68/1.00  
% 2.68/1.00  ------ Superposition Simplification Setup
% 2.68/1.00  
% 2.68/1.00  --sup_indices_passive                   []
% 2.68/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_full_bw                           [BwDemod]
% 2.68/1.00  --sup_immed_triv                        [TrivRules]
% 2.68/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_immed_bw_main                     []
% 2.68/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.00  
% 2.68/1.00  ------ Combination Options
% 2.68/1.00  
% 2.68/1.00  --comb_res_mult                         3
% 2.68/1.00  --comb_sup_mult                         2
% 2.68/1.00  --comb_inst_mult                        10
% 2.68/1.00  
% 2.68/1.00  ------ Debug Options
% 2.68/1.00  
% 2.68/1.00  --dbg_backtrace                         false
% 2.68/1.00  --dbg_dump_prop_clauses                 false
% 2.68/1.00  --dbg_dump_prop_clauses_file            -
% 2.68/1.00  --dbg_out_stat                          false
% 2.68/1.00  ------ Parsing...
% 2.68/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.68/1.00  ------ Proving...
% 2.68/1.00  ------ Problem Properties 
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  clauses                                 24
% 2.68/1.00  conjectures                             8
% 2.68/1.00  EPR                                     6
% 2.68/1.00  Horn                                    23
% 2.68/1.00  unary                                   14
% 2.68/1.00  binary                                  4
% 2.68/1.00  lits                                    55
% 2.68/1.00  lits eq                                 14
% 2.68/1.00  fd_pure                                 0
% 2.68/1.00  fd_pseudo                               0
% 2.68/1.00  fd_cond                                 0
% 2.68/1.00  fd_pseudo_cond                          4
% 2.68/1.00  AC symbols                              0
% 2.68/1.00  
% 2.68/1.00  ------ Schedule dynamic 5 is on 
% 2.68/1.00  
% 2.68/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  ------ 
% 2.68/1.00  Current options:
% 2.68/1.00  ------ 
% 2.68/1.00  
% 2.68/1.00  ------ Input Options
% 2.68/1.00  
% 2.68/1.00  --out_options                           all
% 2.68/1.00  --tptp_safe_out                         true
% 2.68/1.00  --problem_path                          ""
% 2.68/1.00  --include_path                          ""
% 2.68/1.00  --clausifier                            res/vclausify_rel
% 2.68/1.00  --clausifier_options                    --mode clausify
% 2.68/1.00  --stdin                                 false
% 2.68/1.00  --stats_out                             all
% 2.68/1.00  
% 2.68/1.00  ------ General Options
% 2.68/1.00  
% 2.68/1.00  --fof                                   false
% 2.68/1.00  --time_out_real                         305.
% 2.68/1.00  --time_out_virtual                      -1.
% 2.68/1.00  --symbol_type_check                     false
% 2.68/1.00  --clausify_out                          false
% 2.68/1.00  --sig_cnt_out                           false
% 2.68/1.00  --trig_cnt_out                          false
% 2.68/1.00  --trig_cnt_out_tolerance                1.
% 2.68/1.00  --trig_cnt_out_sk_spl                   false
% 2.68/1.00  --abstr_cl_out                          false
% 2.68/1.00  
% 2.68/1.00  ------ Global Options
% 2.68/1.00  
% 2.68/1.00  --schedule                              default
% 2.68/1.00  --add_important_lit                     false
% 2.68/1.00  --prop_solver_per_cl                    1000
% 2.68/1.00  --min_unsat_core                        false
% 2.68/1.00  --soft_assumptions                      false
% 2.68/1.00  --soft_lemma_size                       3
% 2.68/1.00  --prop_impl_unit_size                   0
% 2.68/1.00  --prop_impl_unit                        []
% 2.68/1.00  --share_sel_clauses                     true
% 2.68/1.00  --reset_solvers                         false
% 2.68/1.00  --bc_imp_inh                            [conj_cone]
% 2.68/1.00  --conj_cone_tolerance                   3.
% 2.68/1.00  --extra_neg_conj                        none
% 2.68/1.00  --large_theory_mode                     true
% 2.68/1.00  --prolific_symb_bound                   200
% 2.68/1.00  --lt_threshold                          2000
% 2.68/1.00  --clause_weak_htbl                      true
% 2.68/1.00  --gc_record_bc_elim                     false
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing Options
% 2.68/1.00  
% 2.68/1.00  --preprocessing_flag                    true
% 2.68/1.00  --time_out_prep_mult                    0.1
% 2.68/1.00  --splitting_mode                        input
% 2.68/1.00  --splitting_grd                         true
% 2.68/1.00  --splitting_cvd                         false
% 2.68/1.00  --splitting_cvd_svl                     false
% 2.68/1.00  --splitting_nvd                         32
% 2.68/1.00  --sub_typing                            true
% 2.68/1.00  --prep_gs_sim                           true
% 2.68/1.00  --prep_unflatten                        true
% 2.68/1.00  --prep_res_sim                          true
% 2.68/1.00  --prep_upred                            true
% 2.68/1.00  --prep_sem_filter                       exhaustive
% 2.68/1.00  --prep_sem_filter_out                   false
% 2.68/1.00  --pred_elim                             true
% 2.68/1.00  --res_sim_input                         true
% 2.68/1.00  --eq_ax_congr_red                       true
% 2.68/1.00  --pure_diseq_elim                       true
% 2.68/1.00  --brand_transform                       false
% 2.68/1.00  --non_eq_to_eq                          false
% 2.68/1.00  --prep_def_merge                        true
% 2.68/1.00  --prep_def_merge_prop_impl              false
% 2.68/1.00  --prep_def_merge_mbd                    true
% 2.68/1.00  --prep_def_merge_tr_red                 false
% 2.68/1.00  --prep_def_merge_tr_cl                  false
% 2.68/1.00  --smt_preprocessing                     true
% 2.68/1.00  --smt_ac_axioms                         fast
% 2.68/1.00  --preprocessed_out                      false
% 2.68/1.00  --preprocessed_stats                    false
% 2.68/1.00  
% 2.68/1.00  ------ Abstraction refinement Options
% 2.68/1.00  
% 2.68/1.00  --abstr_ref                             []
% 2.68/1.00  --abstr_ref_prep                        false
% 2.68/1.00  --abstr_ref_until_sat                   false
% 2.68/1.00  --abstr_ref_sig_restrict                funpre
% 2.68/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/1.00  --abstr_ref_under                       []
% 2.68/1.00  
% 2.68/1.00  ------ SAT Options
% 2.68/1.00  
% 2.68/1.00  --sat_mode                              false
% 2.68/1.00  --sat_fm_restart_options                ""
% 2.68/1.00  --sat_gr_def                            false
% 2.68/1.00  --sat_epr_types                         true
% 2.68/1.00  --sat_non_cyclic_types                  false
% 2.68/1.00  --sat_finite_models                     false
% 2.68/1.00  --sat_fm_lemmas                         false
% 2.68/1.00  --sat_fm_prep                           false
% 2.68/1.00  --sat_fm_uc_incr                        true
% 2.68/1.00  --sat_out_model                         small
% 2.68/1.00  --sat_out_clauses                       false
% 2.68/1.00  
% 2.68/1.00  ------ QBF Options
% 2.68/1.00  
% 2.68/1.00  --qbf_mode                              false
% 2.68/1.00  --qbf_elim_univ                         false
% 2.68/1.00  --qbf_dom_inst                          none
% 2.68/1.00  --qbf_dom_pre_inst                      false
% 2.68/1.00  --qbf_sk_in                             false
% 2.68/1.00  --qbf_pred_elim                         true
% 2.68/1.00  --qbf_split                             512
% 2.68/1.00  
% 2.68/1.00  ------ BMC1 Options
% 2.68/1.00  
% 2.68/1.00  --bmc1_incremental                      false
% 2.68/1.00  --bmc1_axioms                           reachable_all
% 2.68/1.00  --bmc1_min_bound                        0
% 2.68/1.00  --bmc1_max_bound                        -1
% 2.68/1.00  --bmc1_max_bound_default                -1
% 2.68/1.00  --bmc1_symbol_reachability              true
% 2.68/1.00  --bmc1_property_lemmas                  false
% 2.68/1.00  --bmc1_k_induction                      false
% 2.68/1.00  --bmc1_non_equiv_states                 false
% 2.68/1.00  --bmc1_deadlock                         false
% 2.68/1.00  --bmc1_ucm                              false
% 2.68/1.00  --bmc1_add_unsat_core                   none
% 2.68/1.00  --bmc1_unsat_core_children              false
% 2.68/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/1.00  --bmc1_out_stat                         full
% 2.68/1.00  --bmc1_ground_init                      false
% 2.68/1.00  --bmc1_pre_inst_next_state              false
% 2.68/1.00  --bmc1_pre_inst_state                   false
% 2.68/1.00  --bmc1_pre_inst_reach_state             false
% 2.68/1.00  --bmc1_out_unsat_core                   false
% 2.68/1.00  --bmc1_aig_witness_out                  false
% 2.68/1.00  --bmc1_verbose                          false
% 2.68/1.00  --bmc1_dump_clauses_tptp                false
% 2.68/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.68/1.00  --bmc1_dump_file                        -
% 2.68/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.68/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.68/1.00  --bmc1_ucm_extend_mode                  1
% 2.68/1.00  --bmc1_ucm_init_mode                    2
% 2.68/1.00  --bmc1_ucm_cone_mode                    none
% 2.68/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.68/1.00  --bmc1_ucm_relax_model                  4
% 2.68/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.68/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/1.00  --bmc1_ucm_layered_model                none
% 2.68/1.00  --bmc1_ucm_max_lemma_size               10
% 2.68/1.00  
% 2.68/1.00  ------ AIG Options
% 2.68/1.00  
% 2.68/1.00  --aig_mode                              false
% 2.68/1.00  
% 2.68/1.00  ------ Instantiation Options
% 2.68/1.00  
% 2.68/1.00  --instantiation_flag                    true
% 2.68/1.00  --inst_sos_flag                         false
% 2.68/1.00  --inst_sos_phase                        true
% 2.68/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/1.00  --inst_lit_sel_side                     none
% 2.68/1.00  --inst_solver_per_active                1400
% 2.68/1.00  --inst_solver_calls_frac                1.
% 2.68/1.00  --inst_passive_queue_type               priority_queues
% 2.68/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/1.00  --inst_passive_queues_freq              [25;2]
% 2.68/1.00  --inst_dismatching                      true
% 2.68/1.00  --inst_eager_unprocessed_to_passive     true
% 2.68/1.00  --inst_prop_sim_given                   true
% 2.68/1.00  --inst_prop_sim_new                     false
% 2.68/1.00  --inst_subs_new                         false
% 2.68/1.00  --inst_eq_res_simp                      false
% 2.68/1.00  --inst_subs_given                       false
% 2.68/1.00  --inst_orphan_elimination               true
% 2.68/1.00  --inst_learning_loop_flag               true
% 2.68/1.00  --inst_learning_start                   3000
% 2.68/1.00  --inst_learning_factor                  2
% 2.68/1.00  --inst_start_prop_sim_after_learn       3
% 2.68/1.00  --inst_sel_renew                        solver
% 2.68/1.00  --inst_lit_activity_flag                true
% 2.68/1.00  --inst_restr_to_given                   false
% 2.68/1.00  --inst_activity_threshold               500
% 2.68/1.00  --inst_out_proof                        true
% 2.68/1.00  
% 2.68/1.00  ------ Resolution Options
% 2.68/1.00  
% 2.68/1.00  --resolution_flag                       false
% 2.68/1.00  --res_lit_sel                           adaptive
% 2.68/1.00  --res_lit_sel_side                      none
% 2.68/1.00  --res_ordering                          kbo
% 2.68/1.00  --res_to_prop_solver                    active
% 2.68/1.00  --res_prop_simpl_new                    false
% 2.68/1.00  --res_prop_simpl_given                  true
% 2.68/1.00  --res_passive_queue_type                priority_queues
% 2.68/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/1.00  --res_passive_queues_freq               [15;5]
% 2.68/1.00  --res_forward_subs                      full
% 2.68/1.00  --res_backward_subs                     full
% 2.68/1.00  --res_forward_subs_resolution           true
% 2.68/1.00  --res_backward_subs_resolution          true
% 2.68/1.00  --res_orphan_elimination                true
% 2.68/1.00  --res_time_limit                        2.
% 2.68/1.00  --res_out_proof                         true
% 2.68/1.00  
% 2.68/1.00  ------ Superposition Options
% 2.68/1.00  
% 2.68/1.00  --superposition_flag                    true
% 2.68/1.00  --sup_passive_queue_type                priority_queues
% 2.68/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.68/1.00  --demod_completeness_check              fast
% 2.68/1.00  --demod_use_ground                      true
% 2.68/1.00  --sup_to_prop_solver                    passive
% 2.68/1.00  --sup_prop_simpl_new                    true
% 2.68/1.00  --sup_prop_simpl_given                  true
% 2.68/1.00  --sup_fun_splitting                     false
% 2.68/1.00  --sup_smt_interval                      50000
% 2.68/1.00  
% 2.68/1.00  ------ Superposition Simplification Setup
% 2.68/1.00  
% 2.68/1.00  --sup_indices_passive                   []
% 2.68/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_full_bw                           [BwDemod]
% 2.68/1.00  --sup_immed_triv                        [TrivRules]
% 2.68/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_immed_bw_main                     []
% 2.68/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.00  
% 2.68/1.00  ------ Combination Options
% 2.68/1.00  
% 2.68/1.00  --comb_res_mult                         3
% 2.68/1.00  --comb_sup_mult                         2
% 2.68/1.00  --comb_inst_mult                        10
% 2.68/1.00  
% 2.68/1.00  ------ Debug Options
% 2.68/1.00  
% 2.68/1.00  --dbg_backtrace                         false
% 2.68/1.00  --dbg_dump_prop_clauses                 false
% 2.68/1.00  --dbg_dump_prop_clauses_file            -
% 2.68/1.00  --dbg_out_stat                          false
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  ------ Proving...
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  % SZS status Theorem for theBenchmark.p
% 2.68/1.00  
% 2.68/1.00   Resolution empty clause
% 2.68/1.00  
% 2.68/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.68/1.00  
% 2.68/1.00  fof(f17,conjecture,(
% 2.68/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f18,negated_conjecture,(
% 2.68/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.68/1.00    inference(negated_conjecture,[],[f17])).
% 2.68/1.00  
% 2.68/1.00  fof(f38,plain,(
% 2.68/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.68/1.00    inference(ennf_transformation,[],[f18])).
% 2.68/1.00  
% 2.68/1.00  fof(f39,plain,(
% 2.68/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.68/1.00    inference(flattening,[],[f38])).
% 2.68/1.00  
% 2.68/1.00  fof(f43,plain,(
% 2.68/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 2.68/1.00    introduced(choice_axiom,[])).
% 2.68/1.00  
% 2.68/1.00  fof(f42,plain,(
% 2.68/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.68/1.00    introduced(choice_axiom,[])).
% 2.68/1.00  
% 2.68/1.00  fof(f44,plain,(
% 2.68/1.00    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.68/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f43,f42])).
% 2.68/1.00  
% 2.68/1.00  fof(f74,plain,(
% 2.68/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f69,plain,(
% 2.68/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f9,axiom,(
% 2.68/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f25,plain,(
% 2.68/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.00    inference(ennf_transformation,[],[f9])).
% 2.68/1.00  
% 2.68/1.00  fof(f53,plain,(
% 2.68/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f25])).
% 2.68/1.00  
% 2.68/1.00  fof(f8,axiom,(
% 2.68/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f19,plain,(
% 2.68/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.68/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.68/1.00  
% 2.68/1.00  fof(f24,plain,(
% 2.68/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.00    inference(ennf_transformation,[],[f19])).
% 2.68/1.00  
% 2.68/1.00  fof(f52,plain,(
% 2.68/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f24])).
% 2.68/1.00  
% 2.68/1.00  fof(f12,axiom,(
% 2.68/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f30,plain,(
% 2.68/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.68/1.00    inference(ennf_transformation,[],[f12])).
% 2.68/1.00  
% 2.68/1.00  fof(f31,plain,(
% 2.68/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.68/1.00    inference(flattening,[],[f30])).
% 2.68/1.00  
% 2.68/1.00  fof(f41,plain,(
% 2.68/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.68/1.00    inference(nnf_transformation,[],[f31])).
% 2.68/1.00  
% 2.68/1.00  fof(f59,plain,(
% 2.68/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f41])).
% 2.68/1.00  
% 2.68/1.00  fof(f11,axiom,(
% 2.68/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f28,plain,(
% 2.68/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.00    inference(ennf_transformation,[],[f11])).
% 2.68/1.00  
% 2.68/1.00  fof(f29,plain,(
% 2.68/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.00    inference(flattening,[],[f28])).
% 2.68/1.00  
% 2.68/1.00  fof(f58,plain,(
% 2.68/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f29])).
% 2.68/1.00  
% 2.68/1.00  fof(f68,plain,(
% 2.68/1.00    v3_funct_2(sK1,sK0,sK0)),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f66,plain,(
% 2.68/1.00    v1_funct_1(sK1)),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f4,axiom,(
% 2.68/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f48,plain,(
% 2.68/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f4])).
% 2.68/1.00  
% 2.68/1.00  fof(f3,axiom,(
% 2.68/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f21,plain,(
% 2.68/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.68/1.00    inference(ennf_transformation,[],[f3])).
% 2.68/1.00  
% 2.68/1.00  fof(f47,plain,(
% 2.68/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f21])).
% 2.68/1.00  
% 2.68/1.00  fof(f16,axiom,(
% 2.68/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f36,plain,(
% 2.68/1.00    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.68/1.00    inference(ennf_transformation,[],[f16])).
% 2.68/1.00  
% 2.68/1.00  fof(f37,plain,(
% 2.68/1.00    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.68/1.00    inference(flattening,[],[f36])).
% 2.68/1.00  
% 2.68/1.00  fof(f65,plain,(
% 2.68/1.00    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f37])).
% 2.68/1.00  
% 2.68/1.00  fof(f15,axiom,(
% 2.68/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f34,plain,(
% 2.68/1.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.68/1.00    inference(ennf_transformation,[],[f15])).
% 2.68/1.00  
% 2.68/1.00  fof(f35,plain,(
% 2.68/1.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.68/1.00    inference(flattening,[],[f34])).
% 2.68/1.00  
% 2.68/1.00  fof(f63,plain,(
% 2.68/1.00    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f35])).
% 2.68/1.00  
% 2.68/1.00  fof(f67,plain,(
% 2.68/1.00    v1_funct_2(sK1,sK0,sK0)),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f70,plain,(
% 2.68/1.00    v1_funct_1(sK2)),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f71,plain,(
% 2.68/1.00    v1_funct_2(sK2,sK0,sK0)),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f73,plain,(
% 2.68/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f75,plain,(
% 2.68/1.00    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f13,axiom,(
% 2.68/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f32,plain,(
% 2.68/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.68/1.00    inference(ennf_transformation,[],[f13])).
% 2.68/1.00  
% 2.68/1.00  fof(f33,plain,(
% 2.68/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.68/1.00    inference(flattening,[],[f32])).
% 2.68/1.00  
% 2.68/1.00  fof(f61,plain,(
% 2.68/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f33])).
% 2.68/1.00  
% 2.68/1.00  fof(f10,axiom,(
% 2.68/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f26,plain,(
% 2.68/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.68/1.00    inference(ennf_transformation,[],[f10])).
% 2.68/1.00  
% 2.68/1.00  fof(f27,plain,(
% 2.68/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.00    inference(flattening,[],[f26])).
% 2.68/1.00  
% 2.68/1.00  fof(f40,plain,(
% 2.68/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.00    inference(nnf_transformation,[],[f27])).
% 2.68/1.00  
% 2.68/1.00  fof(f55,plain,(
% 2.68/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f40])).
% 2.68/1.00  
% 2.68/1.00  fof(f78,plain,(
% 2.68/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.00    inference(equality_resolution,[],[f55])).
% 2.68/1.00  
% 2.68/1.00  fof(f5,axiom,(
% 2.68/1.00    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f22,plain,(
% 2.68/1.00    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 2.68/1.00    inference(ennf_transformation,[],[f5])).
% 2.68/1.00  
% 2.68/1.00  fof(f23,plain,(
% 2.68/1.00    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 2.68/1.00    inference(flattening,[],[f22])).
% 2.68/1.00  
% 2.68/1.00  fof(f49,plain,(
% 2.68/1.00    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f23])).
% 2.68/1.00  
% 2.68/1.00  fof(f1,axiom,(
% 2.68/1.00    v1_xboole_0(k1_xboole_0)),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f45,plain,(
% 2.68/1.00    v1_xboole_0(k1_xboole_0)),
% 2.68/1.00    inference(cnf_transformation,[],[f1])).
% 2.68/1.00  
% 2.68/1.00  fof(f54,plain,(
% 2.68/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f40])).
% 2.68/1.00  
% 2.68/1.00  fof(f72,plain,(
% 2.68/1.00    v3_funct_2(sK2,sK0,sK0)),
% 2.68/1.00    inference(cnf_transformation,[],[f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f2,axiom,(
% 2.68/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f20,plain,(
% 2.68/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.68/1.00    inference(ennf_transformation,[],[f2])).
% 2.68/1.00  
% 2.68/1.00  fof(f46,plain,(
% 2.68/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f20])).
% 2.68/1.00  
% 2.68/1.00  fof(f6,axiom,(
% 2.68/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f50,plain,(
% 2.68/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.68/1.00    inference(cnf_transformation,[],[f6])).
% 2.68/1.00  
% 2.68/1.00  fof(f14,axiom,(
% 2.68/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f62,plain,(
% 2.68/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f14])).
% 2.68/1.00  
% 2.68/1.00  fof(f76,plain,(
% 2.68/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.68/1.00    inference(definition_unfolding,[],[f50,f62])).
% 2.68/1.00  
% 2.68/1.00  fof(f7,axiom,(
% 2.68/1.00    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.68/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f51,plain,(
% 2.68/1.00    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f7])).
% 2.68/1.00  
% 2.68/1.00  fof(f77,plain,(
% 2.68/1.00    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 2.68/1.00    inference(definition_unfolding,[],[f51,f62,f62])).
% 2.68/1.00  
% 2.68/1.00  cnf(c_21,negated_conjecture,
% 2.68/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 2.68/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1092,negated_conjecture,
% 2.68/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1519,plain,
% 2.68/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1092]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_26,negated_conjecture,
% 2.68/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.68/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1088,negated_conjecture,
% 2.68/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1523,plain,
% 2.68/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1088]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_8,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1096,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.68/1.00      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1515,plain,
% 2.68/1.00      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 2.68/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2588,plain,
% 2.68/1.00      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1523,c_1515]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_7,plain,
% 2.68/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.68/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_15,plain,
% 2.68/1.00      ( ~ v2_funct_2(X0,X1)
% 2.68/1.00      | ~ v5_relat_1(X0,X1)
% 2.68/1.00      | ~ v1_relat_1(X0)
% 2.68/1.00      | k2_relat_1(X0) = X1 ),
% 2.68/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_11,plain,
% 2.68/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.68/1.00      | v2_funct_2(X0,X2)
% 2.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/1.00      | ~ v1_funct_1(X0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_27,negated_conjecture,
% 2.68/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_355,plain,
% 2.68/1.00      ( v2_funct_2(X0,X1)
% 2.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.68/1.00      | ~ v1_funct_1(X0)
% 2.68/1.00      | sK1 != X0
% 2.68/1.00      | sK0 != X1
% 2.68/1.00      | sK0 != X2 ),
% 2.68/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_356,plain,
% 2.68/1.00      ( v2_funct_2(sK1,sK0)
% 2.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.68/1.00      | ~ v1_funct_1(sK1) ),
% 2.68/1.00      inference(unflattening,[status(thm)],[c_355]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_29,negated_conjecture,
% 2.68/1.00      ( v1_funct_1(sK1) ),
% 2.68/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_358,plain,
% 2.68/1.00      ( v2_funct_2(sK1,sK0) ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_356,c_29,c_26]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_441,plain,
% 2.68/1.00      ( ~ v5_relat_1(X0,X1)
% 2.68/1.00      | ~ v1_relat_1(X0)
% 2.68/1.00      | k2_relat_1(X0) = X1
% 2.68/1.00      | sK1 != X0
% 2.68/1.00      | sK0 != X1 ),
% 2.68/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_358]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_442,plain,
% 2.68/1.00      ( ~ v5_relat_1(sK1,sK0) | ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 2.68/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_488,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/1.00      | ~ v1_relat_1(sK1)
% 2.68/1.00      | k2_relat_1(sK1) = sK0
% 2.68/1.00      | sK1 != X0
% 2.68/1.00      | sK0 != X2 ),
% 2.68/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_442]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_489,plain,
% 2.68/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 2.68/1.00      | ~ v1_relat_1(sK1)
% 2.68/1.00      | k2_relat_1(sK1) = sK0 ),
% 2.68/1.00      inference(unflattening,[status(thm)],[c_488]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_491,plain,
% 2.68/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.68/1.00      | ~ v1_relat_1(sK1)
% 2.68/1.00      | k2_relat_1(sK1) = sK0 ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_489]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_493,plain,
% 2.68/1.00      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_489,c_26,c_491]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1080,plain,
% 2.68/1.00      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_493]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1529,plain,
% 2.68/1.00      ( k2_relat_1(sK1) = sK0 | v1_relat_1(sK1) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1080]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3,plain,
% 2.68/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.68/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_82,plain,
% 2.68/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1101,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.68/1.00      | ~ v1_relat_1(X1_50)
% 2.68/1.00      | v1_relat_1(X0_50) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1691,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.68/1.00      | v1_relat_1(X0_50)
% 2.68/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1_50,X2_50)) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1101]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1924,plain,
% 2.68/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.68/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 2.68/1.00      | v1_relat_1(sK1) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1691]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2426,plain,
% 2.68/1.00      ( k2_relat_1(sK1) = sK0 ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_1529,c_26,c_82,c_1080,c_1924]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2590,plain,
% 2.68/1.00      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.68/1.00      inference(light_normalisation,[status(thm)],[c_2588,c_2426]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_19,plain,
% 2.68/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.68/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.68/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.68/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.68/1.00      | ~ v2_funct_1(X2)
% 2.68/1.00      | ~ v1_funct_1(X2)
% 2.68/1.00      | ~ v1_funct_1(X3)
% 2.68/1.00      | k2_relset_1(X0,X1,X2) != X1
% 2.68/1.00      | k2_funct_1(X2) = X3
% 2.68/1.00      | k1_xboole_0 = X1
% 2.68/1.00      | k1_xboole_0 = X0 ),
% 2.68/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_18,plain,
% 2.68/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.68/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.68/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.68/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.68/1.00      | v2_funct_1(X2)
% 2.68/1.00      | ~ v1_funct_1(X2)
% 2.68/1.00      | ~ v1_funct_1(X3) ),
% 2.68/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_156,plain,
% 2.68/1.00      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.68/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.68/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.68/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.68/1.00      | ~ v1_funct_1(X2)
% 2.68/1.00      | ~ v1_funct_1(X3)
% 2.68/1.00      | k2_relset_1(X0,X1,X2) != X1
% 2.68/1.00      | k2_funct_1(X2) = X3
% 2.68/1.00      | k1_xboole_0 = X1
% 2.68/1.00      | k1_xboole_0 = X0 ),
% 2.68/1.00      inference(global_propositional_subsumption,[status(thm)],[c_19,c_18]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_157,plain,
% 2.68/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.68/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.68/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.68/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.68/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/1.00      | ~ v1_funct_1(X2)
% 2.68/1.00      | ~ v1_funct_1(X3)
% 2.68/1.00      | k2_relset_1(X0,X1,X2) != X1
% 2.68/1.00      | k2_funct_1(X2) = X3
% 2.68/1.00      | k1_xboole_0 = X0
% 2.68/1.00      | k1_xboole_0 = X1 ),
% 2.68/1.00      inference(renaming,[status(thm)],[c_156]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1085,plain,
% 2.68/1.00      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
% 2.68/1.00      | ~ v1_funct_2(X3_50,X1_50,X0_50)
% 2.68/1.00      | ~ v1_funct_2(X2_50,X0_50,X1_50)
% 2.68/1.00      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 2.68/1.00      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.68/1.00      | ~ v1_funct_1(X2_50)
% 2.68/1.00      | ~ v1_funct_1(X3_50)
% 2.68/1.00      | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 2.68/1.00      | k2_funct_1(X2_50) = X3_50
% 2.68/1.00      | k1_xboole_0 = X0_50
% 2.68/1.00      | k1_xboole_0 = X1_50 ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_157]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1526,plain,
% 2.68/1.00      ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 2.68/1.00      | k2_funct_1(X2_50) = X3_50
% 2.68/1.00      | k1_xboole_0 = X0_50
% 2.68/1.00      | k1_xboole_0 = X1_50
% 2.68/1.00      | r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50)) != iProver_top
% 2.68/1.00      | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
% 2.68/1.00      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 2.68/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.68/1.00      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 2.68/1.00      | v1_funct_1(X2_50) != iProver_top
% 2.68/1.00      | v1_funct_1(X3_50) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3045,plain,
% 2.68/1.00      ( k2_funct_1(sK1) = X0_50
% 2.68/1.00      | sK0 = k1_xboole_0
% 2.68/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 2.68/1.00      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 2.68/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.68/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.68/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.68/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.68/1.00      | v1_funct_1(sK1) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_2590,c_1526]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_30,plain,
% 2.68/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_28,negated_conjecture,
% 2.68/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_31,plain,
% 2.68/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_33,plain,
% 2.68/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3286,plain,
% 2.68/1.00      ( v1_funct_1(X0_50) != iProver_top
% 2.68/1.00      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 2.68/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 2.68/1.00      | sK0 = k1_xboole_0
% 2.68/1.00      | k2_funct_1(sK1) = X0_50
% 2.68/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_3045,c_30,c_31,c_33]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3287,plain,
% 2.68/1.00      ( k2_funct_1(sK1) = X0_50
% 2.68/1.00      | sK0 = k1_xboole_0
% 2.68/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 2.68/1.00      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 2.68/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.68/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.68/1.00      inference(renaming,[status(thm)],[c_3286]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3298,plain,
% 2.68/1.00      ( k2_funct_1(sK1) = sK2
% 2.68/1.00      | sK0 = k1_xboole_0
% 2.68/1.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.68/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.68/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1519,c_3287]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_25,negated_conjecture,
% 2.68/1.00      ( v1_funct_1(sK2) ),
% 2.68/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_24,negated_conjecture,
% 2.68/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_22,negated_conjecture,
% 2.68/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.68/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3299,plain,
% 2.68/1.00      ( ~ v1_funct_2(sK2,sK0,sK0)
% 2.68/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.68/1.00      | ~ v1_funct_1(sK2)
% 2.68/1.00      | k2_funct_1(sK1) = sK2
% 2.68/1.00      | sK0 = k1_xboole_0 ),
% 2.68/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3298]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3325,plain,
% 2.68/1.00      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_3298,c_34,c_35,c_37]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3326,plain,
% 2.68/1.00      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 2.68/1.00      inference(renaming,[status(thm)],[c_3325]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_20,negated_conjecture,
% 2.68/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 2.68/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1093,negated_conjecture,
% 2.68/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1518,plain,
% 2.68/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1093]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_16,plain,
% 2.68/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.68/1.00      | ~ v3_funct_2(X0,X1,X1)
% 2.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.68/1.00      | ~ v1_funct_1(X0)
% 2.68/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_374,plain,
% 2.68/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.68/1.00      | ~ v1_funct_1(X0)
% 2.68/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 2.68/1.00      | sK1 != X0
% 2.68/1.00      | sK0 != X1 ),
% 2.68/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_375,plain,
% 2.68/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 2.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.68/1.00      | ~ v1_funct_1(sK1)
% 2.68/1.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.68/1.00      inference(unflattening,[status(thm)],[c_374]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_377,plain,
% 2.68/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_375,c_29,c_28,c_26]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1083,plain,
% 2.68/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_377]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1554,plain,
% 2.68/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 2.68/1.00      inference(light_normalisation,[status(thm)],[c_1518,c_1083]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3329,plain,
% 2.68/1.00      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_3326,c_1554]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_37,plain,
% 2.68/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_9,plain,
% 2.68/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.68/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.68/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1095,plain,
% 2.68/1.00      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
% 2.68/1.00      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1706,plain,
% 2.68/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 2.68/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1095]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1707,plain,
% 2.68/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 2.68/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1706]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3332,plain,
% 2.68/1.00      ( sK0 = k1_xboole_0 ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_3329,c_37,c_1707]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4,plain,
% 2.68/1.00      ( ~ v1_relat_1(X0) | v1_xboole_0(X0) | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 2.68/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1099,plain,
% 2.68/1.00      ( ~ v1_relat_1(X0_50)
% 2.68/1.00      | v1_xboole_0(X0_50)
% 2.68/1.00      | ~ v1_xboole_0(k2_relat_1(X0_50)) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1514,plain,
% 2.68/1.00      ( v1_relat_1(X0_50) != iProver_top
% 2.68/1.00      | v1_xboole_0(X0_50) = iProver_top
% 2.68/1.00      | v1_xboole_0(k2_relat_1(X0_50)) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1099]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2498,plain,
% 2.68/1.00      ( v1_relat_1(sK1) != iProver_top
% 2.68/1.00      | v1_xboole_0(sK1) = iProver_top
% 2.68/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_2426,c_1514]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_81,plain,
% 2.68/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_83,plain,
% 2.68/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_81]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1925,plain,
% 2.68/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.68/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 2.68/1.00      | v1_relat_1(sK1) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3119,plain,
% 2.68/1.00      ( v1_xboole_0(sK1) = iProver_top | v1_xboole_0(sK0) != iProver_top ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_2498,c_33,c_83,c_1925]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3337,plain,
% 2.68/1.00      ( v1_xboole_0(sK1) = iProver_top
% 2.68/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.68/1.00      inference(demodulation,[status(thm)],[c_3332,c_3119]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_0,plain,
% 2.68/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_88,plain,
% 2.68/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1108,plain,
% 2.68/1.00      ( ~ v1_xboole_0(X0_50) | v1_xboole_0(X1_50) | X1_50 != X0_50 ),
% 2.68/1.00      theory(equality) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1774,plain,
% 2.68/1.00      ( v1_xboole_0(X0_50)
% 2.68/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.68/1.00      | X0_50 != k1_xboole_0 ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1108]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1775,plain,
% 2.68/1.00      ( X0_50 != k1_xboole_0
% 2.68/1.00      | v1_xboole_0(X0_50) = iProver_top
% 2.68/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1777,plain,
% 2.68/1.00      ( sK0 != k1_xboole_0
% 2.68/1.00      | v1_xboole_0(sK0) = iProver_top
% 2.68/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1775]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4361,plain,
% 2.68/1.00      ( v1_xboole_0(sK1) = iProver_top ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_3337,c_33,c_37,c_83,c_88,c_1707,c_1777,c_1925,c_2498,c_3329]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1091,negated_conjecture,
% 2.68/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1520,plain,
% 2.68/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1091]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_10,plain,
% 2.68/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.68/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/1.00      | X3 = X2 ),
% 2.68/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1094,plain,
% 2.68/1.00      ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
% 2.68/1.00      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.68/1.00      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.68/1.00      | X3_50 = X2_50 ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1517,plain,
% 2.68/1.00      ( X0_50 = X1_50
% 2.68/1.00      | r2_relset_1(X2_50,X3_50,X1_50,X0_50) != iProver_top
% 2.68/1.00      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 2.68/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1094]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2666,plain,
% 2.68/1.00      ( sK1 = X0_50
% 2.68/1.00      | r2_relset_1(sK0,sK0,sK1,X0_50) != iProver_top
% 2.68/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1523,c_1517]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2954,plain,
% 2.68/1.00      ( sK1 = sK2 | r2_relset_1(sK0,sK0,sK1,sK2) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1520,c_2666]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3340,plain,
% 2.68/1.00      ( sK1 = sK2
% 2.68/1.00      | r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK2) != iProver_top ),
% 2.68/1.00      inference(demodulation,[status(thm)],[c_3332,c_2954]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1776,plain,
% 2.68/1.00      ( v1_xboole_0(sK0) | ~ v1_xboole_0(k1_xboole_0) | sK0 != k1_xboole_0 ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1774]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1921,plain,
% 2.68/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.68/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 2.68/1.00      | v1_relat_1(sK2) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1691]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_23,negated_conjecture,
% 2.68/1.00      ( v3_funct_2(sK2,sK0,sK0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_344,plain,
% 2.68/1.00      ( v2_funct_2(X0,X1)
% 2.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.68/1.00      | ~ v1_funct_1(X0)
% 2.68/1.00      | sK2 != X0
% 2.68/1.00      | sK0 != X1
% 2.68/1.00      | sK0 != X2 ),
% 2.68/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_345,plain,
% 2.68/1.00      ( v2_funct_2(sK2,sK0)
% 2.68/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.68/1.00      | ~ v1_funct_1(sK2) ),
% 2.68/1.00      inference(unflattening,[status(thm)],[c_344]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_347,plain,
% 2.68/1.00      ( v2_funct_2(sK2,sK0) ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_345,c_25,c_22]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_428,plain,
% 2.68/1.00      ( ~ v5_relat_1(X0,X1)
% 2.68/1.00      | ~ v1_relat_1(X0)
% 2.68/1.00      | k2_relat_1(X0) = X1
% 2.68/1.00      | sK2 != X0
% 2.68/1.00      | sK0 != X1 ),
% 2.68/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_347]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_429,plain,
% 2.68/1.00      ( ~ v5_relat_1(sK2,sK0) | ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK0 ),
% 2.68/1.00      inference(unflattening,[status(thm)],[c_428]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_472,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/1.00      | ~ v1_relat_1(sK2)
% 2.68/1.00      | k2_relat_1(sK2) = sK0
% 2.68/1.00      | sK2 != X0
% 2.68/1.00      | sK0 != X2 ),
% 2.68/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_429]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_473,plain,
% 2.68/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 2.68/1.00      | ~ v1_relat_1(sK2)
% 2.68/1.00      | k2_relat_1(sK2) = sK0 ),
% 2.68/1.00      inference(unflattening,[status(thm)],[c_472]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_475,plain,
% 2.68/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.68/1.00      | ~ v1_relat_1(sK2)
% 2.68/1.00      | k2_relat_1(sK2) = sK0 ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_473]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_477,plain,
% 2.68/1.00      ( ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK0 ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_473,c_22,c_475]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1081,plain,
% 2.68/1.00      ( ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK0 ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_477]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1528,plain,
% 2.68/1.00      ( k2_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2090,plain,
% 2.68/1.00      ( k2_relat_1(sK2) = sK0 ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_1528,c_22,c_82,c_1081,c_1921]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2497,plain,
% 2.68/1.00      ( v1_relat_1(sK2) != iProver_top
% 2.68/1.00      | v1_xboole_0(sK2) = iProver_top
% 2.68/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_2090,c_1514]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2511,plain,
% 2.68/1.00      ( ~ v1_relat_1(sK2) | v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 2.68/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2497]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2512,plain,
% 2.68/1.00      ( ~ v1_relat_1(sK1) | v1_xboole_0(sK1) | ~ v1_xboole_0(sK0) ),
% 2.68/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2498]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1,plain,
% 2.68/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.68/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1102,plain,
% 2.68/1.00      ( ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(X1_50) | X1_50 = X0_50 ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1803,plain,
% 2.68/1.00      ( ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(sK2) | X0_50 = sK2 ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1102]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3923,plain,
% 2.68/1.00      ( ~ v1_xboole_0(sK1) | ~ v1_xboole_0(sK2) | sK1 = sK2 ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1803]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4178,plain,
% 2.68/1.00      ( sK1 = sK2 ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_3340,c_26,c_22,c_37,c_82,c_0,c_1707,c_1776,c_1921,c_1924,
% 2.68/1.00                 c_2511,c_2512,c_3329,c_3923]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4365,plain,
% 2.68/1.00      ( v1_xboole_0(sK2) = iProver_top ),
% 2.68/1.00      inference(light_normalisation,[status(thm)],[c_4361,c_4178]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1103,plain,
% 2.68/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1510,plain,
% 2.68/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1103]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1511,plain,
% 2.68/1.00      ( X0_50 = X1_50
% 2.68/1.00      | v1_xboole_0(X1_50) != iProver_top
% 2.68/1.00      | v1_xboole_0(X0_50) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1102]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2433,plain,
% 2.68/1.00      ( k1_xboole_0 = X0_50 | v1_xboole_0(X0_50) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1510,c_1511]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4368,plain,
% 2.68/1.00      ( sK2 = k1_xboole_0 ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_4365,c_2433]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3348,plain,
% 2.68/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 2.68/1.00      inference(demodulation,[status(thm)],[c_3332,c_1554]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4181,plain,
% 2.68/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2)) != iProver_top ),
% 2.68/1.00      inference(demodulation,[status(thm)],[c_4178,c_3348]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4382,plain,
% 2.68/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.68/1.00      inference(demodulation,[status(thm)],[c_4368,c_4181]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_5,plain,
% 2.68/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.68/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1098,plain,
% 2.68/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_6,plain,
% 2.68/1.00      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1097,plain,
% 2.68/1.00      ( k2_funct_1(k6_partfun1(X0_50)) = k6_partfun1(X0_50) ),
% 2.68/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1849,plain,
% 2.68/1.00      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1098,c_1097]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1850,plain,
% 2.68/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.68/1.00      inference(light_normalisation,[status(thm)],[c_1849,c_1098]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4419,plain,
% 2.68/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.68/1.00      inference(light_normalisation,[status(thm)],[c_4382,c_1850]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1516,plain,
% 2.68/1.00      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
% 2.68/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1095]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2652,plain,
% 2.68/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1520,c_1516]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3345,plain,
% 2.68/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
% 2.68/1.00      inference(demodulation,[status(thm)],[c_3332,c_2652]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4387,plain,
% 2.68/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.68/1.00      inference(demodulation,[status(thm)],[c_4368,c_3345]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4421,plain,
% 2.68/1.00      ( $false ),
% 2.68/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_4419,c_4387]) ).
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.68/1.00  
% 2.68/1.00  ------                               Statistics
% 2.68/1.00  
% 2.68/1.00  ------ General
% 2.68/1.00  
% 2.68/1.00  abstr_ref_over_cycles:                  0
% 2.68/1.00  abstr_ref_under_cycles:                 0
% 2.68/1.00  gc_basic_clause_elim:                   0
% 2.68/1.00  forced_gc_time:                         0
% 2.68/1.00  parsing_time:                           0.009
% 2.68/1.00  unif_index_cands_time:                  0.
% 2.68/1.00  unif_index_add_time:                    0.
% 2.68/1.00  orderings_time:                         0.
% 2.68/1.00  out_proof_time:                         0.016
% 2.68/1.00  total_time:                             0.184
% 2.68/1.00  num_of_symbols:                         55
% 2.68/1.00  num_of_terms:                           5126
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing
% 2.68/1.00  
% 2.68/1.00  num_of_splits:                          0
% 2.68/1.00  num_of_split_atoms:                     0
% 2.68/1.00  num_of_reused_defs:                     0
% 2.68/1.00  num_eq_ax_congr_red:                    13
% 2.68/1.00  num_of_sem_filtered_clauses:            3
% 2.68/1.00  num_of_subtypes:                        2
% 2.68/1.00  monotx_restored_types:                  1
% 2.68/1.00  sat_num_of_epr_types:                   0
% 2.68/1.00  sat_num_of_non_cyclic_types:            0
% 2.68/1.00  sat_guarded_non_collapsed_types:        1
% 2.68/1.00  num_pure_diseq_elim:                    0
% 2.68/1.00  simp_replaced_by:                       0
% 2.68/1.00  res_preprocessed:                       134
% 2.68/1.00  prep_upred:                             0
% 2.68/1.00  prep_unflattend:                        62
% 2.68/1.00  smt_new_axioms:                         0
% 2.68/1.00  pred_elim_cands:                        6
% 2.68/1.00  pred_elim:                              3
% 2.68/1.00  pred_elim_cl:                           3
% 2.68/1.00  pred_elim_cycles:                       6
% 2.68/1.00  merged_defs:                            0
% 2.68/1.00  merged_defs_ncl:                        0
% 2.68/1.00  bin_hyper_res:                          0
% 2.68/1.00  prep_cycles:                            4
% 2.68/1.00  pred_elim_time:                         0.015
% 2.68/1.00  splitting_time:                         0.
% 2.68/1.00  sem_filter_time:                        0.
% 2.68/1.00  monotx_time:                            0.001
% 2.68/1.00  subtype_inf_time:                       0.002
% 2.68/1.00  
% 2.68/1.00  ------ Problem properties
% 2.68/1.00  
% 2.68/1.00  clauses:                                24
% 2.68/1.00  conjectures:                            8
% 2.68/1.00  epr:                                    6
% 2.68/1.00  horn:                                   23
% 2.68/1.00  ground:                                 14
% 2.68/1.00  unary:                                  14
% 2.68/1.00  binary:                                 4
% 2.68/1.00  lits:                                   55
% 2.68/1.00  lits_eq:                                14
% 2.68/1.00  fd_pure:                                0
% 2.68/1.00  fd_pseudo:                              0
% 2.68/1.00  fd_cond:                                0
% 2.68/1.00  fd_pseudo_cond:                         4
% 2.68/1.00  ac_symbols:                             0
% 2.68/1.00  
% 2.68/1.00  ------ Propositional Solver
% 2.68/1.00  
% 2.68/1.00  prop_solver_calls:                      28
% 2.68/1.00  prop_fast_solver_calls:                 1025
% 2.68/1.00  smt_solver_calls:                       0
% 2.68/1.00  smt_fast_solver_calls:                  0
% 2.68/1.00  prop_num_of_clauses:                    1492
% 2.68/1.00  prop_preprocess_simplified:             4954
% 2.68/1.00  prop_fo_subsumed:                       36
% 2.68/1.00  prop_solver_time:                       0.
% 2.68/1.00  smt_solver_time:                        0.
% 2.68/1.00  smt_fast_solver_time:                   0.
% 2.68/1.00  prop_fast_solver_time:                  0.
% 2.68/1.00  prop_unsat_core_time:                   0.
% 2.68/1.00  
% 2.68/1.00  ------ QBF
% 2.68/1.00  
% 2.68/1.00  qbf_q_res:                              0
% 2.68/1.00  qbf_num_tautologies:                    0
% 2.68/1.00  qbf_prep_cycles:                        0
% 2.68/1.00  
% 2.68/1.00  ------ BMC1
% 2.68/1.00  
% 2.68/1.00  bmc1_current_bound:                     -1
% 2.68/1.00  bmc1_last_solved_bound:                 -1
% 2.68/1.00  bmc1_unsat_core_size:                   -1
% 2.68/1.00  bmc1_unsat_core_parents_size:           -1
% 2.68/1.00  bmc1_merge_next_fun:                    0
% 2.68/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.68/1.00  
% 2.68/1.00  ------ Instantiation
% 2.68/1.00  
% 2.68/1.00  inst_num_of_clauses:                    433
% 2.68/1.00  inst_num_in_passive:                    131
% 2.68/1.00  inst_num_in_active:                     208
% 2.68/1.00  inst_num_in_unprocessed:                95
% 2.68/1.00  inst_num_of_loops:                      310
% 2.68/1.00  inst_num_of_learning_restarts:          0
% 2.68/1.00  inst_num_moves_active_passive:          99
% 2.68/1.00  inst_lit_activity:                      0
% 2.68/1.00  inst_lit_activity_moves:                0
% 2.68/1.00  inst_num_tautologies:                   0
% 2.68/1.00  inst_num_prop_implied:                  0
% 2.68/1.00  inst_num_existing_simplified:           0
% 2.68/1.00  inst_num_eq_res_simplified:             0
% 2.68/1.00  inst_num_child_elim:                    0
% 2.68/1.00  inst_num_of_dismatching_blockings:      166
% 2.68/1.00  inst_num_of_non_proper_insts:           475
% 2.68/1.00  inst_num_of_duplicates:                 0
% 2.68/1.00  inst_inst_num_from_inst_to_res:         0
% 2.68/1.00  inst_dismatching_checking_time:         0.
% 2.68/1.00  
% 2.68/1.00  ------ Resolution
% 2.68/1.00  
% 2.68/1.00  res_num_of_clauses:                     0
% 2.68/1.00  res_num_in_passive:                     0
% 2.68/1.00  res_num_in_active:                      0
% 2.68/1.00  res_num_of_loops:                       138
% 2.68/1.00  res_forward_subset_subsumed:            33
% 2.68/1.00  res_backward_subset_subsumed:           2
% 2.68/1.00  res_forward_subsumed:                   0
% 2.68/1.00  res_backward_subsumed:                  0
% 2.68/1.00  res_forward_subsumption_resolution:     1
% 2.68/1.00  res_backward_subsumption_resolution:    0
% 2.68/1.00  res_clause_to_clause_subsumption:       141
% 2.68/1.00  res_orphan_elimination:                 0
% 2.68/1.00  res_tautology_del:                      21
% 2.68/1.00  res_num_eq_res_simplified:              0
% 2.68/1.00  res_num_sel_changes:                    0
% 2.68/1.00  res_moves_from_active_to_pass:          0
% 2.68/1.00  
% 2.68/1.00  ------ Superposition
% 2.68/1.00  
% 2.68/1.00  sup_time_total:                         0.
% 2.68/1.00  sup_time_generating:                    0.
% 2.68/1.00  sup_time_sim_full:                      0.
% 2.68/1.00  sup_time_sim_immed:                     0.
% 2.68/1.00  
% 2.68/1.00  sup_num_of_clauses:                     22
% 2.68/1.00  sup_num_in_active:                      16
% 2.68/1.00  sup_num_in_passive:                     6
% 2.68/1.00  sup_num_of_loops:                       61
% 2.68/1.00  sup_fw_superposition:                   22
% 2.68/1.00  sup_bw_superposition:                   19
% 2.68/1.00  sup_immediate_simplified:               15
% 2.68/1.00  sup_given_eliminated:                   1
% 2.68/1.00  comparisons_done:                       0
% 2.68/1.00  comparisons_avoided:                    3
% 2.68/1.00  
% 2.68/1.00  ------ Simplifications
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  sim_fw_subset_subsumed:                 11
% 2.68/1.00  sim_bw_subset_subsumed:                 2
% 2.68/1.00  sim_fw_subsumed:                        0
% 2.68/1.00  sim_bw_subsumed:                        0
% 2.68/1.00  sim_fw_subsumption_res:                 0
% 2.68/1.00  sim_bw_subsumption_res:                 1
% 2.68/1.00  sim_tautology_del:                      0
% 2.68/1.00  sim_eq_tautology_del:                   6
% 2.68/1.00  sim_eq_res_simp:                        0
% 2.68/1.00  sim_fw_demodulated:                     1
% 2.68/1.00  sim_bw_demodulated:                     46
% 2.68/1.00  sim_light_normalised:                   11
% 2.68/1.00  sim_joinable_taut:                      0
% 2.68/1.00  sim_joinable_simp:                      0
% 2.68/1.00  sim_ac_normalised:                      0
% 2.68/1.00  sim_smt_subsumption:                    0
% 2.68/1.00  
%------------------------------------------------------------------------------
