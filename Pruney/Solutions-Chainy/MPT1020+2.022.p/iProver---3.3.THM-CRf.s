%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:08 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_40)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0(X0))
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f45])).

fof(f55,plain,(
    ! [X0] : v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

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

fof(f50,plain,(
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f50,f49])).

fof(f86,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f60,plain,(
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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    v3_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f58,f74,f74])).

cnf(c_2,plain,
    ( v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1280,plain,
    ( v1_xboole_0(sK0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1787,plain,
    ( v1_xboole_0(sK0(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1282,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1785,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1281,plain,
    ( ~ v1_xboole_0(X0_52)
    | ~ v1_xboole_0(X1_52)
    | X1_52 = X0_52 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1786,plain,
    ( X0_52 = X1_52
    | v1_xboole_0(X1_52) != iProver_top
    | v1_xboole_0(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1281])).

cnf(c_3135,plain,
    ( k1_xboole_0 = X0_52
    | v1_xboole_0(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_1786])).

cnf(c_3486,plain,
    ( sK0(X0_54) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1787,c_3135])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1279,plain,
    ( m1_subset_1(sK0(X0_54),k1_zfmisc_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1788,plain,
    ( m1_subset_1(sK0(X0_54),k1_zfmisc_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1279])).

cnf(c_3562,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3486,c_1788])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1272,plain,
    ( r2_relset_1(X0_52,X1_52,X2_52,X2_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1794,plain,
    ( r2_relset_1(X0_52,X1_52,X2_52,X2_52) = iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_4935,plain,
    ( r2_relset_1(X0_52,X1_52,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3562,c_1794])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1265,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1801,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1261,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1805,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_370,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_18])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_382,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_370,c_7])).

cnf(c_1257,plain,
    ( ~ v2_funct_2(X0_52,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
    | k2_relat_1(X0_52) = X1_52 ),
    inference(subtyping,[status(esa)],[c_382])).

cnf(c_1809,plain,
    ( k2_relat_1(X0_52) = X1_52
    | v2_funct_2(X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_5324,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_2(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1809])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_458,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_459,plain,
    ( v2_funct_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_460,plain,
    ( v2_funct_2(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_5464,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5324,c_35,c_38,c_460])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1273,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k2_relset_1(X1_52,X2_52,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1793,plain,
    ( k2_relset_1(X0_52,X1_52,X2_52) = k2_relat_1(X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_3202,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1805,c_1793])).

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
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_191,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_23])).

cnf(c_192,plain,
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
    inference(renaming,[status(thm)],[c_191])).

cnf(c_1258,plain,
    ( ~ r2_relset_1(X0_52,X0_52,k1_partfun1(X0_52,X1_52,X1_52,X0_52,X2_52,X3_52),k6_partfun1(X0_52))
    | ~ v1_funct_2(X3_52,X1_52,X0_52)
    | ~ v1_funct_2(X2_52,X0_52,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ v1_funct_1(X2_52)
    | ~ v1_funct_1(X3_52)
    | k2_relset_1(X0_52,X1_52,X2_52) != X1_52
    | k2_funct_1(X2_52) = X3_52
    | k1_xboole_0 = X1_52
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_192])).

cnf(c_1808,plain,
    ( k2_relset_1(X0_52,X1_52,X2_52) != X1_52
    | k2_funct_1(X2_52) = X3_52
    | k1_xboole_0 = X1_52
    | k1_xboole_0 = X0_52
    | r2_relset_1(X0_52,X0_52,k1_partfun1(X0_52,X1_52,X1_52,X0_52,X2_52,X3_52),k6_partfun1(X0_52)) != iProver_top
    | v1_funct_2(X3_52,X1_52,X0_52) != iProver_top
    | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top
    | v1_funct_1(X3_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_4817,plain,
    ( k2_funct_1(sK2) = X0_52
    | k2_relat_1(sK2) != sK1
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3202,c_1808])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5245,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0
    | k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4817,c_35,c_36,c_38])).

cnf(c_5246,plain,
    ( k2_funct_1(sK2) = X0_52
    | k2_relat_1(sK2) != sK1
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5245])).

cnf(c_5466,plain,
    ( k2_funct_1(sK2) = X0_52
    | sK1 != sK1
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5464,c_5246])).

cnf(c_5468,plain,
    ( k2_funct_1(sK2) = X0_52
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0_52,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5466])).

cnf(c_5756,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_5468])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5757,plain,
    ( ~ v1_funct_2(sK3,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5756])).

cnf(c_5798,plain,
    ( sK1 = k1_xboole_0
    | k2_funct_1(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5756,c_39,c_40,c_42])).

cnf(c_5799,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5798])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1266,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1800,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1266])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_478,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_480,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_34,c_33,c_31])).

cnf(c_1252,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_480])).

cnf(c_1813,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1800,c_1252])).

cnf(c_5800,plain,
    ( sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5799,c_1813])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1876,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_1877,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1876])).

cnf(c_5803,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5800,c_42,c_1877])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1278,plain,
    ( ~ v1_relat_1(X0_52)
    | k2_relat_1(X0_52) != k1_xboole_0
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1789,plain,
    ( k2_relat_1(X0_52) != k1_xboole_0
    | k1_xboole_0 = X0_52
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_5472,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5464,c_1789])).

cnf(c_1275,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1791,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1275])).

cnf(c_2728,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1791])).

cnf(c_5710,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5472,c_2728])).

cnf(c_5711,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5710])).

cnf(c_5807,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5803,c_5711])).

cnf(c_5853,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5807])).

cnf(c_1264,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1802,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_5323,plain,
    ( k2_relat_1(sK3) = sK1
    | v2_funct_2(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_1809])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,negated_conjecture,
    ( v3_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_447,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK1 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_448,plain,
    ( v2_funct_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_449,plain,
    ( v2_funct_2(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_5453,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5323,c_39,c_42,c_449])).

cnf(c_5461,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5453,c_1789])).

cnf(c_2727,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_1791])).

cnf(c_5707,plain,
    ( sK1 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5461,c_2727])).

cnf(c_5708,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5707])).

cnf(c_5808,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5803,c_5708])).

cnf(c_5837,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5808])).

cnf(c_5827,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5803,c_1813])).

cnf(c_5847,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5837,c_5827])).

cnf(c_5854,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5853,c_5847])).

cnf(c_13,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1270,plain,
    ( m1_subset_1(k6_partfun1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_52,X0_52))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1796,plain,
    ( m1_subset_1(k6_partfun1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_52,X0_52))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1274,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ v1_xboole_0(X2_52)
    | v1_xboole_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1792,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | v1_xboole_0(X2_52) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_2902,plain,
    ( v1_xboole_0(X0_52) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_1792])).

cnf(c_5403,plain,
    ( k6_partfun1(X0_52) = X1_52
    | v1_xboole_0(X0_52) != iProver_top
    | v1_xboole_0(X1_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2902,c_1786])).

cnf(c_6060,plain,
    ( k6_partfun1(k1_xboole_0) = X0_52
    | v1_xboole_0(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_5403])).

cnf(c_6069,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1785,c_6060])).

cnf(c_6,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1276,plain,
    ( k2_funct_1(k6_partfun1(X0_52)) = k6_partfun1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_6527,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6069,c_1276])).

cnf(c_6528,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6527,c_6069])).

cnf(c_6992,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5854,c_6528])).

cnf(c_6994,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4935,c_6992])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:26:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.77/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.99  
% 3.77/0.99  ------  iProver source info
% 3.77/0.99  
% 3.77/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.99  git: non_committed_changes: false
% 3.77/0.99  git: last_make_outside_of_git: false
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  
% 3.77/0.99  ------ Input Options
% 3.77/0.99  
% 3.77/0.99  --out_options                           all
% 3.77/0.99  --tptp_safe_out                         true
% 3.77/0.99  --problem_path                          ""
% 3.77/0.99  --include_path                          ""
% 3.77/0.99  --clausifier                            res/vclausify_rel
% 3.77/0.99  --clausifier_options                    ""
% 3.77/0.99  --stdin                                 false
% 3.77/0.99  --stats_out                             all
% 3.77/0.99  
% 3.77/0.99  ------ General Options
% 3.77/0.99  
% 3.77/0.99  --fof                                   false
% 3.77/0.99  --time_out_real                         305.
% 3.77/0.99  --time_out_virtual                      -1.
% 3.77/0.99  --symbol_type_check                     false
% 3.77/0.99  --clausify_out                          false
% 3.77/0.99  --sig_cnt_out                           false
% 3.77/0.99  --trig_cnt_out                          false
% 3.77/0.99  --trig_cnt_out_tolerance                1.
% 3.77/0.99  --trig_cnt_out_sk_spl                   false
% 3.77/0.99  --abstr_cl_out                          false
% 3.77/0.99  
% 3.77/0.99  ------ Global Options
% 3.77/0.99  
% 3.77/0.99  --schedule                              default
% 3.77/0.99  --add_important_lit                     false
% 3.77/0.99  --prop_solver_per_cl                    1000
% 3.77/0.99  --min_unsat_core                        false
% 3.77/0.99  --soft_assumptions                      false
% 3.77/0.99  --soft_lemma_size                       3
% 3.77/0.99  --prop_impl_unit_size                   0
% 3.77/0.99  --prop_impl_unit                        []
% 3.77/0.99  --share_sel_clauses                     true
% 3.77/0.99  --reset_solvers                         false
% 3.77/0.99  --bc_imp_inh                            [conj_cone]
% 3.77/0.99  --conj_cone_tolerance                   3.
% 3.77/0.99  --extra_neg_conj                        none
% 3.77/0.99  --large_theory_mode                     true
% 3.77/0.99  --prolific_symb_bound                   200
% 3.77/0.99  --lt_threshold                          2000
% 3.77/0.99  --clause_weak_htbl                      true
% 3.77/0.99  --gc_record_bc_elim                     false
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing Options
% 3.77/0.99  
% 3.77/0.99  --preprocessing_flag                    true
% 3.77/0.99  --time_out_prep_mult                    0.1
% 3.77/0.99  --splitting_mode                        input
% 3.77/0.99  --splitting_grd                         true
% 3.77/0.99  --splitting_cvd                         false
% 3.77/0.99  --splitting_cvd_svl                     false
% 3.77/0.99  --splitting_nvd                         32
% 3.77/0.99  --sub_typing                            true
% 3.77/0.99  --prep_gs_sim                           true
% 3.77/0.99  --prep_unflatten                        true
% 3.77/0.99  --prep_res_sim                          true
% 3.77/0.99  --prep_upred                            true
% 3.77/0.99  --prep_sem_filter                       exhaustive
% 3.77/0.99  --prep_sem_filter_out                   false
% 3.77/0.99  --pred_elim                             true
% 3.77/0.99  --res_sim_input                         true
% 3.77/0.99  --eq_ax_congr_red                       true
% 3.77/0.99  --pure_diseq_elim                       true
% 3.77/0.99  --brand_transform                       false
% 3.77/0.99  --non_eq_to_eq                          false
% 3.77/0.99  --prep_def_merge                        true
% 3.77/0.99  --prep_def_merge_prop_impl              false
% 3.77/0.99  --prep_def_merge_mbd                    true
% 3.77/0.99  --prep_def_merge_tr_red                 false
% 3.77/0.99  --prep_def_merge_tr_cl                  false
% 3.77/0.99  --smt_preprocessing                     true
% 3.77/0.99  --smt_ac_axioms                         fast
% 3.77/0.99  --preprocessed_out                      false
% 3.77/0.99  --preprocessed_stats                    false
% 3.77/0.99  
% 3.77/0.99  ------ Abstraction refinement Options
% 3.77/0.99  
% 3.77/0.99  --abstr_ref                             []
% 3.77/0.99  --abstr_ref_prep                        false
% 3.77/0.99  --abstr_ref_until_sat                   false
% 3.77/0.99  --abstr_ref_sig_restrict                funpre
% 3.77/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.99  --abstr_ref_under                       []
% 3.77/0.99  
% 3.77/0.99  ------ SAT Options
% 3.77/0.99  
% 3.77/0.99  --sat_mode                              false
% 3.77/0.99  --sat_fm_restart_options                ""
% 3.77/0.99  --sat_gr_def                            false
% 3.77/0.99  --sat_epr_types                         true
% 3.77/0.99  --sat_non_cyclic_types                  false
% 3.77/0.99  --sat_finite_models                     false
% 3.77/0.99  --sat_fm_lemmas                         false
% 3.77/0.99  --sat_fm_prep                           false
% 3.77/0.99  --sat_fm_uc_incr                        true
% 3.77/0.99  --sat_out_model                         small
% 3.77/0.99  --sat_out_clauses                       false
% 3.77/0.99  
% 3.77/0.99  ------ QBF Options
% 3.77/0.99  
% 3.77/0.99  --qbf_mode                              false
% 3.77/0.99  --qbf_elim_univ                         false
% 3.77/0.99  --qbf_dom_inst                          none
% 3.77/0.99  --qbf_dom_pre_inst                      false
% 3.77/0.99  --qbf_sk_in                             false
% 3.77/0.99  --qbf_pred_elim                         true
% 3.77/0.99  --qbf_split                             512
% 3.77/0.99  
% 3.77/0.99  ------ BMC1 Options
% 3.77/0.99  
% 3.77/0.99  --bmc1_incremental                      false
% 3.77/0.99  --bmc1_axioms                           reachable_all
% 3.77/0.99  --bmc1_min_bound                        0
% 3.77/0.99  --bmc1_max_bound                        -1
% 3.77/0.99  --bmc1_max_bound_default                -1
% 3.77/0.99  --bmc1_symbol_reachability              true
% 3.77/0.99  --bmc1_property_lemmas                  false
% 3.77/0.99  --bmc1_k_induction                      false
% 3.77/0.99  --bmc1_non_equiv_states                 false
% 3.77/0.99  --bmc1_deadlock                         false
% 3.77/0.99  --bmc1_ucm                              false
% 3.77/0.99  --bmc1_add_unsat_core                   none
% 3.77/0.99  --bmc1_unsat_core_children              false
% 3.77/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.99  --bmc1_out_stat                         full
% 3.77/0.99  --bmc1_ground_init                      false
% 3.77/0.99  --bmc1_pre_inst_next_state              false
% 3.77/0.99  --bmc1_pre_inst_state                   false
% 3.77/0.99  --bmc1_pre_inst_reach_state             false
% 3.77/0.99  --bmc1_out_unsat_core                   false
% 3.77/0.99  --bmc1_aig_witness_out                  false
% 3.77/0.99  --bmc1_verbose                          false
% 3.77/0.99  --bmc1_dump_clauses_tptp                false
% 3.77/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.99  --bmc1_dump_file                        -
% 3.77/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.99  --bmc1_ucm_extend_mode                  1
% 3.77/0.99  --bmc1_ucm_init_mode                    2
% 3.77/0.99  --bmc1_ucm_cone_mode                    none
% 3.77/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.99  --bmc1_ucm_relax_model                  4
% 3.77/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.99  --bmc1_ucm_layered_model                none
% 3.77/0.99  --bmc1_ucm_max_lemma_size               10
% 3.77/0.99  
% 3.77/0.99  ------ AIG Options
% 3.77/0.99  
% 3.77/0.99  --aig_mode                              false
% 3.77/0.99  
% 3.77/0.99  ------ Instantiation Options
% 3.77/0.99  
% 3.77/0.99  --instantiation_flag                    true
% 3.77/0.99  --inst_sos_flag                         true
% 3.77/0.99  --inst_sos_phase                        true
% 3.77/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel_side                     num_symb
% 3.77/0.99  --inst_solver_per_active                1400
% 3.77/0.99  --inst_solver_calls_frac                1.
% 3.77/0.99  --inst_passive_queue_type               priority_queues
% 3.77/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.99  --inst_passive_queues_freq              [25;2]
% 3.77/0.99  --inst_dismatching                      true
% 3.77/0.99  --inst_eager_unprocessed_to_passive     true
% 3.77/0.99  --inst_prop_sim_given                   true
% 3.77/0.99  --inst_prop_sim_new                     false
% 3.77/0.99  --inst_subs_new                         false
% 3.77/0.99  --inst_eq_res_simp                      false
% 3.77/0.99  --inst_subs_given                       false
% 3.77/0.99  --inst_orphan_elimination               true
% 3.77/0.99  --inst_learning_loop_flag               true
% 3.77/0.99  --inst_learning_start                   3000
% 3.77/0.99  --inst_learning_factor                  2
% 3.77/0.99  --inst_start_prop_sim_after_learn       3
% 3.77/0.99  --inst_sel_renew                        solver
% 3.77/0.99  --inst_lit_activity_flag                true
% 3.77/0.99  --inst_restr_to_given                   false
% 3.77/0.99  --inst_activity_threshold               500
% 3.77/0.99  --inst_out_proof                        true
% 3.77/0.99  
% 3.77/0.99  ------ Resolution Options
% 3.77/0.99  
% 3.77/0.99  --resolution_flag                       true
% 3.77/0.99  --res_lit_sel                           adaptive
% 3.77/0.99  --res_lit_sel_side                      none
% 3.77/0.99  --res_ordering                          kbo
% 3.77/0.99  --res_to_prop_solver                    active
% 3.77/0.99  --res_prop_simpl_new                    false
% 3.77/0.99  --res_prop_simpl_given                  true
% 3.77/0.99  --res_passive_queue_type                priority_queues
% 3.77/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.99  --res_passive_queues_freq               [15;5]
% 3.77/0.99  --res_forward_subs                      full
% 3.77/0.99  --res_backward_subs                     full
% 3.77/0.99  --res_forward_subs_resolution           true
% 3.77/0.99  --res_backward_subs_resolution          true
% 3.77/0.99  --res_orphan_elimination                true
% 3.77/0.99  --res_time_limit                        2.
% 3.77/0.99  --res_out_proof                         true
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Options
% 3.77/0.99  
% 3.77/0.99  --superposition_flag                    true
% 3.77/0.99  --sup_passive_queue_type                priority_queues
% 3.77/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.99  --demod_completeness_check              fast
% 3.77/0.99  --demod_use_ground                      true
% 3.77/0.99  --sup_to_prop_solver                    passive
% 3.77/0.99  --sup_prop_simpl_new                    true
% 3.77/0.99  --sup_prop_simpl_given                  true
% 3.77/0.99  --sup_fun_splitting                     true
% 3.77/0.99  --sup_smt_interval                      50000
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Simplification Setup
% 3.77/0.99  
% 3.77/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/0.99  --sup_immed_triv                        [TrivRules]
% 3.77/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_bw_main                     []
% 3.77/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_input_bw                          []
% 3.77/0.99  
% 3.77/0.99  ------ Combination Options
% 3.77/0.99  
% 3.77/0.99  --comb_res_mult                         3
% 3.77/0.99  --comb_sup_mult                         2
% 3.77/0.99  --comb_inst_mult                        10
% 3.77/0.99  
% 3.77/0.99  ------ Debug Options
% 3.77/0.99  
% 3.77/0.99  --dbg_backtrace                         false
% 3.77/0.99  --dbg_dump_prop_clauses                 false
% 3.77/0.99  --dbg_dump_prop_clauses_file            -
% 3.77/0.99  --dbg_out_stat                          false
% 3.77/0.99  ------ Parsing...
% 3.77/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.99  ------ Proving...
% 3.77/0.99  ------ Problem Properties 
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  clauses                                 31
% 3.77/0.99  conjectures                             8
% 3.77/0.99  EPR                                     8
% 3.77/0.99  Horn                                    30
% 3.77/0.99  unary                                   17
% 3.77/0.99  binary                                  4
% 3.77/0.99  lits                                    73
% 3.77/0.99  lits eq                                 15
% 3.77/0.99  fd_pure                                 0
% 3.77/0.99  fd_pseudo                               0
% 3.77/0.99  fd_cond                                 2
% 3.77/0.99  fd_pseudo_cond                          4
% 3.77/0.99  AC symbols                              0
% 3.77/0.99  
% 3.77/0.99  ------ Schedule dynamic 5 is on 
% 3.77/0.99  
% 3.77/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  Current options:
% 3.77/0.99  ------ 
% 3.77/0.99  
% 3.77/0.99  ------ Input Options
% 3.77/0.99  
% 3.77/0.99  --out_options                           all
% 3.77/0.99  --tptp_safe_out                         true
% 3.77/0.99  --problem_path                          ""
% 3.77/0.99  --include_path                          ""
% 3.77/0.99  --clausifier                            res/vclausify_rel
% 3.77/0.99  --clausifier_options                    ""
% 3.77/0.99  --stdin                                 false
% 3.77/0.99  --stats_out                             all
% 3.77/0.99  
% 3.77/0.99  ------ General Options
% 3.77/0.99  
% 3.77/0.99  --fof                                   false
% 3.77/0.99  --time_out_real                         305.
% 3.77/0.99  --time_out_virtual                      -1.
% 3.77/0.99  --symbol_type_check                     false
% 3.77/0.99  --clausify_out                          false
% 3.77/0.99  --sig_cnt_out                           false
% 3.77/0.99  --trig_cnt_out                          false
% 3.77/0.99  --trig_cnt_out_tolerance                1.
% 3.77/0.99  --trig_cnt_out_sk_spl                   false
% 3.77/0.99  --abstr_cl_out                          false
% 3.77/0.99  
% 3.77/0.99  ------ Global Options
% 3.77/0.99  
% 3.77/0.99  --schedule                              default
% 3.77/0.99  --add_important_lit                     false
% 3.77/0.99  --prop_solver_per_cl                    1000
% 3.77/0.99  --min_unsat_core                        false
% 3.77/0.99  --soft_assumptions                      false
% 3.77/0.99  --soft_lemma_size                       3
% 3.77/0.99  --prop_impl_unit_size                   0
% 3.77/0.99  --prop_impl_unit                        []
% 3.77/0.99  --share_sel_clauses                     true
% 3.77/0.99  --reset_solvers                         false
% 3.77/0.99  --bc_imp_inh                            [conj_cone]
% 3.77/0.99  --conj_cone_tolerance                   3.
% 3.77/0.99  --extra_neg_conj                        none
% 3.77/0.99  --large_theory_mode                     true
% 3.77/0.99  --prolific_symb_bound                   200
% 3.77/0.99  --lt_threshold                          2000
% 3.77/0.99  --clause_weak_htbl                      true
% 3.77/0.99  --gc_record_bc_elim                     false
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing Options
% 3.77/0.99  
% 3.77/0.99  --preprocessing_flag                    true
% 3.77/0.99  --time_out_prep_mult                    0.1
% 3.77/0.99  --splitting_mode                        input
% 3.77/0.99  --splitting_grd                         true
% 3.77/0.99  --splitting_cvd                         false
% 3.77/0.99  --splitting_cvd_svl                     false
% 3.77/0.99  --splitting_nvd                         32
% 3.77/0.99  --sub_typing                            true
% 3.77/0.99  --prep_gs_sim                           true
% 3.77/0.99  --prep_unflatten                        true
% 3.77/0.99  --prep_res_sim                          true
% 3.77/0.99  --prep_upred                            true
% 3.77/0.99  --prep_sem_filter                       exhaustive
% 3.77/0.99  --prep_sem_filter_out                   false
% 3.77/0.99  --pred_elim                             true
% 3.77/0.99  --res_sim_input                         true
% 3.77/0.99  --eq_ax_congr_red                       true
% 3.77/0.99  --pure_diseq_elim                       true
% 3.77/0.99  --brand_transform                       false
% 3.77/0.99  --non_eq_to_eq                          false
% 3.77/0.99  --prep_def_merge                        true
% 3.77/0.99  --prep_def_merge_prop_impl              false
% 3.77/0.99  --prep_def_merge_mbd                    true
% 3.77/0.99  --prep_def_merge_tr_red                 false
% 3.77/0.99  --prep_def_merge_tr_cl                  false
% 3.77/0.99  --smt_preprocessing                     true
% 3.77/0.99  --smt_ac_axioms                         fast
% 3.77/0.99  --preprocessed_out                      false
% 3.77/0.99  --preprocessed_stats                    false
% 3.77/0.99  
% 3.77/0.99  ------ Abstraction refinement Options
% 3.77/0.99  
% 3.77/0.99  --abstr_ref                             []
% 3.77/0.99  --abstr_ref_prep                        false
% 3.77/0.99  --abstr_ref_until_sat                   false
% 3.77/0.99  --abstr_ref_sig_restrict                funpre
% 3.77/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.99  --abstr_ref_under                       []
% 3.77/0.99  
% 3.77/0.99  ------ SAT Options
% 3.77/0.99  
% 3.77/0.99  --sat_mode                              false
% 3.77/0.99  --sat_fm_restart_options                ""
% 3.77/0.99  --sat_gr_def                            false
% 3.77/0.99  --sat_epr_types                         true
% 3.77/0.99  --sat_non_cyclic_types                  false
% 3.77/0.99  --sat_finite_models                     false
% 3.77/0.99  --sat_fm_lemmas                         false
% 3.77/0.99  --sat_fm_prep                           false
% 3.77/0.99  --sat_fm_uc_incr                        true
% 3.77/0.99  --sat_out_model                         small
% 3.77/0.99  --sat_out_clauses                       false
% 3.77/0.99  
% 3.77/0.99  ------ QBF Options
% 3.77/0.99  
% 3.77/0.99  --qbf_mode                              false
% 3.77/0.99  --qbf_elim_univ                         false
% 3.77/0.99  --qbf_dom_inst                          none
% 3.77/0.99  --qbf_dom_pre_inst                      false
% 3.77/0.99  --qbf_sk_in                             false
% 3.77/0.99  --qbf_pred_elim                         true
% 3.77/0.99  --qbf_split                             512
% 3.77/0.99  
% 3.77/0.99  ------ BMC1 Options
% 3.77/0.99  
% 3.77/0.99  --bmc1_incremental                      false
% 3.77/0.99  --bmc1_axioms                           reachable_all
% 3.77/0.99  --bmc1_min_bound                        0
% 3.77/0.99  --bmc1_max_bound                        -1
% 3.77/0.99  --bmc1_max_bound_default                -1
% 3.77/0.99  --bmc1_symbol_reachability              true
% 3.77/0.99  --bmc1_property_lemmas                  false
% 3.77/0.99  --bmc1_k_induction                      false
% 3.77/0.99  --bmc1_non_equiv_states                 false
% 3.77/0.99  --bmc1_deadlock                         false
% 3.77/0.99  --bmc1_ucm                              false
% 3.77/0.99  --bmc1_add_unsat_core                   none
% 3.77/0.99  --bmc1_unsat_core_children              false
% 3.77/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.99  --bmc1_out_stat                         full
% 3.77/0.99  --bmc1_ground_init                      false
% 3.77/0.99  --bmc1_pre_inst_next_state              false
% 3.77/0.99  --bmc1_pre_inst_state                   false
% 3.77/0.99  --bmc1_pre_inst_reach_state             false
% 3.77/0.99  --bmc1_out_unsat_core                   false
% 3.77/0.99  --bmc1_aig_witness_out                  false
% 3.77/0.99  --bmc1_verbose                          false
% 3.77/0.99  --bmc1_dump_clauses_tptp                false
% 3.77/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.99  --bmc1_dump_file                        -
% 3.77/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.99  --bmc1_ucm_extend_mode                  1
% 3.77/0.99  --bmc1_ucm_init_mode                    2
% 3.77/0.99  --bmc1_ucm_cone_mode                    none
% 3.77/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.99  --bmc1_ucm_relax_model                  4
% 3.77/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.99  --bmc1_ucm_layered_model                none
% 3.77/0.99  --bmc1_ucm_max_lemma_size               10
% 3.77/0.99  
% 3.77/0.99  ------ AIG Options
% 3.77/0.99  
% 3.77/0.99  --aig_mode                              false
% 3.77/0.99  
% 3.77/0.99  ------ Instantiation Options
% 3.77/0.99  
% 3.77/0.99  --instantiation_flag                    true
% 3.77/0.99  --inst_sos_flag                         true
% 3.77/0.99  --inst_sos_phase                        true
% 3.77/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel_side                     none
% 3.77/0.99  --inst_solver_per_active                1400
% 3.77/0.99  --inst_solver_calls_frac                1.
% 3.77/0.99  --inst_passive_queue_type               priority_queues
% 3.77/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.99  --inst_passive_queues_freq              [25;2]
% 3.77/0.99  --inst_dismatching                      true
% 3.77/0.99  --inst_eager_unprocessed_to_passive     true
% 3.77/0.99  --inst_prop_sim_given                   true
% 3.77/0.99  --inst_prop_sim_new                     false
% 3.77/0.99  --inst_subs_new                         false
% 3.77/0.99  --inst_eq_res_simp                      false
% 3.77/0.99  --inst_subs_given                       false
% 3.77/0.99  --inst_orphan_elimination               true
% 3.77/0.99  --inst_learning_loop_flag               true
% 3.77/0.99  --inst_learning_start                   3000
% 3.77/0.99  --inst_learning_factor                  2
% 3.77/0.99  --inst_start_prop_sim_after_learn       3
% 3.77/0.99  --inst_sel_renew                        solver
% 3.77/0.99  --inst_lit_activity_flag                true
% 3.77/0.99  --inst_restr_to_given                   false
% 3.77/0.99  --inst_activity_threshold               500
% 3.77/0.99  --inst_out_proof                        true
% 3.77/0.99  
% 3.77/0.99  ------ Resolution Options
% 3.77/0.99  
% 3.77/0.99  --resolution_flag                       false
% 3.77/0.99  --res_lit_sel                           adaptive
% 3.77/0.99  --res_lit_sel_side                      none
% 3.77/0.99  --res_ordering                          kbo
% 3.77/0.99  --res_to_prop_solver                    active
% 3.77/0.99  --res_prop_simpl_new                    false
% 3.77/0.99  --res_prop_simpl_given                  true
% 3.77/0.99  --res_passive_queue_type                priority_queues
% 3.77/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.99  --res_passive_queues_freq               [15;5]
% 3.77/0.99  --res_forward_subs                      full
% 3.77/0.99  --res_backward_subs                     full
% 3.77/0.99  --res_forward_subs_resolution           true
% 3.77/0.99  --res_backward_subs_resolution          true
% 3.77/0.99  --res_orphan_elimination                true
% 3.77/0.99  --res_time_limit                        2.
% 3.77/0.99  --res_out_proof                         true
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Options
% 3.77/0.99  
% 3.77/0.99  --superposition_flag                    true
% 3.77/0.99  --sup_passive_queue_type                priority_queues
% 3.77/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.99  --demod_completeness_check              fast
% 3.77/0.99  --demod_use_ground                      true
% 3.77/0.99  --sup_to_prop_solver                    passive
% 3.77/0.99  --sup_prop_simpl_new                    true
% 3.77/0.99  --sup_prop_simpl_given                  true
% 3.77/0.99  --sup_fun_splitting                     true
% 3.77/0.99  --sup_smt_interval                      50000
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Simplification Setup
% 3.77/0.99  
% 3.77/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/0.99  --sup_immed_triv                        [TrivRules]
% 3.77/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_bw_main                     []
% 3.77/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_input_bw                          []
% 3.77/0.99  
% 3.77/0.99  ------ Combination Options
% 3.77/0.99  
% 3.77/0.99  --comb_res_mult                         3
% 3.77/0.99  --comb_sup_mult                         2
% 3.77/0.99  --comb_inst_mult                        10
% 3.77/0.99  
% 3.77/0.99  ------ Debug Options
% 3.77/0.99  
% 3.77/0.99  --dbg_backtrace                         false
% 3.77/0.99  --dbg_dump_prop_clauses                 false
% 3.77/0.99  --dbg_dump_prop_clauses_file            -
% 3.77/0.99  --dbg_out_stat                          false
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ Proving...
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS status Theorem for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99   Resolution empty clause
% 3.77/0.99  
% 3.77/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  fof(f3,axiom,(
% 3.77/0.99    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f45,plain,(
% 3.77/0.99    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f46,plain,(
% 3.77/0.99    ! [X0] : (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f45])).
% 3.77/0.99  
% 3.77/0.99  fof(f55,plain,(
% 3.77/0.99    ( ! [X0] : (v1_xboole_0(sK0(X0))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f46])).
% 3.77/0.99  
% 3.77/0.99  fof(f1,axiom,(
% 3.77/0.99    v1_xboole_0(k1_xboole_0)),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f52,plain,(
% 3.77/0.99    v1_xboole_0(k1_xboole_0)),
% 3.77/0.99    inference(cnf_transformation,[],[f1])).
% 3.77/0.99  
% 3.77/0.99  fof(f2,axiom,(
% 3.77/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f22,plain,(
% 3.77/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f2])).
% 3.77/0.99  
% 3.77/0.99  fof(f53,plain,(
% 3.77/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f22])).
% 3.77/0.99  
% 3.77/0.99  fof(f54,plain,(
% 3.77/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f46])).
% 3.77/0.99  
% 3.77/0.99  fof(f10,axiom,(
% 3.77/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f29,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.77/0.99    inference(ennf_transformation,[],[f10])).
% 3.77/0.99  
% 3.77/0.99  fof(f30,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(flattening,[],[f29])).
% 3.77/0.99  
% 3.77/0.99  fof(f47,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(nnf_transformation,[],[f30])).
% 3.77/0.99  
% 3.77/0.99  fof(f64,plain,(
% 3.77/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f47])).
% 3.77/0.99  
% 3.77/0.99  fof(f90,plain,(
% 3.77/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(equality_resolution,[],[f64])).
% 3.77/0.99  
% 3.77/0.99  fof(f19,conjecture,(
% 3.77/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f20,negated_conjecture,(
% 3.77/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.77/0.99    inference(negated_conjecture,[],[f19])).
% 3.77/0.99  
% 3.77/0.99  fof(f43,plain,(
% 3.77/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.77/0.99    inference(ennf_transformation,[],[f20])).
% 3.77/0.99  
% 3.77/0.99  fof(f44,plain,(
% 3.77/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.77/0.99    inference(flattening,[],[f43])).
% 3.77/0.99  
% 3.77/0.99  fof(f50,plain,(
% 3.77/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK3,X0,X0) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f49,plain,(
% 3.77/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(X2,sK1,sK1) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f51,plain,(
% 3.77/0.99    (~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f50,f49])).
% 3.77/0.99  
% 3.77/0.99  fof(f86,plain,(
% 3.77/0.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f81,plain,(
% 3.77/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f7,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f21,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.77/0.99    inference(pure_predicate_removal,[],[f7])).
% 3.77/0.99  
% 3.77/0.99  fof(f26,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f21])).
% 3.77/0.99  
% 3.77/0.99  fof(f60,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f26])).
% 3.77/0.99  
% 3.77/0.99  fof(f13,axiom,(
% 3.77/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f33,plain,(
% 3.77/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.77/0.99    inference(ennf_transformation,[],[f13])).
% 3.77/0.99  
% 3.77/0.99  fof(f34,plain,(
% 3.77/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(flattening,[],[f33])).
% 3.77/0.99  
% 3.77/0.99  fof(f48,plain,(
% 3.77/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f34])).
% 3.77/0.99  
% 3.77/0.99  fof(f69,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f48])).
% 3.77/0.99  
% 3.77/0.99  fof(f6,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f25,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f6])).
% 3.77/0.99  
% 3.77/0.99  fof(f59,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f25])).
% 3.77/0.99  
% 3.77/0.99  fof(f78,plain,(
% 3.77/0.99    v1_funct_1(sK2)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f12,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f31,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f12])).
% 3.77/0.99  
% 3.77/0.99  fof(f32,plain,(
% 3.77/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(flattening,[],[f31])).
% 3.77/0.99  
% 3.77/0.99  fof(f68,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f32])).
% 3.77/0.99  
% 3.77/0.99  fof(f80,plain,(
% 3.77/0.99    v3_funct_2(sK2,sK1,sK1)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f9,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f28,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f9])).
% 3.77/0.99  
% 3.77/0.99  fof(f62,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f28])).
% 3.77/0.99  
% 3.77/0.99  fof(f18,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f41,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.77/0.99    inference(ennf_transformation,[],[f18])).
% 3.77/0.99  
% 3.77/0.99  fof(f42,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.77/0.99    inference(flattening,[],[f41])).
% 3.77/0.99  
% 3.77/0.99  fof(f77,plain,(
% 3.77/0.99    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f42])).
% 3.77/0.99  
% 3.77/0.99  fof(f17,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f39,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.77/0.99    inference(ennf_transformation,[],[f17])).
% 3.77/0.99  
% 3.77/0.99  fof(f40,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.77/0.99    inference(flattening,[],[f39])).
% 3.77/0.99  
% 3.77/0.99  fof(f75,plain,(
% 3.77/0.99    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f40])).
% 3.77/0.99  
% 3.77/0.99  fof(f79,plain,(
% 3.77/0.99    v1_funct_2(sK2,sK1,sK1)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f82,plain,(
% 3.77/0.99    v1_funct_1(sK3)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f83,plain,(
% 3.77/0.99    v1_funct_2(sK3,sK1,sK1)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f85,plain,(
% 3.77/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f87,plain,(
% 3.77/0.99    ~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f15,axiom,(
% 3.77/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f37,plain,(
% 3.77/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.77/0.99    inference(ennf_transformation,[],[f15])).
% 3.77/0.99  
% 3.77/0.99  fof(f38,plain,(
% 3.77/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.77/0.99    inference(flattening,[],[f37])).
% 3.77/0.99  
% 3.77/0.99  fof(f73,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f38])).
% 3.77/0.99  
% 3.77/0.99  fof(f4,axiom,(
% 3.77/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f23,plain,(
% 3.77/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f4])).
% 3.77/0.99  
% 3.77/0.99  fof(f24,plain,(
% 3.77/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.77/0.99    inference(flattening,[],[f23])).
% 3.77/0.99  
% 3.77/0.99  fof(f57,plain,(
% 3.77/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f24])).
% 3.77/0.99  
% 3.77/0.99  fof(f84,plain,(
% 3.77/0.99    v3_funct_2(sK3,sK1,sK1)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f11,axiom,(
% 3.77/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f65,plain,(
% 3.77/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f11])).
% 3.77/0.99  
% 3.77/0.99  fof(f16,axiom,(
% 3.77/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f74,plain,(
% 3.77/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f16])).
% 3.77/0.99  
% 3.77/0.99  fof(f89,plain,(
% 3.77/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.77/0.99    inference(definition_unfolding,[],[f65,f74])).
% 3.77/0.99  
% 3.77/0.99  fof(f8,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f27,plain,(
% 3.77/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f8])).
% 3.77/0.99  
% 3.77/0.99  fof(f61,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f27])).
% 3.77/0.99  
% 3.77/0.99  fof(f5,axiom,(
% 3.77/0.99    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f58,plain,(
% 3.77/0.99    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f5])).
% 3.77/0.99  
% 3.77/0.99  fof(f88,plain,(
% 3.77/0.99    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.77/0.99    inference(definition_unfolding,[],[f58,f74,f74])).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2,plain,
% 3.77/0.99      ( v1_xboole_0(sK0(X0)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1280,plain,
% 3.77/0.99      ( v1_xboole_0(sK0(X0_54)) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1787,plain,
% 3.77/0.99      ( v1_xboole_0(sK0(X0_54)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1280]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_0,plain,
% 3.77/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1282,plain,
% 3.77/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1785,plain,
% 3.77/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1282]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1,plain,
% 3.77/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1281,plain,
% 3.77/0.99      ( ~ v1_xboole_0(X0_52) | ~ v1_xboole_0(X1_52) | X1_52 = X0_52 ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1786,plain,
% 3.77/0.99      ( X0_52 = X1_52
% 3.77/0.99      | v1_xboole_0(X1_52) != iProver_top
% 3.77/0.99      | v1_xboole_0(X0_52) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1281]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3135,plain,
% 3.77/0.99      ( k1_xboole_0 = X0_52 | v1_xboole_0(X0_52) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1785,c_1786]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3486,plain,
% 3.77/0.99      ( sK0(X0_54) = k1_xboole_0 ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1787,c_3135]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3,plain,
% 3.77/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1279,plain,
% 3.77/0.99      ( m1_subset_1(sK0(X0_54),k1_zfmisc_1(X0_54)) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1788,plain,
% 3.77/0.99      ( m1_subset_1(sK0(X0_54),k1_zfmisc_1(X0_54)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1279]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3562,plain,
% 3.77/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_3486,c_1788]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_11,plain,
% 3.77/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.77/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1272,plain,
% 3.77/0.99      ( r2_relset_1(X0_52,X1_52,X2_52,X2_52)
% 3.77/0.99      | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1794,plain,
% 3.77/0.99      ( r2_relset_1(X0_52,X1_52,X2_52,X2_52) = iProver_top
% 3.77/0.99      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4935,plain,
% 3.77/0.99      ( r2_relset_1(X0_52,X1_52,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_3562,c_1794]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_26,negated_conjecture,
% 3.77/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1265,negated_conjecture,
% 3.77/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1801,plain,
% 3.77/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_31,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1261,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_31]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1805,plain,
% 3.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8,plain,
% 3.77/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_18,plain,
% 3.77/0.99      ( ~ v2_funct_2(X0,X1)
% 3.77/0.99      | ~ v5_relat_1(X0,X1)
% 3.77/0.99      | ~ v1_relat_1(X0)
% 3.77/0.99      | k2_relat_1(X0) = X1 ),
% 3.77/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_370,plain,
% 3.77/0.99      ( ~ v2_funct_2(X0,X1)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.77/0.99      | ~ v1_relat_1(X0)
% 3.77/0.99      | k2_relat_1(X0) = X1 ),
% 3.77/0.99      inference(resolution,[status(thm)],[c_8,c_18]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_382,plain,
% 3.77/0.99      ( ~ v2_funct_2(X0,X1)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.77/0.99      | k2_relat_1(X0) = X1 ),
% 3.77/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_370,c_7]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1257,plain,
% 3.77/0.99      ( ~ v2_funct_2(X0_52,X1_52)
% 3.77/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
% 3.77/0.99      | k2_relat_1(X0_52) = X1_52 ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_382]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1809,plain,
% 3.77/0.99      ( k2_relat_1(X0_52) = X1_52
% 3.77/0.99      | v2_funct_2(X0_52,X1_52) != iProver_top
% 3.77/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5324,plain,
% 3.77/0.99      ( k2_relat_1(sK2) = sK1 | v2_funct_2(sK2,sK1) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1805,c_1809]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_34,negated_conjecture,
% 3.77/0.99      ( v1_funct_1(sK2) ),
% 3.77/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_35,plain,
% 3.77/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_38,plain,
% 3.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_14,plain,
% 3.77/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.77/0.99      | v2_funct_2(X0,X2)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | ~ v1_funct_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_32,negated_conjecture,
% 3.77/0.99      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_458,plain,
% 3.77/0.99      ( v2_funct_2(X0,X1)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.77/0.99      | ~ v1_funct_1(X0)
% 3.77/0.99      | sK2 != X0
% 3.77/0.99      | sK1 != X1
% 3.77/0.99      | sK1 != X2 ),
% 3.77/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_459,plain,
% 3.77/0.99      ( v2_funct_2(sK2,sK1)
% 3.77/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.77/0.99      | ~ v1_funct_1(sK2) ),
% 3.77/0.99      inference(unflattening,[status(thm)],[c_458]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_460,plain,
% 3.77/0.99      ( v2_funct_2(sK2,sK1) = iProver_top
% 3.77/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5464,plain,
% 3.77/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_5324,c_35,c_38,c_460]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1273,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 3.77/0.99      | k2_relset_1(X1_52,X2_52,X0_52) = k2_relat_1(X0_52) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1793,plain,
% 3.77/0.99      ( k2_relset_1(X0_52,X1_52,X2_52) = k2_relat_1(X2_52)
% 3.77/0.99      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3202,plain,
% 3.77/0.99      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1805,c_1793]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_24,plain,
% 3.77/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.77/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.77/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.77/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.77/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.77/0.99      | ~ v2_funct_1(X2)
% 3.77/0.99      | ~ v1_funct_1(X2)
% 3.77/0.99      | ~ v1_funct_1(X3)
% 3.77/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.77/0.99      | k2_funct_1(X2) = X3
% 3.77/0.99      | k1_xboole_0 = X0
% 3.77/0.99      | k1_xboole_0 = X1 ),
% 3.77/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_23,plain,
% 3.77/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.77/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.77/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.77/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.77/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.77/0.99      | v2_funct_1(X2)
% 3.77/0.99      | ~ v1_funct_1(X2)
% 3.77/0.99      | ~ v1_funct_1(X3) ),
% 3.77/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_191,plain,
% 3.77/0.99      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.77/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.77/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.77/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.77/0.99      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.77/0.99      | ~ v1_funct_1(X2)
% 3.77/0.99      | ~ v1_funct_1(X3)
% 3.77/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.77/0.99      | k2_funct_1(X2) = X3
% 3.77/0.99      | k1_xboole_0 = X0
% 3.77/0.99      | k1_xboole_0 = X1 ),
% 3.77/0.99      inference(global_propositional_subsumption,[status(thm)],[c_24,c_23]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_192,plain,
% 3.77/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.77/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.77/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.77/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.77/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.77/0.99      | ~ v1_funct_1(X2)
% 3.77/0.99      | ~ v1_funct_1(X3)
% 3.77/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.77/0.99      | k2_funct_1(X2) = X3
% 3.77/0.99      | k1_xboole_0 = X1
% 3.77/0.99      | k1_xboole_0 = X0 ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_191]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1258,plain,
% 3.77/0.99      ( ~ r2_relset_1(X0_52,X0_52,k1_partfun1(X0_52,X1_52,X1_52,X0_52,X2_52,X3_52),k6_partfun1(X0_52))
% 3.77/0.99      | ~ v1_funct_2(X3_52,X1_52,X0_52)
% 3.77/0.99      | ~ v1_funct_2(X2_52,X0_52,X1_52)
% 3.77/0.99      | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.77/0.99      | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 3.77/0.99      | ~ v1_funct_1(X2_52)
% 3.77/0.99      | ~ v1_funct_1(X3_52)
% 3.77/0.99      | k2_relset_1(X0_52,X1_52,X2_52) != X1_52
% 3.77/0.99      | k2_funct_1(X2_52) = X3_52
% 3.77/0.99      | k1_xboole_0 = X1_52
% 3.77/0.99      | k1_xboole_0 = X0_52 ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_192]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1808,plain,
% 3.77/0.99      ( k2_relset_1(X0_52,X1_52,X2_52) != X1_52
% 3.77/0.99      | k2_funct_1(X2_52) = X3_52
% 3.77/0.99      | k1_xboole_0 = X1_52
% 3.77/0.99      | k1_xboole_0 = X0_52
% 3.77/0.99      | r2_relset_1(X0_52,X0_52,k1_partfun1(X0_52,X1_52,X1_52,X0_52,X2_52,X3_52),k6_partfun1(X0_52)) != iProver_top
% 3.77/0.99      | v1_funct_2(X3_52,X1_52,X0_52) != iProver_top
% 3.77/0.99      | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
% 3.77/0.99      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.77/0.99      | m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
% 3.77/0.99      | v1_funct_1(X2_52) != iProver_top
% 3.77/0.99      | v1_funct_1(X3_52) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4817,plain,
% 3.77/0.99      ( k2_funct_1(sK2) = X0_52
% 3.77/0.99      | k2_relat_1(sK2) != sK1
% 3.77/0.99      | sK1 = k1_xboole_0
% 3.77/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.77/0.99      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.77/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.77/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.77/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.77/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_3202,c_1808]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_33,negated_conjecture,
% 3.77/0.99      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_36,plain,
% 3.77/0.99      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5245,plain,
% 3.77/0.99      ( v1_funct_1(X0_52) != iProver_top
% 3.77/0.99      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.77/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.77/0.99      | sK1 = k1_xboole_0
% 3.77/0.99      | k2_relat_1(sK2) != sK1
% 3.77/0.99      | k2_funct_1(sK2) = X0_52
% 3.77/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_4817,c_35,c_36,c_38]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5246,plain,
% 3.77/0.99      ( k2_funct_1(sK2) = X0_52
% 3.77/0.99      | k2_relat_1(sK2) != sK1
% 3.77/0.99      | sK1 = k1_xboole_0
% 3.77/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.77/0.99      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.77/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.77/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_5245]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5466,plain,
% 3.77/0.99      ( k2_funct_1(sK2) = X0_52
% 3.77/0.99      | sK1 != sK1
% 3.77/0.99      | sK1 = k1_xboole_0
% 3.77/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.77/0.99      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.77/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.77/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_5464,c_5246]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5468,plain,
% 3.77/0.99      ( k2_funct_1(sK2) = X0_52
% 3.77/0.99      | sK1 = k1_xboole_0
% 3.77/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0_52),k6_partfun1(sK1)) != iProver_top
% 3.77/0.99      | v1_funct_2(X0_52,sK1,sK1) != iProver_top
% 3.77/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.77/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.77/0.99      inference(equality_resolution_simp,[status(thm)],[c_5466]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5756,plain,
% 3.77/0.99      ( k2_funct_1(sK2) = sK3
% 3.77/0.99      | sK1 = k1_xboole_0
% 3.77/0.99      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.77/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.77/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1801,c_5468]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_30,negated_conjecture,
% 3.77/0.99      ( v1_funct_1(sK3) ),
% 3.77/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_29,negated_conjecture,
% 3.77/0.99      ( v1_funct_2(sK3,sK1,sK1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_27,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5757,plain,
% 3.77/0.99      ( ~ v1_funct_2(sK3,sK1,sK1)
% 3.77/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.77/0.99      | ~ v1_funct_1(sK3)
% 3.77/0.99      | k2_funct_1(sK2) = sK3
% 3.77/0.99      | sK1 = k1_xboole_0 ),
% 3.77/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5756]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5798,plain,
% 3.77/0.99      ( sK1 = k1_xboole_0 | k2_funct_1(sK2) = sK3 ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_5756,c_39,c_40,c_42]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5799,plain,
% 3.77/0.99      ( k2_funct_1(sK2) = sK3 | sK1 = k1_xboole_0 ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_5798]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_25,negated_conjecture,
% 3.77/0.99      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1266,negated_conjecture,
% 3.77/0.99      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1800,plain,
% 3.77/0.99      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1266]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_21,plain,
% 3.77/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.77/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.77/0.99      | ~ v1_funct_1(X0)
% 3.77/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_477,plain,
% 3.77/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.77/0.99      | ~ v1_funct_1(X0)
% 3.77/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.77/0.99      | sK2 != X0
% 3.77/0.99      | sK1 != X1 ),
% 3.77/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_478,plain,
% 3.77/0.99      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.77/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.77/0.99      | ~ v1_funct_1(sK2)
% 3.77/0.99      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.77/0.99      inference(unflattening,[status(thm)],[c_477]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_480,plain,
% 3.77/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_478,c_34,c_33,c_31]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1252,plain,
% 3.77/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_480]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1813,plain,
% 3.77/0.99      ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_1800,c_1252]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5800,plain,
% 3.77/0.99      ( sK1 = k1_xboole_0 | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_5799,c_1813]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_42,plain,
% 3.77/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1876,plain,
% 3.77/0.99      ( r2_relset_1(sK1,sK1,sK3,sK3)
% 3.77/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_1272]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1877,plain,
% 3.77/0.99      ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
% 3.77/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1876]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5803,plain,
% 3.77/0.99      ( sK1 = k1_xboole_0 ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_5800,c_42,c_1877]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4,plain,
% 3.77/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1278,plain,
% 3.77/0.99      ( ~ v1_relat_1(X0_52)
% 3.77/0.99      | k2_relat_1(X0_52) != k1_xboole_0
% 3.77/0.99      | k1_xboole_0 = X0_52 ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1789,plain,
% 3.77/0.99      ( k2_relat_1(X0_52) != k1_xboole_0
% 3.77/0.99      | k1_xboole_0 = X0_52
% 3.77/0.99      | v1_relat_1(X0_52) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5472,plain,
% 3.77/0.99      ( sK2 = k1_xboole_0
% 3.77/0.99      | sK1 != k1_xboole_0
% 3.77/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_5464,c_1789]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1275,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 3.77/0.99      | v1_relat_1(X0_52) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1791,plain,
% 3.77/0.99      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 3.77/0.99      | v1_relat_1(X0_52) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1275]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2728,plain,
% 3.77/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1805,c_1791]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5710,plain,
% 3.77/0.99      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.77/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5472,c_2728]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5711,plain,
% 3.77/0.99      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_5710]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5807,plain,
% 3.77/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_5803,c_5711]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5853,plain,
% 3.77/0.99      ( sK2 = k1_xboole_0 ),
% 3.77/0.99      inference(equality_resolution_simp,[status(thm)],[c_5807]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1264,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1802,plain,
% 3.77/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5323,plain,
% 3.77/0.99      ( k2_relat_1(sK3) = sK1 | v2_funct_2(sK3,sK1) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1802,c_1809]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_39,plain,
% 3.77/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_28,negated_conjecture,
% 3.77/0.99      ( v3_funct_2(sK3,sK1,sK1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_447,plain,
% 3.77/0.99      ( v2_funct_2(X0,X1)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.77/0.99      | ~ v1_funct_1(X0)
% 3.77/0.99      | sK3 != X0
% 3.77/0.99      | sK1 != X1
% 3.77/0.99      | sK1 != X2 ),
% 3.77/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_448,plain,
% 3.77/0.99      ( v2_funct_2(sK3,sK1)
% 3.77/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.77/0.99      | ~ v1_funct_1(sK3) ),
% 3.77/0.99      inference(unflattening,[status(thm)],[c_447]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_449,plain,
% 3.77/0.99      ( v2_funct_2(sK3,sK1) = iProver_top
% 3.77/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.77/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5453,plain,
% 3.77/0.99      ( k2_relat_1(sK3) = sK1 ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_5323,c_39,c_42,c_449]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5461,plain,
% 3.77/0.99      ( sK3 = k1_xboole_0
% 3.77/0.99      | sK1 != k1_xboole_0
% 3.77/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_5453,c_1789]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2727,plain,
% 3.77/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1802,c_1791]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5707,plain,
% 3.77/0.99      ( sK1 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.77/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5461,c_2727]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5708,plain,
% 3.77/0.99      ( sK3 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_5707]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5808,plain,
% 3.77/0.99      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_5803,c_5708]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5837,plain,
% 3.77/0.99      ( sK3 = k1_xboole_0 ),
% 3.77/0.99      inference(equality_resolution_simp,[status(thm)],[c_5808]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5827,plain,
% 3.77/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_5803,c_1813]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5847,plain,
% 3.77/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_5837,c_5827]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5854,plain,
% 3.77/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_5853,c_5847]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_13,plain,
% 3.77/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1270,plain,
% 3.77/0.99      ( m1_subset_1(k6_partfun1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_52,X0_52))) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1796,plain,
% 3.77/0.99      ( m1_subset_1(k6_partfun1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_52,X0_52))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | ~ v1_xboole_0(X2)
% 3.77/0.99      | v1_xboole_0(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1274,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 3.77/0.99      | ~ v1_xboole_0(X2_52)
% 3.77/0.99      | v1_xboole_0(X0_52) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1792,plain,
% 3.77/0.99      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 3.77/0.99      | v1_xboole_0(X2_52) != iProver_top
% 3.77/0.99      | v1_xboole_0(X0_52) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1274]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2902,plain,
% 3.77/0.99      ( v1_xboole_0(X0_52) != iProver_top
% 3.77/0.99      | v1_xboole_0(k6_partfun1(X0_52)) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1796,c_1792]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5403,plain,
% 3.77/0.99      ( k6_partfun1(X0_52) = X1_52
% 3.77/0.99      | v1_xboole_0(X0_52) != iProver_top
% 3.77/0.99      | v1_xboole_0(X1_52) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2902,c_1786]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6060,plain,
% 3.77/0.99      ( k6_partfun1(k1_xboole_0) = X0_52 | v1_xboole_0(X0_52) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1785,c_5403]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6069,plain,
% 3.77/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1785,c_6060]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6,plain,
% 3.77/0.99      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1276,plain,
% 3.77/0.99      ( k2_funct_1(k6_partfun1(X0_52)) = k6_partfun1(X0_52) ),
% 3.77/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6527,plain,
% 3.77/0.99      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_6069,c_1276]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6528,plain,
% 3.77/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_6527,c_6069]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6992,plain,
% 3.77/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_5854,c_6528]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6994,plain,
% 3.77/0.99      ( $false ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_4935,c_6992]) ).
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  ------                               Statistics
% 3.77/0.99  
% 3.77/0.99  ------ General
% 3.77/0.99  
% 3.77/0.99  abstr_ref_over_cycles:                  0
% 3.77/0.99  abstr_ref_under_cycles:                 0
% 3.77/0.99  gc_basic_clause_elim:                   0
% 3.77/0.99  forced_gc_time:                         0
% 3.77/0.99  parsing_time:                           0.011
% 3.77/0.99  unif_index_cands_time:                  0.
% 3.77/0.99  unif_index_add_time:                    0.
% 3.77/0.99  orderings_time:                         0.
% 3.77/0.99  out_proof_time:                         0.026
% 3.77/0.99  total_time:                             0.288
% 3.77/0.99  num_of_symbols:                         58
% 3.77/0.99  num_of_terms:                           9110
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing
% 3.77/0.99  
% 3.77/0.99  num_of_splits:                          0
% 3.77/0.99  num_of_split_atoms:                     0
% 3.77/0.99  num_of_reused_defs:                     0
% 3.77/0.99  num_eq_ax_congr_red:                    24
% 3.77/0.99  num_of_sem_filtered_clauses:            3
% 3.77/0.99  num_of_subtypes:                        3
% 3.77/0.99  monotx_restored_types:                  1
% 3.77/0.99  sat_num_of_epr_types:                   0
% 3.77/0.99  sat_num_of_non_cyclic_types:            0
% 3.77/0.99  sat_guarded_non_collapsed_types:        1
% 3.77/0.99  num_pure_diseq_elim:                    0
% 3.77/0.99  simp_replaced_by:                       0
% 3.77/0.99  res_preprocessed:                       160
% 3.77/0.99  prep_upred:                             0
% 3.77/0.99  prep_unflattend:                        66
% 3.77/0.99  smt_new_axioms:                         0
% 3.77/0.99  pred_elim_cands:                        7
% 3.77/0.99  pred_elim:                              2
% 3.77/0.99  pred_elim_cl:                           1
% 3.77/0.99  pred_elim_cycles:                       8
% 3.77/0.99  merged_defs:                            0
% 3.77/0.99  merged_defs_ncl:                        0
% 3.77/0.99  bin_hyper_res:                          0
% 3.77/0.99  prep_cycles:                            4
% 3.77/0.99  pred_elim_time:                         0.015
% 3.77/0.99  splitting_time:                         0.
% 3.77/0.99  sem_filter_time:                        0.
% 3.77/0.99  monotx_time:                            0.001
% 3.77/0.99  subtype_inf_time:                       0.001
% 3.77/0.99  
% 3.77/0.99  ------ Problem properties
% 3.77/0.99  
% 3.77/0.99  clauses:                                31
% 3.77/0.99  conjectures:                            8
% 3.77/0.99  epr:                                    8
% 3.77/0.99  horn:                                   30
% 3.77/0.99  ground:                                 13
% 3.77/0.99  unary:                                  17
% 3.77/0.99  binary:                                 4
% 3.77/0.99  lits:                                   73
% 3.77/0.99  lits_eq:                                15
% 3.77/0.99  fd_pure:                                0
% 3.77/0.99  fd_pseudo:                              0
% 3.77/0.99  fd_cond:                                2
% 3.77/0.99  fd_pseudo_cond:                         4
% 3.77/0.99  ac_symbols:                             0
% 3.77/0.99  
% 3.77/0.99  ------ Propositional Solver
% 3.77/0.99  
% 3.77/0.99  prop_solver_calls:                      28
% 3.77/0.99  prop_fast_solver_calls:                 1310
% 3.77/0.99  smt_solver_calls:                       0
% 3.77/0.99  smt_fast_solver_calls:                  0
% 3.77/0.99  prop_num_of_clauses:                    2847
% 3.77/0.99  prop_preprocess_simplified:             8817
% 3.77/0.99  prop_fo_subsumed:                       50
% 3.77/0.99  prop_solver_time:                       0.
% 3.77/0.99  smt_solver_time:                        0.
% 3.77/0.99  smt_fast_solver_time:                   0.
% 3.77/0.99  prop_fast_solver_time:                  0.
% 3.77/0.99  prop_unsat_core_time:                   0.
% 3.77/0.99  
% 3.77/0.99  ------ QBF
% 3.77/0.99  
% 3.77/0.99  qbf_q_res:                              0
% 3.77/0.99  qbf_num_tautologies:                    0
% 3.77/0.99  qbf_prep_cycles:                        0
% 3.77/0.99  
% 3.77/0.99  ------ BMC1
% 3.77/0.99  
% 3.77/0.99  bmc1_current_bound:                     -1
% 3.77/0.99  bmc1_last_solved_bound:                 -1
% 3.77/0.99  bmc1_unsat_core_size:                   -1
% 3.77/0.99  bmc1_unsat_core_parents_size:           -1
% 3.77/0.99  bmc1_merge_next_fun:                    0
% 3.77/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.77/0.99  
% 3.77/0.99  ------ Instantiation
% 3.77/0.99  
% 3.77/0.99  inst_num_of_clauses:                    820
% 3.77/0.99  inst_num_in_passive:                    3
% 3.77/0.99  inst_num_in_active:                     453
% 3.77/0.99  inst_num_in_unprocessed:                364
% 3.77/0.99  inst_num_of_loops:                      470
% 3.77/0.99  inst_num_of_learning_restarts:          0
% 3.77/0.99  inst_num_moves_active_passive:          15
% 3.77/0.99  inst_lit_activity:                      0
% 3.77/0.99  inst_lit_activity_moves:                0
% 3.77/0.99  inst_num_tautologies:                   0
% 3.77/0.99  inst_num_prop_implied:                  0
% 3.77/0.99  inst_num_existing_simplified:           0
% 3.77/0.99  inst_num_eq_res_simplified:             0
% 3.77/0.99  inst_num_child_elim:                    0
% 3.77/0.99  inst_num_of_dismatching_blockings:      424
% 3.77/0.99  inst_num_of_non_proper_insts:           1226
% 3.77/0.99  inst_num_of_duplicates:                 0
% 3.77/0.99  inst_inst_num_from_inst_to_res:         0
% 3.77/0.99  inst_dismatching_checking_time:         0.
% 3.77/0.99  
% 3.77/0.99  ------ Resolution
% 3.77/0.99  
% 3.77/0.99  res_num_of_clauses:                     0
% 3.77/0.99  res_num_in_passive:                     0
% 3.77/0.99  res_num_in_active:                      0
% 3.77/0.99  res_num_of_loops:                       164
% 3.77/0.99  res_forward_subset_subsumed:            45
% 3.77/0.99  res_backward_subset_subsumed:           0
% 3.77/0.99  res_forward_subsumed:                   0
% 3.77/0.99  res_backward_subsumed:                  0
% 3.77/0.99  res_forward_subsumption_resolution:     4
% 3.77/0.99  res_backward_subsumption_resolution:    0
% 3.77/0.99  res_clause_to_clause_subsumption:       289
% 3.77/0.99  res_orphan_elimination:                 0
% 3.77/0.99  res_tautology_del:                      62
% 3.77/0.99  res_num_eq_res_simplified:              0
% 3.77/0.99  res_num_sel_changes:                    0
% 3.77/0.99  res_moves_from_active_to_pass:          0
% 3.77/0.99  
% 3.77/0.99  ------ Superposition
% 3.77/0.99  
% 3.77/0.99  sup_time_total:                         0.
% 3.77/0.99  sup_time_generating:                    0.
% 3.77/0.99  sup_time_sim_full:                      0.
% 3.77/0.99  sup_time_sim_immed:                     0.
% 3.77/0.99  
% 3.77/0.99  sup_num_of_clauses:                     62
% 3.77/0.99  sup_num_in_active:                      45
% 3.77/0.99  sup_num_in_passive:                     17
% 3.77/0.99  sup_num_of_loops:                       93
% 3.77/0.99  sup_fw_superposition:                   54
% 3.77/0.99  sup_bw_superposition:                   35
% 3.77/0.99  sup_immediate_simplified:               49
% 3.77/0.99  sup_given_eliminated:                   1
% 3.77/0.99  comparisons_done:                       0
% 3.77/0.99  comparisons_avoided:                    3
% 3.77/0.99  
% 3.77/0.99  ------ Simplifications
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  sim_fw_subset_subsumed:                 4
% 3.77/0.99  sim_bw_subset_subsumed:                 4
% 3.77/0.99  sim_fw_subsumed:                        3
% 3.77/0.99  sim_bw_subsumed:                        3
% 3.77/0.99  sim_fw_subsumption_res:                 0
% 3.77/0.99  sim_bw_subsumption_res:                 0
% 3.77/0.99  sim_tautology_del:                      4
% 3.77/0.99  sim_eq_tautology_del:                   13
% 3.77/0.99  sim_eq_res_simp:                        4
% 3.77/0.99  sim_fw_demodulated:                     8
% 3.77/0.99  sim_bw_demodulated:                     75
% 3.77/0.99  sim_light_normalised:                   8
% 3.77/0.99  sim_joinable_taut:                      0
% 3.77/0.99  sim_joinable_simp:                      0
% 3.77/0.99  sim_ac_normalised:                      0
% 3.77/0.99  sim_smt_subsumption:                    0
% 3.77/0.99  
%------------------------------------------------------------------------------
