%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:07 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_35)

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
    inference(ennf_transformation,[],[f18])).

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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45,f44])).

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f71,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f16])).

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
    inference(cnf_transformation,[],[f39])).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f49,f65,f65])).

cnf(c_22,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1164,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1615,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1164])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1160,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1619,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1160])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_364,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_13])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_376,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_364,c_3])).

cnf(c_1156,plain,
    ( ~ v2_funct_2(X0_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
    | k2_relat_1(X0_50) = X1_50 ),
    inference(subtyping,[status(esa)],[c_376])).

cnf(c_1623,plain,
    ( k2_relat_1(X0_50) = X1_50
    | v2_funct_2(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_4717,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1623])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_418,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_419,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_420,plain,
    ( v2_funct_2(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_4804,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4717,c_31,c_34,c_420])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1172,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1607,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_2476,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1619,c_1607])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
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
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_19])).

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
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_1157,plain,
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
    inference(subtyping,[status(esa)],[c_168])).

cnf(c_1622,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_3838,plain,
    ( k2_relat_1(sK1) != sK0
    | k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2476,c_1622])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4355,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0_50
    | k2_relat_1(sK1) != sK0
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3838,c_31,c_32,c_34])).

cnf(c_4356,plain,
    ( k2_relat_1(sK1) != sK0
    | k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_4355])).

cnf(c_4806,plain,
    ( k2_funct_1(sK1) = X0_50
    | sK0 != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4804,c_4356])).

cnf(c_4808,plain,
    ( k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4806])).

cnf(c_5079,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1615,c_4808])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5080,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5079])).

cnf(c_5092,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5079,c_35,c_36,c_38])).

cnf(c_5093,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5092])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1165,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1614,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_437,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_438,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_440,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_30,c_29,c_27])).

cnf(c_1151,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_440])).

cnf(c_1627,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1614,c_1151])).

cnf(c_5094,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_1627])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1171,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1685,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_1686,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1685])).

cnf(c_5097,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5094,c_38,c_1686])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1173,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ v1_xboole_0(X1_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1606,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | v1_xboole_0(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_2625,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1606])).

cnf(c_5113,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5097,c_2625])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_95,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1182,plain,
    ( ~ v1_xboole_0(X0_50)
    | v1_xboole_0(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_2421,plain,
    ( v1_xboole_0(X0_50)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_50 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1182])).

cnf(c_2422,plain,
    ( X0_50 != k1_xboole_0
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2421])).

cnf(c_2424,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_6286,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5113,c_38,c_95,c_1686,c_2424,c_2625,c_5094])).

cnf(c_1176,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1604,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1176])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1175,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(X1_50)
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1605,plain,
    ( X0_50 = X1_50
    | v1_xboole_0(X0_50) != iProver_top
    | v1_xboole_0(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_2346,plain,
    ( k1_xboole_0 = X0_50
    | v1_xboole_0(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1604,c_1605])).

cnf(c_6299,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6286,c_2346])).

cnf(c_5117,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5097,c_1627])).

cnf(c_7346,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6299,c_5117])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1167,plain,
    ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1612,plain,
    ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_2626,plain,
    ( v1_xboole_0(X0_50) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_1606])).

cnf(c_3366,plain,
    ( k6_partfun1(X0_50) = k1_xboole_0
    | v1_xboole_0(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2626,c_2346])).

cnf(c_3540,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1604,c_3366])).

cnf(c_2,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1174,plain,
    ( k2_funct_1(k6_partfun1(X0_50)) = k6_partfun1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3679,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3540,c_1174])).

cnf(c_3680,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3679,c_3540])).

cnf(c_1163,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1616,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_2624,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_1606])).

cnf(c_5114,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5097,c_2624])).

cnf(c_6374,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5114,c_38,c_95,c_1686,c_2424,c_2624,c_5094])).

cnf(c_6387,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6374,c_2346])).

cnf(c_7355,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7346,c_3680,c_6387])).

cnf(c_1608,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_2635,plain,
    ( r2_relset_1(X0_50,X0_50,k6_partfun1(X0_50),k6_partfun1(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_1608])).

cnf(c_3674,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3540,c_2635])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7355,c_3674])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:54:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.93/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/0.99  
% 3.93/0.99  ------  iProver source info
% 3.93/0.99  
% 3.93/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.93/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/0.99  git: non_committed_changes: false
% 3.93/0.99  git: last_make_outside_of_git: false
% 3.93/0.99  
% 3.93/0.99  ------ 
% 3.93/0.99  
% 3.93/0.99  ------ Input Options
% 3.93/0.99  
% 3.93/0.99  --out_options                           all
% 3.93/0.99  --tptp_safe_out                         true
% 3.93/0.99  --problem_path                          ""
% 3.93/0.99  --include_path                          ""
% 3.93/0.99  --clausifier                            res/vclausify_rel
% 3.93/0.99  --clausifier_options                    ""
% 3.93/0.99  --stdin                                 false
% 3.93/0.99  --stats_out                             all
% 3.93/0.99  
% 3.93/0.99  ------ General Options
% 3.93/0.99  
% 3.93/0.99  --fof                                   false
% 3.93/0.99  --time_out_real                         305.
% 3.93/0.99  --time_out_virtual                      -1.
% 3.93/0.99  --symbol_type_check                     false
% 3.93/0.99  --clausify_out                          false
% 3.93/0.99  --sig_cnt_out                           false
% 3.93/0.99  --trig_cnt_out                          false
% 3.93/0.99  --trig_cnt_out_tolerance                1.
% 3.93/0.99  --trig_cnt_out_sk_spl                   false
% 3.93/0.99  --abstr_cl_out                          false
% 3.93/0.99  
% 3.93/0.99  ------ Global Options
% 3.93/0.99  
% 3.93/0.99  --schedule                              default
% 3.93/0.99  --add_important_lit                     false
% 3.93/0.99  --prop_solver_per_cl                    1000
% 3.93/0.99  --min_unsat_core                        false
% 3.93/0.99  --soft_assumptions                      false
% 3.93/0.99  --soft_lemma_size                       3
% 3.93/0.99  --prop_impl_unit_size                   0
% 3.93/0.99  --prop_impl_unit                        []
% 3.93/0.99  --share_sel_clauses                     true
% 3.93/0.99  --reset_solvers                         false
% 3.93/0.99  --bc_imp_inh                            [conj_cone]
% 3.93/0.99  --conj_cone_tolerance                   3.
% 3.93/0.99  --extra_neg_conj                        none
% 3.93/0.99  --large_theory_mode                     true
% 3.93/0.99  --prolific_symb_bound                   200
% 3.93/0.99  --lt_threshold                          2000
% 3.93/0.99  --clause_weak_htbl                      true
% 3.93/0.99  --gc_record_bc_elim                     false
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing Options
% 3.93/0.99  
% 3.93/0.99  --preprocessing_flag                    true
% 3.93/0.99  --time_out_prep_mult                    0.1
% 3.93/0.99  --splitting_mode                        input
% 3.93/0.99  --splitting_grd                         true
% 3.93/0.99  --splitting_cvd                         false
% 3.93/0.99  --splitting_cvd_svl                     false
% 3.93/0.99  --splitting_nvd                         32
% 3.93/0.99  --sub_typing                            true
% 3.93/0.99  --prep_gs_sim                           true
% 3.93/0.99  --prep_unflatten                        true
% 3.93/0.99  --prep_res_sim                          true
% 3.93/0.99  --prep_upred                            true
% 3.93/0.99  --prep_sem_filter                       exhaustive
% 3.93/0.99  --prep_sem_filter_out                   false
% 3.93/0.99  --pred_elim                             true
% 3.93/0.99  --res_sim_input                         true
% 3.93/0.99  --eq_ax_congr_red                       true
% 3.93/0.99  --pure_diseq_elim                       true
% 3.93/0.99  --brand_transform                       false
% 3.93/0.99  --non_eq_to_eq                          false
% 3.93/0.99  --prep_def_merge                        true
% 3.93/0.99  --prep_def_merge_prop_impl              false
% 3.93/0.99  --prep_def_merge_mbd                    true
% 3.93/0.99  --prep_def_merge_tr_red                 false
% 3.93/0.99  --prep_def_merge_tr_cl                  false
% 3.93/0.99  --smt_preprocessing                     true
% 3.93/0.99  --smt_ac_axioms                         fast
% 3.93/0.99  --preprocessed_out                      false
% 3.93/0.99  --preprocessed_stats                    false
% 3.93/0.99  
% 3.93/0.99  ------ Abstraction refinement Options
% 3.93/0.99  
% 3.93/0.99  --abstr_ref                             []
% 3.93/0.99  --abstr_ref_prep                        false
% 3.93/0.99  --abstr_ref_until_sat                   false
% 3.93/0.99  --abstr_ref_sig_restrict                funpre
% 3.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/0.99  --abstr_ref_under                       []
% 3.93/0.99  
% 3.93/0.99  ------ SAT Options
% 3.93/0.99  
% 3.93/0.99  --sat_mode                              false
% 3.93/0.99  --sat_fm_restart_options                ""
% 3.93/0.99  --sat_gr_def                            false
% 3.93/0.99  --sat_epr_types                         true
% 3.93/0.99  --sat_non_cyclic_types                  false
% 3.93/0.99  --sat_finite_models                     false
% 3.93/0.99  --sat_fm_lemmas                         false
% 3.93/0.99  --sat_fm_prep                           false
% 3.93/0.99  --sat_fm_uc_incr                        true
% 3.93/0.99  --sat_out_model                         small
% 3.93/0.99  --sat_out_clauses                       false
% 3.93/0.99  
% 3.93/0.99  ------ QBF Options
% 3.93/0.99  
% 3.93/0.99  --qbf_mode                              false
% 3.93/0.99  --qbf_elim_univ                         false
% 3.93/0.99  --qbf_dom_inst                          none
% 3.93/0.99  --qbf_dom_pre_inst                      false
% 3.93/0.99  --qbf_sk_in                             false
% 3.93/0.99  --qbf_pred_elim                         true
% 3.93/0.99  --qbf_split                             512
% 3.93/0.99  
% 3.93/0.99  ------ BMC1 Options
% 3.93/0.99  
% 3.93/0.99  --bmc1_incremental                      false
% 3.93/0.99  --bmc1_axioms                           reachable_all
% 3.93/0.99  --bmc1_min_bound                        0
% 3.93/0.99  --bmc1_max_bound                        -1
% 3.93/0.99  --bmc1_max_bound_default                -1
% 3.93/0.99  --bmc1_symbol_reachability              true
% 3.93/0.99  --bmc1_property_lemmas                  false
% 3.93/0.99  --bmc1_k_induction                      false
% 3.93/0.99  --bmc1_non_equiv_states                 false
% 3.93/0.99  --bmc1_deadlock                         false
% 3.93/0.99  --bmc1_ucm                              false
% 3.93/0.99  --bmc1_add_unsat_core                   none
% 3.93/0.99  --bmc1_unsat_core_children              false
% 3.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/0.99  --bmc1_out_stat                         full
% 3.93/0.99  --bmc1_ground_init                      false
% 3.93/0.99  --bmc1_pre_inst_next_state              false
% 3.93/0.99  --bmc1_pre_inst_state                   false
% 3.93/0.99  --bmc1_pre_inst_reach_state             false
% 3.93/0.99  --bmc1_out_unsat_core                   false
% 3.93/0.99  --bmc1_aig_witness_out                  false
% 3.93/0.99  --bmc1_verbose                          false
% 3.93/0.99  --bmc1_dump_clauses_tptp                false
% 3.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.93/0.99  --bmc1_dump_file                        -
% 3.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.93/0.99  --bmc1_ucm_extend_mode                  1
% 3.93/0.99  --bmc1_ucm_init_mode                    2
% 3.93/0.99  --bmc1_ucm_cone_mode                    none
% 3.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.93/0.99  --bmc1_ucm_relax_model                  4
% 3.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/0.99  --bmc1_ucm_layered_model                none
% 3.93/0.99  --bmc1_ucm_max_lemma_size               10
% 3.93/0.99  
% 3.93/0.99  ------ AIG Options
% 3.93/0.99  
% 3.93/0.99  --aig_mode                              false
% 3.93/0.99  
% 3.93/0.99  ------ Instantiation Options
% 3.93/0.99  
% 3.93/0.99  --instantiation_flag                    true
% 3.93/0.99  --inst_sos_flag                         true
% 3.93/0.99  --inst_sos_phase                        true
% 3.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/0.99  --inst_lit_sel_side                     num_symb
% 3.93/0.99  --inst_solver_per_active                1400
% 3.93/0.99  --inst_solver_calls_frac                1.
% 3.93/0.99  --inst_passive_queue_type               priority_queues
% 3.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/0.99  --inst_passive_queues_freq              [25;2]
% 3.93/0.99  --inst_dismatching                      true
% 3.93/0.99  --inst_eager_unprocessed_to_passive     true
% 3.93/0.99  --inst_prop_sim_given                   true
% 3.93/0.99  --inst_prop_sim_new                     false
% 3.93/0.99  --inst_subs_new                         false
% 3.93/0.99  --inst_eq_res_simp                      false
% 3.93/0.99  --inst_subs_given                       false
% 3.93/0.99  --inst_orphan_elimination               true
% 3.93/0.99  --inst_learning_loop_flag               true
% 3.93/0.99  --inst_learning_start                   3000
% 3.93/0.99  --inst_learning_factor                  2
% 3.93/0.99  --inst_start_prop_sim_after_learn       3
% 3.93/0.99  --inst_sel_renew                        solver
% 3.93/0.99  --inst_lit_activity_flag                true
% 3.93/0.99  --inst_restr_to_given                   false
% 3.93/0.99  --inst_activity_threshold               500
% 3.93/0.99  --inst_out_proof                        true
% 3.93/0.99  
% 3.93/0.99  ------ Resolution Options
% 3.93/0.99  
% 3.93/0.99  --resolution_flag                       true
% 3.93/0.99  --res_lit_sel                           adaptive
% 3.93/0.99  --res_lit_sel_side                      none
% 3.93/0.99  --res_ordering                          kbo
% 3.93/0.99  --res_to_prop_solver                    active
% 3.93/0.99  --res_prop_simpl_new                    false
% 3.93/0.99  --res_prop_simpl_given                  true
% 3.93/0.99  --res_passive_queue_type                priority_queues
% 3.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/0.99  --res_passive_queues_freq               [15;5]
% 3.93/0.99  --res_forward_subs                      full
% 3.93/0.99  --res_backward_subs                     full
% 3.93/0.99  --res_forward_subs_resolution           true
% 3.93/0.99  --res_backward_subs_resolution          true
% 3.93/0.99  --res_orphan_elimination                true
% 3.93/0.99  --res_time_limit                        2.
% 3.93/0.99  --res_out_proof                         true
% 3.93/0.99  
% 3.93/0.99  ------ Superposition Options
% 3.93/0.99  
% 3.93/0.99  --superposition_flag                    true
% 3.93/0.99  --sup_passive_queue_type                priority_queues
% 3.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.93/0.99  --demod_completeness_check              fast
% 3.93/0.99  --demod_use_ground                      true
% 3.93/0.99  --sup_to_prop_solver                    passive
% 3.93/0.99  --sup_prop_simpl_new                    true
% 3.93/0.99  --sup_prop_simpl_given                  true
% 3.93/0.99  --sup_fun_splitting                     true
% 3.93/0.99  --sup_smt_interval                      50000
% 3.93/0.99  
% 3.93/0.99  ------ Superposition Simplification Setup
% 3.93/0.99  
% 3.93/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/0.99  --sup_immed_triv                        [TrivRules]
% 3.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.99  --sup_immed_bw_main                     []
% 3.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.99  --sup_input_bw                          []
% 3.93/0.99  
% 3.93/0.99  ------ Combination Options
% 3.93/0.99  
% 3.93/0.99  --comb_res_mult                         3
% 3.93/0.99  --comb_sup_mult                         2
% 3.93/0.99  --comb_inst_mult                        10
% 3.93/0.99  
% 3.93/0.99  ------ Debug Options
% 3.93/0.99  
% 3.93/0.99  --dbg_backtrace                         false
% 3.93/0.99  --dbg_dump_prop_clauses                 false
% 3.93/0.99  --dbg_dump_prop_clauses_file            -
% 3.93/0.99  --dbg_out_stat                          false
% 3.93/0.99  ------ Parsing...
% 3.93/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/0.99  ------ Proving...
% 3.93/0.99  ------ Problem Properties 
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  clauses                                 26
% 3.93/0.99  conjectures                             8
% 3.93/0.99  EPR                                     8
% 3.93/0.99  Horn                                    25
% 3.93/0.99  unary                                   15
% 3.93/0.99  binary                                  3
% 3.93/0.99  lits                                    63
% 3.93/0.99  lits eq                                 11
% 3.93/0.99  fd_pure                                 0
% 3.93/0.99  fd_pseudo                               0
% 3.93/0.99  fd_cond                                 0
% 3.93/0.99  fd_pseudo_cond                          4
% 3.93/0.99  AC symbols                              0
% 3.93/0.99  
% 3.93/0.99  ------ Schedule dynamic 5 is on 
% 3.93/0.99  
% 3.93/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  ------ 
% 3.93/0.99  Current options:
% 3.93/0.99  ------ 
% 3.93/0.99  
% 3.93/0.99  ------ Input Options
% 3.93/0.99  
% 3.93/0.99  --out_options                           all
% 3.93/0.99  --tptp_safe_out                         true
% 3.93/0.99  --problem_path                          ""
% 3.93/0.99  --include_path                          ""
% 3.93/0.99  --clausifier                            res/vclausify_rel
% 3.93/0.99  --clausifier_options                    ""
% 3.93/0.99  --stdin                                 false
% 3.93/0.99  --stats_out                             all
% 3.93/0.99  
% 3.93/0.99  ------ General Options
% 3.93/0.99  
% 3.93/0.99  --fof                                   false
% 3.93/0.99  --time_out_real                         305.
% 3.93/0.99  --time_out_virtual                      -1.
% 3.93/0.99  --symbol_type_check                     false
% 3.93/0.99  --clausify_out                          false
% 3.93/0.99  --sig_cnt_out                           false
% 3.93/0.99  --trig_cnt_out                          false
% 3.93/0.99  --trig_cnt_out_tolerance                1.
% 3.93/0.99  --trig_cnt_out_sk_spl                   false
% 3.93/0.99  --abstr_cl_out                          false
% 3.93/0.99  
% 3.93/0.99  ------ Global Options
% 3.93/0.99  
% 3.93/0.99  --schedule                              default
% 3.93/0.99  --add_important_lit                     false
% 3.93/0.99  --prop_solver_per_cl                    1000
% 3.93/0.99  --min_unsat_core                        false
% 3.93/0.99  --soft_assumptions                      false
% 3.93/0.99  --soft_lemma_size                       3
% 3.93/0.99  --prop_impl_unit_size                   0
% 3.93/0.99  --prop_impl_unit                        []
% 3.93/0.99  --share_sel_clauses                     true
% 3.93/0.99  --reset_solvers                         false
% 3.93/0.99  --bc_imp_inh                            [conj_cone]
% 3.93/0.99  --conj_cone_tolerance                   3.
% 3.93/0.99  --extra_neg_conj                        none
% 3.93/0.99  --large_theory_mode                     true
% 3.93/0.99  --prolific_symb_bound                   200
% 3.93/0.99  --lt_threshold                          2000
% 3.93/0.99  --clause_weak_htbl                      true
% 3.93/0.99  --gc_record_bc_elim                     false
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing Options
% 3.93/0.99  
% 3.93/0.99  --preprocessing_flag                    true
% 3.93/0.99  --time_out_prep_mult                    0.1
% 3.93/0.99  --splitting_mode                        input
% 3.93/0.99  --splitting_grd                         true
% 3.93/0.99  --splitting_cvd                         false
% 3.93/0.99  --splitting_cvd_svl                     false
% 3.93/0.99  --splitting_nvd                         32
% 3.93/0.99  --sub_typing                            true
% 3.93/0.99  --prep_gs_sim                           true
% 3.93/0.99  --prep_unflatten                        true
% 3.93/0.99  --prep_res_sim                          true
% 3.93/0.99  --prep_upred                            true
% 3.93/0.99  --prep_sem_filter                       exhaustive
% 3.93/0.99  --prep_sem_filter_out                   false
% 3.93/0.99  --pred_elim                             true
% 3.93/0.99  --res_sim_input                         true
% 3.93/0.99  --eq_ax_congr_red                       true
% 3.93/0.99  --pure_diseq_elim                       true
% 3.93/0.99  --brand_transform                       false
% 3.93/0.99  --non_eq_to_eq                          false
% 3.93/0.99  --prep_def_merge                        true
% 3.93/0.99  --prep_def_merge_prop_impl              false
% 3.93/0.99  --prep_def_merge_mbd                    true
% 3.93/0.99  --prep_def_merge_tr_red                 false
% 3.93/0.99  --prep_def_merge_tr_cl                  false
% 3.93/0.99  --smt_preprocessing                     true
% 3.93/0.99  --smt_ac_axioms                         fast
% 3.93/0.99  --preprocessed_out                      false
% 3.93/0.99  --preprocessed_stats                    false
% 3.93/0.99  
% 3.93/0.99  ------ Abstraction refinement Options
% 3.93/0.99  
% 3.93/0.99  --abstr_ref                             []
% 3.93/0.99  --abstr_ref_prep                        false
% 3.93/0.99  --abstr_ref_until_sat                   false
% 3.93/0.99  --abstr_ref_sig_restrict                funpre
% 3.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/0.99  --abstr_ref_under                       []
% 3.93/0.99  
% 3.93/0.99  ------ SAT Options
% 3.93/0.99  
% 3.93/0.99  --sat_mode                              false
% 3.93/0.99  --sat_fm_restart_options                ""
% 3.93/0.99  --sat_gr_def                            false
% 3.93/0.99  --sat_epr_types                         true
% 3.93/0.99  --sat_non_cyclic_types                  false
% 3.93/0.99  --sat_finite_models                     false
% 3.93/0.99  --sat_fm_lemmas                         false
% 3.93/0.99  --sat_fm_prep                           false
% 3.93/0.99  --sat_fm_uc_incr                        true
% 3.93/0.99  --sat_out_model                         small
% 3.93/0.99  --sat_out_clauses                       false
% 3.93/0.99  
% 3.93/0.99  ------ QBF Options
% 3.93/0.99  
% 3.93/0.99  --qbf_mode                              false
% 3.93/0.99  --qbf_elim_univ                         false
% 3.93/0.99  --qbf_dom_inst                          none
% 3.93/0.99  --qbf_dom_pre_inst                      false
% 3.93/0.99  --qbf_sk_in                             false
% 3.93/0.99  --qbf_pred_elim                         true
% 3.93/0.99  --qbf_split                             512
% 3.93/0.99  
% 3.93/0.99  ------ BMC1 Options
% 3.93/0.99  
% 3.93/0.99  --bmc1_incremental                      false
% 3.93/0.99  --bmc1_axioms                           reachable_all
% 3.93/0.99  --bmc1_min_bound                        0
% 3.93/0.99  --bmc1_max_bound                        -1
% 3.93/0.99  --bmc1_max_bound_default                -1
% 3.93/0.99  --bmc1_symbol_reachability              true
% 3.93/0.99  --bmc1_property_lemmas                  false
% 3.93/0.99  --bmc1_k_induction                      false
% 3.93/0.99  --bmc1_non_equiv_states                 false
% 3.93/0.99  --bmc1_deadlock                         false
% 3.93/0.99  --bmc1_ucm                              false
% 3.93/0.99  --bmc1_add_unsat_core                   none
% 3.93/0.99  --bmc1_unsat_core_children              false
% 3.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/0.99  --bmc1_out_stat                         full
% 3.93/0.99  --bmc1_ground_init                      false
% 3.93/0.99  --bmc1_pre_inst_next_state              false
% 3.93/0.99  --bmc1_pre_inst_state                   false
% 3.93/0.99  --bmc1_pre_inst_reach_state             false
% 3.93/0.99  --bmc1_out_unsat_core                   false
% 3.93/0.99  --bmc1_aig_witness_out                  false
% 3.93/0.99  --bmc1_verbose                          false
% 3.93/0.99  --bmc1_dump_clauses_tptp                false
% 3.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.93/0.99  --bmc1_dump_file                        -
% 3.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.93/0.99  --bmc1_ucm_extend_mode                  1
% 3.93/0.99  --bmc1_ucm_init_mode                    2
% 3.93/0.99  --bmc1_ucm_cone_mode                    none
% 3.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.93/0.99  --bmc1_ucm_relax_model                  4
% 3.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/0.99  --bmc1_ucm_layered_model                none
% 3.93/0.99  --bmc1_ucm_max_lemma_size               10
% 3.93/0.99  
% 3.93/0.99  ------ AIG Options
% 3.93/0.99  
% 3.93/0.99  --aig_mode                              false
% 3.93/0.99  
% 3.93/0.99  ------ Instantiation Options
% 3.93/0.99  
% 3.93/0.99  --instantiation_flag                    true
% 3.93/0.99  --inst_sos_flag                         true
% 3.93/0.99  --inst_sos_phase                        true
% 3.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/0.99  --inst_lit_sel_side                     none
% 3.93/0.99  --inst_solver_per_active                1400
% 3.93/0.99  --inst_solver_calls_frac                1.
% 3.93/0.99  --inst_passive_queue_type               priority_queues
% 3.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/0.99  --inst_passive_queues_freq              [25;2]
% 3.93/0.99  --inst_dismatching                      true
% 3.93/0.99  --inst_eager_unprocessed_to_passive     true
% 3.93/0.99  --inst_prop_sim_given                   true
% 3.93/0.99  --inst_prop_sim_new                     false
% 3.93/0.99  --inst_subs_new                         false
% 3.93/0.99  --inst_eq_res_simp                      false
% 3.93/0.99  --inst_subs_given                       false
% 3.93/0.99  --inst_orphan_elimination               true
% 3.93/0.99  --inst_learning_loop_flag               true
% 3.93/0.99  --inst_learning_start                   3000
% 3.93/0.99  --inst_learning_factor                  2
% 3.93/0.99  --inst_start_prop_sim_after_learn       3
% 3.93/0.99  --inst_sel_renew                        solver
% 3.93/0.99  --inst_lit_activity_flag                true
% 3.93/0.99  --inst_restr_to_given                   false
% 3.93/0.99  --inst_activity_threshold               500
% 3.93/0.99  --inst_out_proof                        true
% 3.93/0.99  
% 3.93/0.99  ------ Resolution Options
% 3.93/0.99  
% 3.93/0.99  --resolution_flag                       false
% 3.93/0.99  --res_lit_sel                           adaptive
% 3.93/0.99  --res_lit_sel_side                      none
% 3.93/0.99  --res_ordering                          kbo
% 3.93/0.99  --res_to_prop_solver                    active
% 3.93/0.99  --res_prop_simpl_new                    false
% 3.93/0.99  --res_prop_simpl_given                  true
% 3.93/0.99  --res_passive_queue_type                priority_queues
% 3.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/0.99  --res_passive_queues_freq               [15;5]
% 3.93/0.99  --res_forward_subs                      full
% 3.93/0.99  --res_backward_subs                     full
% 3.93/0.99  --res_forward_subs_resolution           true
% 3.93/0.99  --res_backward_subs_resolution          true
% 3.93/0.99  --res_orphan_elimination                true
% 3.93/0.99  --res_time_limit                        2.
% 3.93/0.99  --res_out_proof                         true
% 3.93/0.99  
% 3.93/0.99  ------ Superposition Options
% 3.93/0.99  
% 3.93/0.99  --superposition_flag                    true
% 3.93/0.99  --sup_passive_queue_type                priority_queues
% 3.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.93/0.99  --demod_completeness_check              fast
% 3.93/0.99  --demod_use_ground                      true
% 3.93/0.99  --sup_to_prop_solver                    passive
% 3.93/0.99  --sup_prop_simpl_new                    true
% 3.93/0.99  --sup_prop_simpl_given                  true
% 3.93/0.99  --sup_fun_splitting                     true
% 3.93/0.99  --sup_smt_interval                      50000
% 3.93/0.99  
% 3.93/0.99  ------ Superposition Simplification Setup
% 3.93/0.99  
% 3.93/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/0.99  --sup_immed_triv                        [TrivRules]
% 3.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.99  --sup_immed_bw_main                     []
% 3.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.99  --sup_input_bw                          []
% 3.93/0.99  
% 3.93/0.99  ------ Combination Options
% 3.93/0.99  
% 3.93/0.99  --comb_res_mult                         3
% 3.93/0.99  --comb_sup_mult                         2
% 3.93/0.99  --comb_inst_mult                        10
% 3.93/0.99  
% 3.93/0.99  ------ Debug Options
% 3.93/0.99  
% 3.93/0.99  --dbg_backtrace                         false
% 3.93/0.99  --dbg_dump_prop_clauses                 false
% 3.93/0.99  --dbg_dump_prop_clauses_file            -
% 3.93/0.99  --dbg_out_stat                          false
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  ------ Proving...
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  % SZS status Theorem for theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  fof(f17,conjecture,(
% 3.93/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f18,negated_conjecture,(
% 3.93/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.93/0.99    inference(negated_conjecture,[],[f17])).
% 3.93/0.99  
% 3.93/0.99  fof(f40,plain,(
% 3.93/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.93/0.99    inference(ennf_transformation,[],[f18])).
% 3.93/0.99  
% 3.93/0.99  fof(f41,plain,(
% 3.93/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.93/0.99    inference(flattening,[],[f40])).
% 3.93/0.99  
% 3.93/0.99  fof(f45,plain,(
% 3.93/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.93/0.99    introduced(choice_axiom,[])).
% 3.93/0.99  
% 3.93/0.99  fof(f44,plain,(
% 3.93/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.93/0.99    introduced(choice_axiom,[])).
% 3.93/0.99  
% 3.93/0.99  fof(f46,plain,(
% 3.93/0.99    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45,f44])).
% 3.93/0.99  
% 3.93/0.99  fof(f77,plain,(
% 3.93/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.93/0.99    inference(cnf_transformation,[],[f46])).
% 3.93/0.99  
% 3.93/0.99  fof(f72,plain,(
% 3.93/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.93/0.99    inference(cnf_transformation,[],[f46])).
% 3.93/0.99  
% 3.93/0.99  fof(f5,axiom,(
% 3.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f20,plain,(
% 3.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.93/0.99    inference(pure_predicate_removal,[],[f5])).
% 3.93/0.99  
% 3.93/0.99  fof(f23,plain,(
% 3.93/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/0.99    inference(ennf_transformation,[],[f20])).
% 3.93/0.99  
% 3.93/0.99  fof(f51,plain,(
% 3.93/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/0.99    inference(cnf_transformation,[],[f23])).
% 3.93/0.99  
% 3.93/0.99  fof(f10,axiom,(
% 3.93/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f30,plain,(
% 3.93/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.93/0.99    inference(ennf_transformation,[],[f10])).
% 3.93/0.99  
% 3.93/0.99  fof(f31,plain,(
% 3.93/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.93/0.99    inference(flattening,[],[f30])).
% 3.93/0.99  
% 3.93/0.99  fof(f43,plain,(
% 3.93/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.93/0.99    inference(nnf_transformation,[],[f31])).
% 3.93/0.99  
% 3.93/0.99  fof(f59,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f43])).
% 3.93/0.99  
% 3.93/0.99  fof(f4,axiom,(
% 3.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f22,plain,(
% 3.93/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/0.99    inference(ennf_transformation,[],[f4])).
% 3.93/0.99  
% 3.93/0.99  fof(f50,plain,(
% 3.93/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/0.99    inference(cnf_transformation,[],[f22])).
% 3.93/0.99  
% 3.93/0.99  fof(f69,plain,(
% 3.93/0.99    v1_funct_1(sK1)),
% 3.93/0.99    inference(cnf_transformation,[],[f46])).
% 3.93/0.99  
% 3.93/0.99  fof(f9,axiom,(
% 3.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f28,plain,(
% 3.93/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/0.99    inference(ennf_transformation,[],[f9])).
% 3.93/0.99  
% 3.93/0.99  fof(f29,plain,(
% 3.93/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/0.99    inference(flattening,[],[f28])).
% 3.93/0.99  
% 3.93/0.99  fof(f58,plain,(
% 3.93/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/0.99    inference(cnf_transformation,[],[f29])).
% 3.93/0.99  
% 3.93/0.99  fof(f71,plain,(
% 3.93/0.99    v3_funct_2(sK1,sK0,sK0)),
% 3.93/0.99    inference(cnf_transformation,[],[f46])).
% 3.93/0.99  
% 3.93/0.99  fof(f7,axiom,(
% 3.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f25,plain,(
% 3.93/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/0.99    inference(ennf_transformation,[],[f7])).
% 3.93/0.99  
% 3.93/0.99  fof(f53,plain,(
% 3.93/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/0.99    inference(cnf_transformation,[],[f25])).
% 3.93/0.99  
% 3.93/0.99  fof(f16,axiom,(
% 3.93/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f38,plain,(
% 3.93/0.99    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.93/0.99    inference(ennf_transformation,[],[f16])).
% 3.93/0.99  
% 3.93/0.99  fof(f39,plain,(
% 3.93/0.99    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.93/0.99    inference(flattening,[],[f38])).
% 3.93/0.99  
% 3.93/0.99  fof(f68,plain,(
% 3.93/0.99    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f39])).
% 3.93/0.99  
% 3.93/0.99  fof(f15,axiom,(
% 3.93/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f36,plain,(
% 3.93/0.99    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.93/0.99    inference(ennf_transformation,[],[f15])).
% 3.93/0.99  
% 3.93/0.99  fof(f37,plain,(
% 3.93/0.99    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.93/0.99    inference(flattening,[],[f36])).
% 3.93/0.99  
% 3.93/0.99  fof(f66,plain,(
% 3.93/0.99    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f37])).
% 3.93/1.00  
% 3.93/1.00  fof(f70,plain,(
% 3.93/1.00    v1_funct_2(sK1,sK0,sK0)),
% 3.93/1.00    inference(cnf_transformation,[],[f46])).
% 3.93/1.00  
% 3.93/1.00  fof(f73,plain,(
% 3.93/1.00    v1_funct_1(sK2)),
% 3.93/1.00    inference(cnf_transformation,[],[f46])).
% 3.93/1.00  
% 3.93/1.00  fof(f74,plain,(
% 3.93/1.00    v1_funct_2(sK2,sK0,sK0)),
% 3.93/1.00    inference(cnf_transformation,[],[f46])).
% 3.93/1.00  
% 3.93/1.00  fof(f76,plain,(
% 3.93/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.93/1.00    inference(cnf_transformation,[],[f46])).
% 3.93/1.00  
% 3.93/1.00  fof(f78,plain,(
% 3.93/1.00    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.93/1.00    inference(cnf_transformation,[],[f46])).
% 3.93/1.00  
% 3.93/1.00  fof(f13,axiom,(
% 3.93/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f34,plain,(
% 3.93/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.93/1.00    inference(ennf_transformation,[],[f13])).
% 3.93/1.00  
% 3.93/1.00  fof(f35,plain,(
% 3.93/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.93/1.00    inference(flattening,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f64,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f35])).
% 3.93/1.00  
% 3.93/1.00  fof(f8,axiom,(
% 3.93/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f26,plain,(
% 3.93/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.93/1.00    inference(ennf_transformation,[],[f8])).
% 3.93/1.00  
% 3.93/1.00  fof(f27,plain,(
% 3.93/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.00    inference(flattening,[],[f26])).
% 3.93/1.00  
% 3.93/1.00  fof(f42,plain,(
% 3.93/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.00    inference(nnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f55,plain,(
% 3.93/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f42])).
% 3.93/1.00  
% 3.93/1.00  fof(f80,plain,(
% 3.93/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/1.00    inference(equality_resolution,[],[f55])).
% 3.93/1.00  
% 3.93/1.00  fof(f6,axiom,(
% 3.93/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f24,plain,(
% 3.93/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.93/1.00    inference(ennf_transformation,[],[f6])).
% 3.93/1.00  
% 3.93/1.00  fof(f52,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f24])).
% 3.93/1.00  
% 3.93/1.00  fof(f1,axiom,(
% 3.93/1.00    v1_xboole_0(k1_xboole_0)),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f47,plain,(
% 3.93/1.00    v1_xboole_0(k1_xboole_0)),
% 3.93/1.00    inference(cnf_transformation,[],[f1])).
% 3.93/1.00  
% 3.93/1.00  fof(f2,axiom,(
% 3.93/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f21,plain,(
% 3.93/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.93/1.00    inference(ennf_transformation,[],[f2])).
% 3.93/1.00  
% 3.93/1.00  fof(f48,plain,(
% 3.93/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f21])).
% 3.93/1.00  
% 3.93/1.00  fof(f12,axiom,(
% 3.93/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f19,plain,(
% 3.93/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.93/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.93/1.00  
% 3.93/1.00  fof(f63,plain,(
% 3.93/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f19])).
% 3.93/1.00  
% 3.93/1.00  fof(f3,axiom,(
% 3.93/1.00    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f49,plain,(
% 3.93/1.00    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f3])).
% 3.93/1.00  
% 3.93/1.00  fof(f14,axiom,(
% 3.93/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f65,plain,(
% 3.93/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f14])).
% 3.93/1.00  
% 3.93/1.00  fof(f79,plain,(
% 3.93/1.00    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.93/1.00    inference(definition_unfolding,[],[f49,f65,f65])).
% 3.93/1.00  
% 3.93/1.00  cnf(c_22,negated_conjecture,
% 3.93/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1164,negated_conjecture,
% 3.93/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1615,plain,
% 3.93/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1164]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_27,negated_conjecture,
% 3.93/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.93/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1160,negated_conjecture,
% 3.93/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_27]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1619,plain,
% 3.93/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1160]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4,plain,
% 3.93/1.00      ( v5_relat_1(X0,X1)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.93/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_13,plain,
% 3.93/1.00      ( ~ v2_funct_2(X0,X1)
% 3.93/1.00      | ~ v5_relat_1(X0,X1)
% 3.93/1.00      | ~ v1_relat_1(X0)
% 3.93/1.00      | k2_relat_1(X0) = X1 ),
% 3.93/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_364,plain,
% 3.93/1.00      ( ~ v2_funct_2(X0,X1)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.93/1.00      | ~ v1_relat_1(X0)
% 3.93/1.00      | k2_relat_1(X0) = X1 ),
% 3.93/1.00      inference(resolution,[status(thm)],[c_4,c_13]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3,plain,
% 3.93/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.00      | v1_relat_1(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_376,plain,
% 3.93/1.00      ( ~ v2_funct_2(X0,X1)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.93/1.00      | k2_relat_1(X0) = X1 ),
% 3.93/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_364,c_3]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1156,plain,
% 3.93/1.00      ( ~ v2_funct_2(X0_50,X1_50)
% 3.93/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
% 3.93/1.00      | k2_relat_1(X0_50) = X1_50 ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_376]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1623,plain,
% 3.93/1.00      ( k2_relat_1(X0_50) = X1_50
% 3.93/1.00      | v2_funct_2(X0_50,X1_50) != iProver_top
% 3.93/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4717,plain,
% 3.93/1.00      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1619,c_1623]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_30,negated_conjecture,
% 3.93/1.00      ( v1_funct_1(sK1) ),
% 3.93/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_31,plain,
% 3.93/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_34,plain,
% 3.93/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_9,plain,
% 3.93/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.93/1.00      | v2_funct_2(X0,X2)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.00      | ~ v1_funct_1(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_28,negated_conjecture,
% 3.93/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_418,plain,
% 3.93/1.00      ( v2_funct_2(X0,X1)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.93/1.00      | ~ v1_funct_1(X0)
% 3.93/1.00      | sK1 != X0
% 3.93/1.00      | sK0 != X1
% 3.93/1.00      | sK0 != X2 ),
% 3.93/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_28]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_419,plain,
% 3.93/1.00      ( v2_funct_2(sK1,sK0)
% 3.93/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.93/1.00      | ~ v1_funct_1(sK1) ),
% 3.93/1.00      inference(unflattening,[status(thm)],[c_418]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_420,plain,
% 3.93/1.00      ( v2_funct_2(sK1,sK0) = iProver_top
% 3.93/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.93/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4804,plain,
% 3.93/1.00      ( k2_relat_1(sK1) = sK0 ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_4717,c_31,c_34,c_420]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6,plain,
% 3.93/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1172,plain,
% 3.93/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 3.93/1.00      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1607,plain,
% 3.93/1.00      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 3.93/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2476,plain,
% 3.93/1.00      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1619,c_1607]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_20,plain,
% 3.93/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.93/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.93/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.93/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.93/1.00      | ~ v2_funct_1(X2)
% 3.93/1.00      | ~ v1_funct_1(X2)
% 3.93/1.00      | ~ v1_funct_1(X3)
% 3.93/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.93/1.00      | k2_funct_1(X2) = X3
% 3.93/1.00      | k1_xboole_0 = X1
% 3.93/1.00      | k1_xboole_0 = X0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_19,plain,
% 3.93/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.93/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.93/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.93/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.93/1.00      | v2_funct_1(X2)
% 3.93/1.00      | ~ v1_funct_1(X2)
% 3.93/1.00      | ~ v1_funct_1(X3) ),
% 3.93/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_167,plain,
% 3.93/1.00      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.93/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.93/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.93/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.93/1.00      | ~ v1_funct_1(X2)
% 3.93/1.00      | ~ v1_funct_1(X3)
% 3.93/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.93/1.00      | k2_funct_1(X2) = X3
% 3.93/1.00      | k1_xboole_0 = X1
% 3.93/1.00      | k1_xboole_0 = X0 ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_20,c_19]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_168,plain,
% 3.93/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.93/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.93/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.93/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.93/1.00      | ~ v1_funct_1(X2)
% 3.93/1.00      | ~ v1_funct_1(X3)
% 3.93/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.93/1.00      | k2_funct_1(X2) = X3
% 3.93/1.00      | k1_xboole_0 = X0
% 3.93/1.00      | k1_xboole_0 = X1 ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_167]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1157,plain,
% 3.93/1.00      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
% 3.93/1.00      | ~ v1_funct_2(X3_50,X1_50,X0_50)
% 3.93/1.00      | ~ v1_funct_2(X2_50,X0_50,X1_50)
% 3.93/1.00      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 3.93/1.00      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 3.93/1.00      | ~ v1_funct_1(X2_50)
% 3.93/1.00      | ~ v1_funct_1(X3_50)
% 3.93/1.00      | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 3.93/1.00      | k2_funct_1(X2_50) = X3_50
% 3.93/1.00      | k1_xboole_0 = X0_50
% 3.93/1.00      | k1_xboole_0 = X1_50 ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_168]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1622,plain,
% 3.93/1.00      ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 3.93/1.00      | k2_funct_1(X2_50) = X3_50
% 3.93/1.00      | k1_xboole_0 = X0_50
% 3.93/1.00      | k1_xboole_0 = X1_50
% 3.93/1.00      | r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50)) != iProver_top
% 3.93/1.00      | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
% 3.93/1.00      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 3.93/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 3.93/1.00      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 3.93/1.00      | v1_funct_1(X2_50) != iProver_top
% 3.93/1.00      | v1_funct_1(X3_50) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3838,plain,
% 3.93/1.00      ( k2_relat_1(sK1) != sK0
% 3.93/1.00      | k2_funct_1(sK1) = X0_50
% 3.93/1.00      | sK0 = k1_xboole_0
% 3.93/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.93/1.00      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.93/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.93/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.93/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.93/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.93/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2476,c_1622]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_29,negated_conjecture,
% 3.93/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_32,plain,
% 3.93/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4355,plain,
% 3.93/1.00      ( v1_funct_1(X0_50) != iProver_top
% 3.93/1.00      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.93/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.93/1.00      | sK0 = k1_xboole_0
% 3.93/1.00      | k2_funct_1(sK1) = X0_50
% 3.93/1.00      | k2_relat_1(sK1) != sK0
% 3.93/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_3838,c_31,c_32,c_34]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4356,plain,
% 3.93/1.00      ( k2_relat_1(sK1) != sK0
% 3.93/1.00      | k2_funct_1(sK1) = X0_50
% 3.93/1.00      | sK0 = k1_xboole_0
% 3.93/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.93/1.00      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.93/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.93/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_4355]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4806,plain,
% 3.93/1.00      ( k2_funct_1(sK1) = X0_50
% 3.93/1.00      | sK0 != sK0
% 3.93/1.00      | sK0 = k1_xboole_0
% 3.93/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.93/1.00      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.93/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.93/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_4804,c_4356]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4808,plain,
% 3.93/1.00      ( k2_funct_1(sK1) = X0_50
% 3.93/1.00      | sK0 = k1_xboole_0
% 3.93/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.93/1.00      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.93/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.93/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 3.93/1.00      inference(equality_resolution_simp,[status(thm)],[c_4806]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5079,plain,
% 3.93/1.00      ( k2_funct_1(sK1) = sK2
% 3.93/1.00      | sK0 = k1_xboole_0
% 3.93/1.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.93/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.93/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1615,c_4808]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_26,negated_conjecture,
% 3.93/1.00      ( v1_funct_1(sK2) ),
% 3.93/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_25,negated_conjecture,
% 3.93/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_23,negated_conjecture,
% 3.93/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.93/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5080,plain,
% 3.93/1.00      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.93/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.93/1.00      | ~ v1_funct_1(sK2)
% 3.93/1.00      | k2_funct_1(sK1) = sK2
% 3.93/1.00      | sK0 = k1_xboole_0 ),
% 3.93/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5079]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5092,plain,
% 3.93/1.00      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_5079,c_35,c_36,c_38]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5093,plain,
% 3.93/1.00      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_5092]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_21,negated_conjecture,
% 3.93/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1165,negated_conjecture,
% 3.93/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1614,plain,
% 3.93/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_17,plain,
% 3.93/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.93/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.93/1.00      | ~ v1_funct_1(X0)
% 3.93/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_437,plain,
% 3.93/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.93/1.00      | ~ v1_funct_1(X0)
% 3.93/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.93/1.00      | sK1 != X0
% 3.93/1.00      | sK0 != X1 ),
% 3.93/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_438,plain,
% 3.93/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.93/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.93/1.00      | ~ v1_funct_1(sK1)
% 3.93/1.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.93/1.00      inference(unflattening,[status(thm)],[c_437]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_440,plain,
% 3.93/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_438,c_30,c_29,c_27]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1151,plain,
% 3.93/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_440]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1627,plain,
% 3.93/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_1614,c_1151]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5094,plain,
% 3.93/1.00      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_5093,c_1627]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_38,plain,
% 3.93/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_7,plain,
% 3.93/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.93/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1171,plain,
% 3.93/1.00      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
% 3.93/1.00      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1685,plain,
% 3.93/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.93/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_1171]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1686,plain,
% 3.93/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.93/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1685]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5097,plain,
% 3.93/1.00      ( sK0 = k1_xboole_0 ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_5094,c_38,c_1686]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5,plain,
% 3.93/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.00      | ~ v1_xboole_0(X1)
% 3.93/1.00      | v1_xboole_0(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1173,plain,
% 3.93/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 3.93/1.00      | ~ v1_xboole_0(X1_50)
% 3.93/1.00      | v1_xboole_0(X0_50) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1606,plain,
% 3.93/1.00      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 3.93/1.00      | v1_xboole_0(X1_50) != iProver_top
% 3.93/1.00      | v1_xboole_0(X0_50) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2625,plain,
% 3.93/1.00      ( v1_xboole_0(sK1) = iProver_top
% 3.93/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1619,c_1606]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5113,plain,
% 3.93/1.00      ( v1_xboole_0(sK1) = iProver_top
% 3.93/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_5097,c_2625]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_0,plain,
% 3.93/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_95,plain,
% 3.93/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1182,plain,
% 3.93/1.00      ( ~ v1_xboole_0(X0_50) | v1_xboole_0(X1_50) | X1_50 != X0_50 ),
% 3.93/1.00      theory(equality) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2421,plain,
% 3.93/1.00      ( v1_xboole_0(X0_50)
% 3.93/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.93/1.00      | X0_50 != k1_xboole_0 ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_1182]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2422,plain,
% 3.93/1.00      ( X0_50 != k1_xboole_0
% 3.93/1.00      | v1_xboole_0(X0_50) = iProver_top
% 3.93/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_2421]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2424,plain,
% 3.93/1.00      ( sK0 != k1_xboole_0
% 3.93/1.00      | v1_xboole_0(sK0) = iProver_top
% 3.93/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_2422]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6286,plain,
% 3.93/1.00      ( v1_xboole_0(sK1) = iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_5113,c_38,c_95,c_1686,c_2424,c_2625,c_5094]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1176,plain,
% 3.93/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1604,plain,
% 3.93/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1176]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1,plain,
% 3.93/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1175,plain,
% 3.93/1.00      ( ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(X1_50) | X1_50 = X0_50 ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1605,plain,
% 3.93/1.00      ( X0_50 = X1_50
% 3.93/1.00      | v1_xboole_0(X0_50) != iProver_top
% 3.93/1.00      | v1_xboole_0(X1_50) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2346,plain,
% 3.93/1.00      ( k1_xboole_0 = X0_50 | v1_xboole_0(X0_50) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1604,c_1605]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6299,plain,
% 3.93/1.00      ( sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_6286,c_2346]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5117,plain,
% 3.93/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_5097,c_1627]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_7346,plain,
% 3.93/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_6299,c_5117]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_16,plain,
% 3.93/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.93/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1167,plain,
% 3.93/1.00      ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1612,plain,
% 3.93/1.00      ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2626,plain,
% 3.93/1.00      ( v1_xboole_0(X0_50) != iProver_top
% 3.93/1.00      | v1_xboole_0(k6_partfun1(X0_50)) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1612,c_1606]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3366,plain,
% 3.93/1.00      ( k6_partfun1(X0_50) = k1_xboole_0
% 3.93/1.00      | v1_xboole_0(X0_50) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2626,c_2346]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3540,plain,
% 3.93/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1604,c_3366]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2,plain,
% 3.93/1.00      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1174,plain,
% 3.93/1.00      ( k2_funct_1(k6_partfun1(X0_50)) = k6_partfun1(X0_50) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3679,plain,
% 3.93/1.00      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3540,c_1174]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3680,plain,
% 3.93/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_3679,c_3540]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1163,negated_conjecture,
% 3.93/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.93/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1616,plain,
% 3.93/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1163]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2624,plain,
% 3.93/1.00      ( v1_xboole_0(sK2) = iProver_top
% 3.93/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1616,c_1606]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5114,plain,
% 3.93/1.00      ( v1_xboole_0(sK2) = iProver_top
% 3.93/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_5097,c_2624]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6374,plain,
% 3.93/1.00      ( v1_xboole_0(sK2) = iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_5114,c_38,c_95,c_1686,c_2424,c_2624,c_5094]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6387,plain,
% 3.93/1.00      ( sK2 = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_6374,c_2346]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_7355,plain,
% 3.93/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_7346,c_3680,c_6387]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1608,plain,
% 3.93/1.00      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
% 3.93/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2635,plain,
% 3.93/1.00      ( r2_relset_1(X0_50,X0_50,k6_partfun1(X0_50),k6_partfun1(X0_50)) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1612,c_1608]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3674,plain,
% 3.93/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3540,c_2635]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(contradiction,plain,
% 3.93/1.00      ( $false ),
% 3.93/1.00      inference(minisat,[status(thm)],[c_7355,c_3674]) ).
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  ------                               Statistics
% 3.93/1.00  
% 3.93/1.00  ------ General
% 3.93/1.00  
% 3.93/1.00  abstr_ref_over_cycles:                  0
% 3.93/1.00  abstr_ref_under_cycles:                 0
% 3.93/1.00  gc_basic_clause_elim:                   0
% 3.93/1.00  forced_gc_time:                         0
% 3.93/1.00  parsing_time:                           0.01
% 3.93/1.00  unif_index_cands_time:                  0.
% 3.93/1.00  unif_index_add_time:                    0.
% 3.93/1.00  orderings_time:                         0.
% 3.93/1.00  out_proof_time:                         0.016
% 3.93/1.00  total_time:                             0.437
% 3.93/1.00  num_of_symbols:                         56
% 3.93/1.00  num_of_terms:                           9332
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing
% 3.93/1.00  
% 3.93/1.00  num_of_splits:                          0
% 3.93/1.00  num_of_split_atoms:                     0
% 3.93/1.00  num_of_reused_defs:                     0
% 3.93/1.00  num_eq_ax_congr_red:                    16
% 3.93/1.00  num_of_sem_filtered_clauses:            3
% 3.93/1.00  num_of_subtypes:                        3
% 3.93/1.00  monotx_restored_types:                  1
% 3.93/1.00  sat_num_of_epr_types:                   0
% 3.93/1.00  sat_num_of_non_cyclic_types:            0
% 3.93/1.00  sat_guarded_non_collapsed_types:        1
% 3.93/1.00  num_pure_diseq_elim:                    0
% 3.93/1.00  simp_replaced_by:                       0
% 3.93/1.00  res_preprocessed:                       141
% 3.93/1.00  prep_upred:                             0
% 3.93/1.00  prep_unflattend:                        66
% 3.93/1.00  smt_new_axioms:                         0
% 3.93/1.00  pred_elim_cands:                        6
% 3.93/1.00  pred_elim:                              3
% 3.93/1.00  pred_elim_cl:                           2
% 3.93/1.00  pred_elim_cycles:                       8
% 3.93/1.00  merged_defs:                            0
% 3.93/1.00  merged_defs_ncl:                        0
% 3.93/1.00  bin_hyper_res:                          0
% 3.93/1.00  prep_cycles:                            4
% 3.93/1.00  pred_elim_time:                         0.029
% 3.93/1.00  splitting_time:                         0.
% 3.93/1.00  sem_filter_time:                        0.
% 3.93/1.00  monotx_time:                            0.001
% 3.93/1.00  subtype_inf_time:                       0.001
% 3.93/1.00  
% 3.93/1.00  ------ Problem properties
% 3.93/1.00  
% 3.93/1.00  clauses:                                26
% 3.93/1.00  conjectures:                            8
% 3.93/1.00  epr:                                    8
% 3.93/1.00  horn:                                   25
% 3.93/1.00  ground:                                 13
% 3.93/1.00  unary:                                  15
% 3.93/1.00  binary:                                 3
% 3.93/1.00  lits:                                   63
% 3.93/1.00  lits_eq:                                11
% 3.93/1.00  fd_pure:                                0
% 3.93/1.00  fd_pseudo:                              0
% 3.93/1.00  fd_cond:                                0
% 3.93/1.00  fd_pseudo_cond:                         4
% 3.93/1.00  ac_symbols:                             0
% 3.93/1.00  
% 3.93/1.00  ------ Propositional Solver
% 3.93/1.00  
% 3.93/1.00  prop_solver_calls:                      30
% 3.93/1.00  prop_fast_solver_calls:                 1367
% 3.93/1.00  smt_solver_calls:                       0
% 3.93/1.00  smt_fast_solver_calls:                  0
% 3.93/1.00  prop_num_of_clauses:                    3098
% 3.93/1.00  prop_preprocess_simplified:             7733
% 3.93/1.00  prop_fo_subsumed:                       44
% 3.93/1.00  prop_solver_time:                       0.
% 3.93/1.00  smt_solver_time:                        0.
% 3.93/1.00  smt_fast_solver_time:                   0.
% 3.93/1.00  prop_fast_solver_time:                  0.
% 3.93/1.00  prop_unsat_core_time:                   0.
% 3.93/1.00  
% 3.93/1.00  ------ QBF
% 3.93/1.00  
% 3.93/1.00  qbf_q_res:                              0
% 3.93/1.00  qbf_num_tautologies:                    0
% 3.93/1.00  qbf_prep_cycles:                        0
% 3.93/1.00  
% 3.93/1.00  ------ BMC1
% 3.93/1.00  
% 3.93/1.00  bmc1_current_bound:                     -1
% 3.93/1.00  bmc1_last_solved_bound:                 -1
% 3.93/1.00  bmc1_unsat_core_size:                   -1
% 3.93/1.00  bmc1_unsat_core_parents_size:           -1
% 3.93/1.00  bmc1_merge_next_fun:                    0
% 3.93/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.93/1.00  
% 3.93/1.00  ------ Instantiation
% 3.93/1.00  
% 3.93/1.00  inst_num_of_clauses:                    900
% 3.93/1.00  inst_num_in_passive:                    489
% 3.93/1.00  inst_num_in_active:                     400
% 3.93/1.00  inst_num_in_unprocessed:                11
% 3.93/1.00  inst_num_of_loops:                      550
% 3.93/1.00  inst_num_of_learning_restarts:          0
% 3.93/1.00  inst_num_moves_active_passive:          144
% 3.93/1.00  inst_lit_activity:                      0
% 3.93/1.00  inst_lit_activity_moves:                0
% 3.93/1.00  inst_num_tautologies:                   0
% 3.93/1.00  inst_num_prop_implied:                  0
% 3.93/1.00  inst_num_existing_simplified:           0
% 3.93/1.00  inst_num_eq_res_simplified:             0
% 3.93/1.00  inst_num_child_elim:                    0
% 3.93/1.00  inst_num_of_dismatching_blockings:      532
% 3.93/1.00  inst_num_of_non_proper_insts:           1479
% 3.93/1.00  inst_num_of_duplicates:                 0
% 3.93/1.00  inst_inst_num_from_inst_to_res:         0
% 3.93/1.00  inst_dismatching_checking_time:         0.
% 3.93/1.00  
% 3.93/1.00  ------ Resolution
% 3.93/1.00  
% 3.93/1.00  res_num_of_clauses:                     0
% 3.93/1.00  res_num_in_passive:                     0
% 3.93/1.00  res_num_in_active:                      0
% 3.93/1.00  res_num_of_loops:                       145
% 3.93/1.00  res_forward_subset_subsumed:            44
% 3.93/1.00  res_backward_subset_subsumed:           0
% 3.93/1.00  res_forward_subsumed:                   0
% 3.93/1.00  res_backward_subsumed:                  0
% 3.93/1.00  res_forward_subsumption_resolution:     4
% 3.93/1.00  res_backward_subsumption_resolution:    0
% 3.93/1.00  res_clause_to_clause_subsumption:       506
% 3.93/1.00  res_orphan_elimination:                 0
% 3.93/1.00  res_tautology_del:                      100
% 3.93/1.00  res_num_eq_res_simplified:              0
% 3.93/1.00  res_num_sel_changes:                    0
% 3.93/1.00  res_moves_from_active_to_pass:          0
% 3.93/1.00  
% 3.93/1.00  ------ Superposition
% 3.93/1.00  
% 3.93/1.00  sup_time_total:                         0.
% 3.93/1.00  sup_time_generating:                    0.
% 3.93/1.00  sup_time_sim_full:                      0.
% 3.93/1.00  sup_time_sim_immed:                     0.
% 3.93/1.00  
% 3.93/1.00  sup_num_of_clauses:                     112
% 3.93/1.00  sup_num_in_active:                      64
% 3.93/1.00  sup_num_in_passive:                     48
% 3.93/1.00  sup_num_of_loops:                       108
% 3.93/1.00  sup_fw_superposition:                   107
% 3.93/1.00  sup_bw_superposition:                   68
% 3.93/1.00  sup_immediate_simplified:               64
% 3.93/1.00  sup_given_eliminated:                   2
% 3.93/1.00  comparisons_done:                       0
% 3.93/1.00  comparisons_avoided:                    3
% 3.93/1.00  
% 3.93/1.00  ------ Simplifications
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  sim_fw_subset_subsumed:                 8
% 3.93/1.00  sim_bw_subset_subsumed:                 10
% 3.93/1.00  sim_fw_subsumed:                        2
% 3.93/1.00  sim_bw_subsumed:                        1
% 3.93/1.00  sim_fw_subsumption_res:                 0
% 3.93/1.00  sim_bw_subsumption_res:                 0
% 3.93/1.00  sim_tautology_del:                      2
% 3.93/1.00  sim_eq_tautology_del:                   33
% 3.93/1.00  sim_eq_res_simp:                        2
% 3.93/1.00  sim_fw_demodulated:                     7
% 3.93/1.00  sim_bw_demodulated:                     42
% 3.93/1.00  sim_light_normalised:                   64
% 3.93/1.00  sim_joinable_taut:                      0
% 3.93/1.00  sim_joinable_simp:                      0
% 3.93/1.00  sim_ac_normalised:                      0
% 3.93/1.00  sim_smt_subsumption:                    0
% 3.93/1.00  
%------------------------------------------------------------------------------
