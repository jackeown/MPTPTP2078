%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:13 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_38)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f80,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f71,plain,(
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

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f69,plain,(
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

fof(f73,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f61,f68])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1992,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1988,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_358,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_370,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_358,c_9])).

cnf(c_1984,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_4409,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1988,c_1984])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_504,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_505,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_507,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_33,c_30])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_370,c_507])).

cnf(c_585,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_587,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_5190,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4409,c_30,c_587])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1999,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4426,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1988,c_1999])).

cnf(c_5193,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_5190,c_4426])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f71])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_185,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_22])).

cnf(c_186,plain,
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
    inference(renaming,[status(thm)],[c_185])).

cnf(c_1985,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_5244,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5193,c_1985])).

cnf(c_34,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8061,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5244,c_34,c_35,c_37])).

cnf(c_8062,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8061])).

cnf(c_8073,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1992,c_8062])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_8074,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8073])).

cnf(c_8212,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8073,c_38,c_39,c_41])).

cnf(c_8213,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8212])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1993,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_523,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_524,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_526,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_33,c_32,c_30])).

cnf(c_2038,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1993,c_526])).

cnf(c_8222,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8213,c_2038])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2321,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2322,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2321])).

cnf(c_8247,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8222,c_41,c_2322])).

cnf(c_1986,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2001,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5425,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_2001])).

cnf(c_5429,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = sK0
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5425,c_5190])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_494,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_495,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_2276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2277,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2276])).

cnf(c_5950,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5429,c_34,c_37,c_495,c_2277])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2006,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5953,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5950,c_2006])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2263,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2264,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2263])).

cnf(c_7444,plain,
    ( sK0 != k1_xboole_0
    | k2_funct_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5953,c_34,c_37,c_495,c_2264,c_2277])).

cnf(c_7445,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7444])).

cnf(c_8255,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8247,c_7445])).

cnf(c_8370,plain,
    ( k2_funct_1(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8255])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2007,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5194,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5190,c_2007])).

cnf(c_5226,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5194,c_37,c_2277])).

cnf(c_5227,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5226])).

cnf(c_8264,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8247,c_5227])).

cnf(c_8335,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8264])).

cnf(c_8371,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8370,c_8335])).

cnf(c_1991,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4408,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_1984])).

cnf(c_27,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_482,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_483,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_485,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_29,c_26])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_370,c_485])).

cnf(c_575,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_577,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_5121,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4408,c_26,c_577])).

cnf(c_5125,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5121,c_2007])).

cnf(c_2273,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5136,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5125])).

cnf(c_5221,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5125,c_26,c_2273,c_5136])).

cnf(c_5222,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5221])).

cnf(c_8265,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8247,c_5222])).

cnf(c_8315,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8265])).

cnf(c_8272,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8247,c_2038])).

cnf(c_8320,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8315,c_8272])).

cnf(c_8337,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8335,c_8320])).

cnf(c_8374,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8371,c_8337])).

cnf(c_3,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3413,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2006])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_69,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2268,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_relat_1(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2269,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2268])).

cnf(c_3534,plain,
    ( k1_xboole_0 != X0
    | k6_partfun1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3413,c_69,c_2269])).

cnf(c_3535,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3534])).

cnf(c_3539,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3535])).

cnf(c_1996,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3837,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3539,c_1996])).

cnf(c_1998,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3994,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3837,c_1998])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8374,c_3994])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:39:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.33/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/1.00  
% 3.33/1.00  ------  iProver source info
% 3.33/1.00  
% 3.33/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.33/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/1.00  git: non_committed_changes: false
% 3.33/1.00  git: last_make_outside_of_git: false
% 3.33/1.00  
% 3.33/1.00  ------ 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options
% 3.33/1.00  
% 3.33/1.00  --out_options                           all
% 3.33/1.00  --tptp_safe_out                         true
% 3.33/1.00  --problem_path                          ""
% 3.33/1.00  --include_path                          ""
% 3.33/1.00  --clausifier                            res/vclausify_rel
% 3.33/1.00  --clausifier_options                    --mode clausify
% 3.33/1.00  --stdin                                 false
% 3.33/1.00  --stats_out                             all
% 3.33/1.00  
% 3.33/1.00  ------ General Options
% 3.33/1.00  
% 3.33/1.00  --fof                                   false
% 3.33/1.00  --time_out_real                         305.
% 3.33/1.00  --time_out_virtual                      -1.
% 3.33/1.00  --symbol_type_check                     false
% 3.33/1.00  --clausify_out                          false
% 3.33/1.00  --sig_cnt_out                           false
% 3.33/1.00  --trig_cnt_out                          false
% 3.33/1.00  --trig_cnt_out_tolerance                1.
% 3.33/1.00  --trig_cnt_out_sk_spl                   false
% 3.33/1.00  --abstr_cl_out                          false
% 3.33/1.00  
% 3.33/1.00  ------ Global Options
% 3.33/1.00  
% 3.33/1.00  --schedule                              default
% 3.33/1.00  --add_important_lit                     false
% 3.33/1.00  --prop_solver_per_cl                    1000
% 3.33/1.00  --min_unsat_core                        false
% 3.33/1.00  --soft_assumptions                      false
% 3.33/1.00  --soft_lemma_size                       3
% 3.33/1.00  --prop_impl_unit_size                   0
% 3.33/1.00  --prop_impl_unit                        []
% 3.33/1.00  --share_sel_clauses                     true
% 3.33/1.00  --reset_solvers                         false
% 3.33/1.00  --bc_imp_inh                            [conj_cone]
% 3.33/1.00  --conj_cone_tolerance                   3.
% 3.33/1.00  --extra_neg_conj                        none
% 3.33/1.00  --large_theory_mode                     true
% 3.33/1.00  --prolific_symb_bound                   200
% 3.33/1.00  --lt_threshold                          2000
% 3.33/1.00  --clause_weak_htbl                      true
% 3.33/1.00  --gc_record_bc_elim                     false
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing Options
% 3.33/1.00  
% 3.33/1.00  --preprocessing_flag                    true
% 3.33/1.00  --time_out_prep_mult                    0.1
% 3.33/1.00  --splitting_mode                        input
% 3.33/1.00  --splitting_grd                         true
% 3.33/1.00  --splitting_cvd                         false
% 3.33/1.00  --splitting_cvd_svl                     false
% 3.33/1.00  --splitting_nvd                         32
% 3.33/1.00  --sub_typing                            true
% 3.33/1.00  --prep_gs_sim                           true
% 3.33/1.00  --prep_unflatten                        true
% 3.33/1.00  --prep_res_sim                          true
% 3.33/1.00  --prep_upred                            true
% 3.33/1.00  --prep_sem_filter                       exhaustive
% 3.33/1.00  --prep_sem_filter_out                   false
% 3.33/1.00  --pred_elim                             true
% 3.33/1.00  --res_sim_input                         true
% 3.33/1.00  --eq_ax_congr_red                       true
% 3.33/1.00  --pure_diseq_elim                       true
% 3.33/1.00  --brand_transform                       false
% 3.33/1.00  --non_eq_to_eq                          false
% 3.33/1.00  --prep_def_merge                        true
% 3.33/1.00  --prep_def_merge_prop_impl              false
% 3.33/1.00  --prep_def_merge_mbd                    true
% 3.33/1.00  --prep_def_merge_tr_red                 false
% 3.33/1.00  --prep_def_merge_tr_cl                  false
% 3.33/1.00  --smt_preprocessing                     true
% 3.33/1.00  --smt_ac_axioms                         fast
% 3.33/1.00  --preprocessed_out                      false
% 3.33/1.00  --preprocessed_stats                    false
% 3.33/1.00  
% 3.33/1.00  ------ Abstraction refinement Options
% 3.33/1.00  
% 3.33/1.00  --abstr_ref                             []
% 3.33/1.00  --abstr_ref_prep                        false
% 3.33/1.00  --abstr_ref_until_sat                   false
% 3.33/1.00  --abstr_ref_sig_restrict                funpre
% 3.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.00  --abstr_ref_under                       []
% 3.33/1.00  
% 3.33/1.00  ------ SAT Options
% 3.33/1.00  
% 3.33/1.00  --sat_mode                              false
% 3.33/1.00  --sat_fm_restart_options                ""
% 3.33/1.00  --sat_gr_def                            false
% 3.33/1.00  --sat_epr_types                         true
% 3.33/1.00  --sat_non_cyclic_types                  false
% 3.33/1.00  --sat_finite_models                     false
% 3.33/1.00  --sat_fm_lemmas                         false
% 3.33/1.00  --sat_fm_prep                           false
% 3.33/1.00  --sat_fm_uc_incr                        true
% 3.33/1.00  --sat_out_model                         small
% 3.33/1.00  --sat_out_clauses                       false
% 3.33/1.00  
% 3.33/1.00  ------ QBF Options
% 3.33/1.00  
% 3.33/1.00  --qbf_mode                              false
% 3.33/1.00  --qbf_elim_univ                         false
% 3.33/1.00  --qbf_dom_inst                          none
% 3.33/1.00  --qbf_dom_pre_inst                      false
% 3.33/1.00  --qbf_sk_in                             false
% 3.33/1.00  --qbf_pred_elim                         true
% 3.33/1.00  --qbf_split                             512
% 3.33/1.00  
% 3.33/1.00  ------ BMC1 Options
% 3.33/1.00  
% 3.33/1.00  --bmc1_incremental                      false
% 3.33/1.00  --bmc1_axioms                           reachable_all
% 3.33/1.00  --bmc1_min_bound                        0
% 3.33/1.00  --bmc1_max_bound                        -1
% 3.33/1.00  --bmc1_max_bound_default                -1
% 3.33/1.00  --bmc1_symbol_reachability              true
% 3.33/1.00  --bmc1_property_lemmas                  false
% 3.33/1.00  --bmc1_k_induction                      false
% 3.33/1.00  --bmc1_non_equiv_states                 false
% 3.33/1.00  --bmc1_deadlock                         false
% 3.33/1.00  --bmc1_ucm                              false
% 3.33/1.00  --bmc1_add_unsat_core                   none
% 3.33/1.00  --bmc1_unsat_core_children              false
% 3.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.00  --bmc1_out_stat                         full
% 3.33/1.00  --bmc1_ground_init                      false
% 3.33/1.00  --bmc1_pre_inst_next_state              false
% 3.33/1.00  --bmc1_pre_inst_state                   false
% 3.33/1.00  --bmc1_pre_inst_reach_state             false
% 3.33/1.00  --bmc1_out_unsat_core                   false
% 3.33/1.00  --bmc1_aig_witness_out                  false
% 3.33/1.00  --bmc1_verbose                          false
% 3.33/1.00  --bmc1_dump_clauses_tptp                false
% 3.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.00  --bmc1_dump_file                        -
% 3.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.00  --bmc1_ucm_extend_mode                  1
% 3.33/1.00  --bmc1_ucm_init_mode                    2
% 3.33/1.00  --bmc1_ucm_cone_mode                    none
% 3.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.00  --bmc1_ucm_relax_model                  4
% 3.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.00  --bmc1_ucm_layered_model                none
% 3.33/1.00  --bmc1_ucm_max_lemma_size               10
% 3.33/1.00  
% 3.33/1.00  ------ AIG Options
% 3.33/1.00  
% 3.33/1.00  --aig_mode                              false
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation Options
% 3.33/1.00  
% 3.33/1.00  --instantiation_flag                    true
% 3.33/1.00  --inst_sos_flag                         false
% 3.33/1.00  --inst_sos_phase                        true
% 3.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel_side                     num_symb
% 3.33/1.00  --inst_solver_per_active                1400
% 3.33/1.00  --inst_solver_calls_frac                1.
% 3.33/1.00  --inst_passive_queue_type               priority_queues
% 3.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.00  --inst_passive_queues_freq              [25;2]
% 3.33/1.00  --inst_dismatching                      true
% 3.33/1.00  --inst_eager_unprocessed_to_passive     true
% 3.33/1.00  --inst_prop_sim_given                   true
% 3.33/1.00  --inst_prop_sim_new                     false
% 3.33/1.00  --inst_subs_new                         false
% 3.33/1.00  --inst_eq_res_simp                      false
% 3.33/1.00  --inst_subs_given                       false
% 3.33/1.00  --inst_orphan_elimination               true
% 3.33/1.00  --inst_learning_loop_flag               true
% 3.33/1.00  --inst_learning_start                   3000
% 3.33/1.00  --inst_learning_factor                  2
% 3.33/1.00  --inst_start_prop_sim_after_learn       3
% 3.33/1.00  --inst_sel_renew                        solver
% 3.33/1.00  --inst_lit_activity_flag                true
% 3.33/1.00  --inst_restr_to_given                   false
% 3.33/1.00  --inst_activity_threshold               500
% 3.33/1.00  --inst_out_proof                        true
% 3.33/1.00  
% 3.33/1.00  ------ Resolution Options
% 3.33/1.00  
% 3.33/1.00  --resolution_flag                       true
% 3.33/1.00  --res_lit_sel                           adaptive
% 3.33/1.00  --res_lit_sel_side                      none
% 3.33/1.00  --res_ordering                          kbo
% 3.33/1.00  --res_to_prop_solver                    active
% 3.33/1.00  --res_prop_simpl_new                    false
% 3.33/1.00  --res_prop_simpl_given                  true
% 3.33/1.00  --res_passive_queue_type                priority_queues
% 3.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.00  --res_passive_queues_freq               [15;5]
% 3.33/1.00  --res_forward_subs                      full
% 3.33/1.00  --res_backward_subs                     full
% 3.33/1.00  --res_forward_subs_resolution           true
% 3.33/1.00  --res_backward_subs_resolution          true
% 3.33/1.00  --res_orphan_elimination                true
% 3.33/1.00  --res_time_limit                        2.
% 3.33/1.00  --res_out_proof                         true
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Options
% 3.33/1.00  
% 3.33/1.00  --superposition_flag                    true
% 3.33/1.00  --sup_passive_queue_type                priority_queues
% 3.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.00  --demod_completeness_check              fast
% 3.33/1.00  --demod_use_ground                      true
% 3.33/1.00  --sup_to_prop_solver                    passive
% 3.33/1.00  --sup_prop_simpl_new                    true
% 3.33/1.00  --sup_prop_simpl_given                  true
% 3.33/1.00  --sup_fun_splitting                     false
% 3.33/1.00  --sup_smt_interval                      50000
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Simplification Setup
% 3.33/1.00  
% 3.33/1.00  --sup_indices_passive                   []
% 3.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_full_bw                           [BwDemod]
% 3.33/1.00  --sup_immed_triv                        [TrivRules]
% 3.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_immed_bw_main                     []
% 3.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  
% 3.33/1.00  ------ Combination Options
% 3.33/1.00  
% 3.33/1.00  --comb_res_mult                         3
% 3.33/1.00  --comb_sup_mult                         2
% 3.33/1.00  --comb_inst_mult                        10
% 3.33/1.00  
% 3.33/1.00  ------ Debug Options
% 3.33/1.00  
% 3.33/1.00  --dbg_backtrace                         false
% 3.33/1.00  --dbg_dump_prop_clauses                 false
% 3.33/1.00  --dbg_dump_prop_clauses_file            -
% 3.33/1.00  --dbg_out_stat                          false
% 3.33/1.00  ------ Parsing...
% 3.33/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/1.00  ------ Proving...
% 3.33/1.00  ------ Problem Properties 
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  clauses                                 33
% 3.33/1.00  conjectures                             8
% 3.33/1.00  EPR                                     8
% 3.33/1.00  Horn                                    32
% 3.33/1.00  unary                                   17
% 3.33/1.00  binary                                  4
% 3.33/1.00  lits                                    85
% 3.33/1.00  lits eq                                 17
% 3.33/1.00  fd_pure                                 0
% 3.33/1.00  fd_pseudo                               0
% 3.33/1.00  fd_cond                                 2
% 3.33/1.00  fd_pseudo_cond                          3
% 3.33/1.00  AC symbols                              0
% 3.33/1.00  
% 3.33/1.00  ------ Schedule dynamic 5 is on 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ 
% 3.33/1.00  Current options:
% 3.33/1.00  ------ 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options
% 3.33/1.00  
% 3.33/1.00  --out_options                           all
% 3.33/1.00  --tptp_safe_out                         true
% 3.33/1.00  --problem_path                          ""
% 3.33/1.00  --include_path                          ""
% 3.33/1.00  --clausifier                            res/vclausify_rel
% 3.33/1.00  --clausifier_options                    --mode clausify
% 3.33/1.00  --stdin                                 false
% 3.33/1.00  --stats_out                             all
% 3.33/1.00  
% 3.33/1.00  ------ General Options
% 3.33/1.00  
% 3.33/1.00  --fof                                   false
% 3.33/1.00  --time_out_real                         305.
% 3.33/1.00  --time_out_virtual                      -1.
% 3.33/1.00  --symbol_type_check                     false
% 3.33/1.00  --clausify_out                          false
% 3.33/1.00  --sig_cnt_out                           false
% 3.33/1.00  --trig_cnt_out                          false
% 3.33/1.00  --trig_cnt_out_tolerance                1.
% 3.33/1.00  --trig_cnt_out_sk_spl                   false
% 3.33/1.00  --abstr_cl_out                          false
% 3.33/1.00  
% 3.33/1.00  ------ Global Options
% 3.33/1.00  
% 3.33/1.00  --schedule                              default
% 3.33/1.00  --add_important_lit                     false
% 3.33/1.00  --prop_solver_per_cl                    1000
% 3.33/1.00  --min_unsat_core                        false
% 3.33/1.00  --soft_assumptions                      false
% 3.33/1.00  --soft_lemma_size                       3
% 3.33/1.00  --prop_impl_unit_size                   0
% 3.33/1.00  --prop_impl_unit                        []
% 3.33/1.00  --share_sel_clauses                     true
% 3.33/1.00  --reset_solvers                         false
% 3.33/1.00  --bc_imp_inh                            [conj_cone]
% 3.33/1.00  --conj_cone_tolerance                   3.
% 3.33/1.00  --extra_neg_conj                        none
% 3.33/1.00  --large_theory_mode                     true
% 3.33/1.00  --prolific_symb_bound                   200
% 3.33/1.00  --lt_threshold                          2000
% 3.33/1.00  --clause_weak_htbl                      true
% 3.33/1.00  --gc_record_bc_elim                     false
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing Options
% 3.33/1.00  
% 3.33/1.00  --preprocessing_flag                    true
% 3.33/1.00  --time_out_prep_mult                    0.1
% 3.33/1.00  --splitting_mode                        input
% 3.33/1.00  --splitting_grd                         true
% 3.33/1.00  --splitting_cvd                         false
% 3.33/1.00  --splitting_cvd_svl                     false
% 3.33/1.00  --splitting_nvd                         32
% 3.33/1.00  --sub_typing                            true
% 3.33/1.00  --prep_gs_sim                           true
% 3.33/1.00  --prep_unflatten                        true
% 3.33/1.00  --prep_res_sim                          true
% 3.33/1.00  --prep_upred                            true
% 3.33/1.00  --prep_sem_filter                       exhaustive
% 3.33/1.00  --prep_sem_filter_out                   false
% 3.33/1.00  --pred_elim                             true
% 3.33/1.00  --res_sim_input                         true
% 3.33/1.00  --eq_ax_congr_red                       true
% 3.33/1.00  --pure_diseq_elim                       true
% 3.33/1.00  --brand_transform                       false
% 3.33/1.00  --non_eq_to_eq                          false
% 3.33/1.00  --prep_def_merge                        true
% 3.33/1.00  --prep_def_merge_prop_impl              false
% 3.33/1.00  --prep_def_merge_mbd                    true
% 3.33/1.00  --prep_def_merge_tr_red                 false
% 3.33/1.00  --prep_def_merge_tr_cl                  false
% 3.33/1.00  --smt_preprocessing                     true
% 3.33/1.00  --smt_ac_axioms                         fast
% 3.33/1.00  --preprocessed_out                      false
% 3.33/1.00  --preprocessed_stats                    false
% 3.33/1.00  
% 3.33/1.00  ------ Abstraction refinement Options
% 3.33/1.00  
% 3.33/1.00  --abstr_ref                             []
% 3.33/1.00  --abstr_ref_prep                        false
% 3.33/1.00  --abstr_ref_until_sat                   false
% 3.33/1.00  --abstr_ref_sig_restrict                funpre
% 3.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.00  --abstr_ref_under                       []
% 3.33/1.00  
% 3.33/1.00  ------ SAT Options
% 3.33/1.00  
% 3.33/1.00  --sat_mode                              false
% 3.33/1.00  --sat_fm_restart_options                ""
% 3.33/1.00  --sat_gr_def                            false
% 3.33/1.00  --sat_epr_types                         true
% 3.33/1.00  --sat_non_cyclic_types                  false
% 3.33/1.00  --sat_finite_models                     false
% 3.33/1.00  --sat_fm_lemmas                         false
% 3.33/1.00  --sat_fm_prep                           false
% 3.33/1.00  --sat_fm_uc_incr                        true
% 3.33/1.00  --sat_out_model                         small
% 3.33/1.00  --sat_out_clauses                       false
% 3.33/1.00  
% 3.33/1.00  ------ QBF Options
% 3.33/1.00  
% 3.33/1.00  --qbf_mode                              false
% 3.33/1.00  --qbf_elim_univ                         false
% 3.33/1.00  --qbf_dom_inst                          none
% 3.33/1.00  --qbf_dom_pre_inst                      false
% 3.33/1.00  --qbf_sk_in                             false
% 3.33/1.00  --qbf_pred_elim                         true
% 3.33/1.00  --qbf_split                             512
% 3.33/1.00  
% 3.33/1.00  ------ BMC1 Options
% 3.33/1.00  
% 3.33/1.00  --bmc1_incremental                      false
% 3.33/1.00  --bmc1_axioms                           reachable_all
% 3.33/1.00  --bmc1_min_bound                        0
% 3.33/1.00  --bmc1_max_bound                        -1
% 3.33/1.00  --bmc1_max_bound_default                -1
% 3.33/1.00  --bmc1_symbol_reachability              true
% 3.33/1.00  --bmc1_property_lemmas                  false
% 3.33/1.00  --bmc1_k_induction                      false
% 3.33/1.00  --bmc1_non_equiv_states                 false
% 3.33/1.00  --bmc1_deadlock                         false
% 3.33/1.00  --bmc1_ucm                              false
% 3.33/1.00  --bmc1_add_unsat_core                   none
% 3.33/1.00  --bmc1_unsat_core_children              false
% 3.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.00  --bmc1_out_stat                         full
% 3.33/1.00  --bmc1_ground_init                      false
% 3.33/1.00  --bmc1_pre_inst_next_state              false
% 3.33/1.00  --bmc1_pre_inst_state                   false
% 3.33/1.00  --bmc1_pre_inst_reach_state             false
% 3.33/1.00  --bmc1_out_unsat_core                   false
% 3.33/1.00  --bmc1_aig_witness_out                  false
% 3.33/1.00  --bmc1_verbose                          false
% 3.33/1.00  --bmc1_dump_clauses_tptp                false
% 3.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.00  --bmc1_dump_file                        -
% 3.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.00  --bmc1_ucm_extend_mode                  1
% 3.33/1.00  --bmc1_ucm_init_mode                    2
% 3.33/1.00  --bmc1_ucm_cone_mode                    none
% 3.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.00  --bmc1_ucm_relax_model                  4
% 3.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.00  --bmc1_ucm_layered_model                none
% 3.33/1.00  --bmc1_ucm_max_lemma_size               10
% 3.33/1.00  
% 3.33/1.00  ------ AIG Options
% 3.33/1.00  
% 3.33/1.00  --aig_mode                              false
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation Options
% 3.33/1.00  
% 3.33/1.00  --instantiation_flag                    true
% 3.33/1.00  --inst_sos_flag                         false
% 3.33/1.00  --inst_sos_phase                        true
% 3.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel_side                     none
% 3.33/1.00  --inst_solver_per_active                1400
% 3.33/1.00  --inst_solver_calls_frac                1.
% 3.33/1.00  --inst_passive_queue_type               priority_queues
% 3.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.00  --inst_passive_queues_freq              [25;2]
% 3.33/1.00  --inst_dismatching                      true
% 3.33/1.00  --inst_eager_unprocessed_to_passive     true
% 3.33/1.00  --inst_prop_sim_given                   true
% 3.33/1.00  --inst_prop_sim_new                     false
% 3.33/1.00  --inst_subs_new                         false
% 3.33/1.00  --inst_eq_res_simp                      false
% 3.33/1.00  --inst_subs_given                       false
% 3.33/1.00  --inst_orphan_elimination               true
% 3.33/1.00  --inst_learning_loop_flag               true
% 3.33/1.00  --inst_learning_start                   3000
% 3.33/1.00  --inst_learning_factor                  2
% 3.33/1.00  --inst_start_prop_sim_after_learn       3
% 3.33/1.00  --inst_sel_renew                        solver
% 3.33/1.00  --inst_lit_activity_flag                true
% 3.33/1.00  --inst_restr_to_given                   false
% 3.33/1.00  --inst_activity_threshold               500
% 3.33/1.00  --inst_out_proof                        true
% 3.33/1.00  
% 3.33/1.00  ------ Resolution Options
% 3.33/1.00  
% 3.33/1.00  --resolution_flag                       false
% 3.33/1.00  --res_lit_sel                           adaptive
% 3.33/1.00  --res_lit_sel_side                      none
% 3.33/1.00  --res_ordering                          kbo
% 3.33/1.00  --res_to_prop_solver                    active
% 3.33/1.00  --res_prop_simpl_new                    false
% 3.33/1.00  --res_prop_simpl_given                  true
% 3.33/1.00  --res_passive_queue_type                priority_queues
% 3.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.00  --res_passive_queues_freq               [15;5]
% 3.33/1.00  --res_forward_subs                      full
% 3.33/1.00  --res_backward_subs                     full
% 3.33/1.00  --res_forward_subs_resolution           true
% 3.33/1.00  --res_backward_subs_resolution          true
% 3.33/1.00  --res_orphan_elimination                true
% 3.33/1.00  --res_time_limit                        2.
% 3.33/1.00  --res_out_proof                         true
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Options
% 3.33/1.00  
% 3.33/1.00  --superposition_flag                    true
% 3.33/1.00  --sup_passive_queue_type                priority_queues
% 3.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.00  --demod_completeness_check              fast
% 3.33/1.00  --demod_use_ground                      true
% 3.33/1.00  --sup_to_prop_solver                    passive
% 3.33/1.00  --sup_prop_simpl_new                    true
% 3.33/1.00  --sup_prop_simpl_given                  true
% 3.33/1.00  --sup_fun_splitting                     false
% 3.33/1.00  --sup_smt_interval                      50000
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Simplification Setup
% 3.33/1.00  
% 3.33/1.00  --sup_indices_passive                   []
% 3.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_full_bw                           [BwDemod]
% 3.33/1.00  --sup_immed_triv                        [TrivRules]
% 3.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_immed_bw_main                     []
% 3.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  
% 3.33/1.00  ------ Combination Options
% 3.33/1.00  
% 3.33/1.00  --comb_res_mult                         3
% 3.33/1.00  --comb_sup_mult                         2
% 3.33/1.00  --comb_inst_mult                        10
% 3.33/1.00  
% 3.33/1.00  ------ Debug Options
% 3.33/1.00  
% 3.33/1.00  --dbg_backtrace                         false
% 3.33/1.00  --dbg_dump_prop_clauses                 false
% 3.33/1.00  --dbg_dump_prop_clauses_file            -
% 3.33/1.00  --dbg_out_stat                          false
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ Proving...
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS status Theorem for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  fof(f16,conjecture,(
% 3.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f17,negated_conjecture,(
% 3.33/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.33/1.00    inference(negated_conjecture,[],[f16])).
% 3.33/1.00  
% 3.33/1.00  fof(f40,plain,(
% 3.33/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.33/1.00    inference(ennf_transformation,[],[f17])).
% 3.33/1.00  
% 3.33/1.00  fof(f41,plain,(
% 3.33/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.33/1.00    inference(flattening,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f45,plain,(
% 3.33/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f44,plain,(
% 3.33/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f46,plain,(
% 3.33/1.00    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45,f44])).
% 3.33/1.00  
% 3.33/1.00  fof(f80,plain,(
% 3.33/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f75,plain,(
% 3.33/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f6,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f18,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.33/1.00    inference(pure_predicate_removal,[],[f6])).
% 3.33/1.00  
% 3.33/1.00  fof(f26,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f18])).
% 3.33/1.00  
% 3.33/1.00  fof(f57,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f26])).
% 3.33/1.00  
% 3.33/1.00  fof(f11,axiom,(
% 3.33/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f32,plain,(
% 3.33/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.33/1.00    inference(ennf_transformation,[],[f11])).
% 3.33/1.00  
% 3.33/1.00  fof(f33,plain,(
% 3.33/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(flattening,[],[f32])).
% 3.33/1.00  
% 3.33/1.00  fof(f43,plain,(
% 3.33/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(nnf_transformation,[],[f33])).
% 3.33/1.00  
% 3.33/1.00  fof(f65,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f43])).
% 3.33/1.00  
% 3.33/1.00  fof(f5,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f25,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f5])).
% 3.33/1.00  
% 3.33/1.00  fof(f56,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f25])).
% 3.33/1.00  
% 3.33/1.00  fof(f10,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f30,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f10])).
% 3.33/1.00  
% 3.33/1.00  fof(f31,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(flattening,[],[f30])).
% 3.33/1.00  
% 3.33/1.00  fof(f64,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f31])).
% 3.33/1.00  
% 3.33/1.00  fof(f74,plain,(
% 3.33/1.00    v3_funct_2(sK1,sK0,sK0)),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f72,plain,(
% 3.33/1.00    v1_funct_1(sK1)),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f7,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f27,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f7])).
% 3.33/1.00  
% 3.33/1.00  fof(f58,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f27])).
% 3.33/1.00  
% 3.33/1.00  fof(f15,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f38,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.33/1.00    inference(ennf_transformation,[],[f15])).
% 3.33/1.00  
% 3.33/1.00  fof(f39,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.33/1.00    inference(flattening,[],[f38])).
% 3.33/1.00  
% 3.33/1.00  fof(f71,plain,(
% 3.33/1.00    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f39])).
% 3.33/1.00  
% 3.33/1.00  fof(f14,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f36,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.33/1.00    inference(ennf_transformation,[],[f14])).
% 3.33/1.00  
% 3.33/1.00  fof(f37,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.33/1.00    inference(flattening,[],[f36])).
% 3.33/1.00  
% 3.33/1.00  fof(f69,plain,(
% 3.33/1.00    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f73,plain,(
% 3.33/1.00    v1_funct_2(sK1,sK0,sK0)),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f76,plain,(
% 3.33/1.00    v1_funct_1(sK2)),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f77,plain,(
% 3.33/1.00    v1_funct_2(sK2,sK0,sK0)),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f79,plain,(
% 3.33/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f81,plain,(
% 3.33/1.00    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f12,axiom,(
% 3.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f34,plain,(
% 3.33/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.33/1.00    inference(ennf_transformation,[],[f12])).
% 3.33/1.00  
% 3.33/1.00  fof(f35,plain,(
% 3.33/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.33/1.00    inference(flattening,[],[f34])).
% 3.33/1.00  
% 3.33/1.00  fof(f67,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f35])).
% 3.33/1.00  
% 3.33/1.00  fof(f8,axiom,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f28,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.33/1.00    inference(ennf_transformation,[],[f8])).
% 3.33/1.00  
% 3.33/1.00  fof(f29,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(flattening,[],[f28])).
% 3.33/1.00  
% 3.33/1.00  fof(f42,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(nnf_transformation,[],[f29])).
% 3.33/1.00  
% 3.33/1.00  fof(f60,plain,(
% 3.33/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f42])).
% 3.33/1.00  
% 3.33/1.00  fof(f85,plain,(
% 3.33/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(equality_resolution,[],[f60])).
% 3.33/1.00  
% 3.33/1.00  fof(f4,axiom,(
% 3.33/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f23,plain,(
% 3.33/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.33/1.00    inference(ennf_transformation,[],[f4])).
% 3.33/1.00  
% 3.33/1.00  fof(f24,plain,(
% 3.33/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(flattening,[],[f23])).
% 3.33/1.00  
% 3.33/1.00  fof(f54,plain,(
% 3.33/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f24])).
% 3.33/1.00  
% 3.33/1.00  fof(f63,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f31])).
% 3.33/1.00  
% 3.33/1.00  fof(f1,axiom,(
% 3.33/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f19,plain,(
% 3.33/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f1])).
% 3.33/1.00  
% 3.33/1.00  fof(f20,plain,(
% 3.33/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(flattening,[],[f19])).
% 3.33/1.00  
% 3.33/1.00  fof(f47,plain,(
% 3.33/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f20])).
% 3.33/1.00  
% 3.33/1.00  fof(f3,axiom,(
% 3.33/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f21,plain,(
% 3.33/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.33/1.00    inference(ennf_transformation,[],[f3])).
% 3.33/1.00  
% 3.33/1.00  fof(f22,plain,(
% 3.33/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(flattening,[],[f21])).
% 3.33/1.00  
% 3.33/1.00  fof(f51,plain,(
% 3.33/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f22])).
% 3.33/1.00  
% 3.33/1.00  fof(f48,plain,(
% 3.33/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f20])).
% 3.33/1.00  
% 3.33/1.00  fof(f78,plain,(
% 3.33/1.00    v3_funct_2(sK2,sK0,sK0)),
% 3.33/1.00    inference(cnf_transformation,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f2,axiom,(
% 3.33/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f49,plain,(
% 3.33/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.33/1.00    inference(cnf_transformation,[],[f2])).
% 3.33/1.00  
% 3.33/1.00  fof(f13,axiom,(
% 3.33/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f68,plain,(
% 3.33/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f13])).
% 3.33/1.00  
% 3.33/1.00  fof(f83,plain,(
% 3.33/1.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.33/1.00    inference(definition_unfolding,[],[f49,f68])).
% 3.33/1.00  
% 3.33/1.00  fof(f9,axiom,(
% 3.33/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f61,plain,(
% 3.33/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f9])).
% 3.33/1.00  
% 3.33/1.00  fof(f84,plain,(
% 3.33/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.33/1.00    inference(definition_unfolding,[],[f61,f68])).
% 3.33/1.00  
% 3.33/1.00  cnf(c_25,negated_conjecture,
% 3.33/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1992,plain,
% 3.33/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_30,negated_conjecture,
% 3.33/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1988,plain,
% 3.33/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10,plain,
% 3.33/1.00      ( v5_relat_1(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_19,plain,
% 3.33/1.00      ( ~ v2_funct_2(X0,X1)
% 3.33/1.00      | ~ v5_relat_1(X0,X1)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | k2_relat_1(X0) = X1 ),
% 3.33/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_358,plain,
% 3.33/1.00      ( ~ v2_funct_2(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | k2_relat_1(X0) = X1 ),
% 3.33/1.00      inference(resolution,[status(thm)],[c_10,c_19]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | v1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_370,plain,
% 3.33/1.00      ( ~ v2_funct_2(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.33/1.00      | k2_relat_1(X0) = X1 ),
% 3.33/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_358,c_9]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1984,plain,
% 3.33/1.00      ( k2_relat_1(X0) = X1
% 3.33/1.00      | v2_funct_2(X0,X1) != iProver_top
% 3.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4409,plain,
% 3.33/1.00      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1988,c_1984]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_15,plain,
% 3.33/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.33/1.00      | v2_funct_2(X0,X2)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ v1_funct_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_31,negated_conjecture,
% 3.33/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_504,plain,
% 3.33/1.00      ( v2_funct_2(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | sK1 != X0
% 3.33/1.00      | sK0 != X1
% 3.33/1.00      | sK0 != X2 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_505,plain,
% 3.33/1.00      ( v2_funct_2(sK1,sK0)
% 3.33/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.00      | ~ v1_funct_1(sK1) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_504]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_33,negated_conjecture,
% 3.33/1.00      ( v1_funct_1(sK1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_507,plain,
% 3.33/1.00      ( v2_funct_2(sK1,sK0) ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_505,c_33,c_30]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_584,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k2_relat_1(X0) = X2
% 3.33/1.00      | sK1 != X0
% 3.33/1.00      | sK0 != X2 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_370,c_507]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_585,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.33/1.00      | k2_relat_1(sK1) = sK0 ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_584]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_587,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.00      | k2_relat_1(sK1) = sK0 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_585]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5190,plain,
% 3.33/1.00      ( k2_relat_1(sK1) = sK0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_4409,c_30,c_587]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_11,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1999,plain,
% 3.33/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4426,plain,
% 3.33/1.00      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1988,c_1999]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5193,plain,
% 3.33/1.00      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_5190,c_4426]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_23,plain,
% 3.33/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.33/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.33/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.33/1.00      | ~ v1_funct_1(X2)
% 3.33/1.00      | ~ v1_funct_1(X3)
% 3.33/1.00      | ~ v2_funct_1(X2)
% 3.33/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.33/1.00      | k2_funct_1(X2) = X3
% 3.33/1.00      | k1_xboole_0 = X0
% 3.33/1.00      | k1_xboole_0 = X1 ),
% 3.33/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_22,plain,
% 3.33/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.33/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.33/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.33/1.00      | ~ v1_funct_1(X2)
% 3.33/1.00      | ~ v1_funct_1(X3)
% 3.33/1.00      | v2_funct_1(X2) ),
% 3.33/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_185,plain,
% 3.33/1.00      ( ~ v1_funct_1(X3)
% 3.33/1.00      | ~ v1_funct_1(X2)
% 3.33/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.33/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.33/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.33/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.33/1.00      | k2_funct_1(X2) = X3
% 3.33/1.00      | k1_xboole_0 = X0
% 3.33/1.00      | k1_xboole_0 = X1 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_23,c_22]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_186,plain,
% 3.33/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.33/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.33/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.33/1.00      | ~ v1_funct_1(X2)
% 3.33/1.00      | ~ v1_funct_1(X3)
% 3.33/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.33/1.00      | k2_funct_1(X2) = X3
% 3.33/1.00      | k1_xboole_0 = X0
% 3.33/1.00      | k1_xboole_0 = X1 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_185]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1985,plain,
% 3.33/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.33/1.00      | k2_funct_1(X2) = X3
% 3.33/1.00      | k1_xboole_0 = X0
% 3.33/1.00      | k1_xboole_0 = X1
% 3.33/1.00      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.33/1.00      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.33/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.33/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.33/1.00      | v1_funct_1(X2) != iProver_top
% 3.33/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5244,plain,
% 3.33/1.00      ( k2_funct_1(sK1) = X0
% 3.33/1.00      | sK0 = k1_xboole_0
% 3.33/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.33/1.00      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.33/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.33/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.33/1.00      | v1_funct_1(X0) != iProver_top
% 3.33/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_5193,c_1985]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_34,plain,
% 3.33/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_32,negated_conjecture,
% 3.33/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_35,plain,
% 3.33/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_37,plain,
% 3.33/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8061,plain,
% 3.33/1.00      ( v1_funct_1(X0) != iProver_top
% 3.33/1.00      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.33/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.33/1.00      | sK0 = k1_xboole_0
% 3.33/1.00      | k2_funct_1(sK1) = X0
% 3.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_5244,c_34,c_35,c_37]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8062,plain,
% 3.33/1.00      ( k2_funct_1(sK1) = X0
% 3.33/1.00      | sK0 = k1_xboole_0
% 3.33/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.33/1.00      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.33/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_8061]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8073,plain,
% 3.33/1.00      ( k2_funct_1(sK1) = sK2
% 3.33/1.00      | sK0 = k1_xboole_0
% 3.33/1.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.33/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1992,c_8062]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_29,negated_conjecture,
% 3.33/1.00      ( v1_funct_1(sK2) ),
% 3.33/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_28,negated_conjecture,
% 3.33/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_26,negated_conjecture,
% 3.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8074,plain,
% 3.33/1.00      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.00      | ~ v1_funct_1(sK2)
% 3.33/1.00      | k2_funct_1(sK1) = sK2
% 3.33/1.00      | sK0 = k1_xboole_0 ),
% 3.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_8073]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8212,plain,
% 3.33/1.00      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_8073,c_38,c_39,c_41]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8213,plain,
% 3.33/1.00      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_8212]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_24,negated_conjecture,
% 3.33/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1993,plain,
% 3.33/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_20,plain,
% 3.33/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.33/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_523,plain,
% 3.33/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.33/1.00      | sK1 != X0
% 3.33/1.00      | sK0 != X1 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_524,plain,
% 3.33/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.33/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.00      | ~ v1_funct_1(sK1)
% 3.33/1.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_523]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_526,plain,
% 3.33/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_524,c_33,c_32,c_30]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2038,plain,
% 3.33/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_1993,c_526]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8222,plain,
% 3.33/1.00      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_8213,c_2038]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_41,plain,
% 3.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_12,plain,
% 3.33/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2321,plain,
% 3.33/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2322,plain,
% 3.33/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2321]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8247,plain,
% 3.33/1.00      ( sK0 = k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_8222,c_41,c_2322]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1986,plain,
% 3.33/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8,plain,
% 3.33/1.00      ( ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v2_funct_1(X0)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2001,plain,
% 3.33/1.00      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.33/1.00      | v1_funct_1(X0) != iProver_top
% 3.33/1.00      | v2_funct_1(X0) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5425,plain,
% 3.33/1.00      ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
% 3.33/1.00      | v2_funct_1(sK1) != iProver_top
% 3.33/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1986,c_2001]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5429,plain,
% 3.33/1.00      ( k1_relat_1(k2_funct_1(sK1)) = sK0
% 3.33/1.00      | v2_funct_1(sK1) != iProver_top
% 3.33/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_5425,c_5190]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_16,plain,
% 3.33/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | v2_funct_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_493,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | v2_funct_1(X0)
% 3.33/1.00      | sK1 != X0
% 3.33/1.00      | sK0 != X2
% 3.33/1.00      | sK0 != X1 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_494,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.00      | ~ v1_funct_1(sK1)
% 3.33/1.00      | v2_funct_1(sK1) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_493]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_495,plain,
% 3.33/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.33/1.00      | v1_funct_1(sK1) != iProver_top
% 3.33/1.00      | v2_funct_1(sK1) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2276,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.00      | v1_relat_1(sK1) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2277,plain,
% 3.33/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.33/1.00      | v1_relat_1(sK1) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2276]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5950,plain,
% 3.33/1.00      ( k1_relat_1(k2_funct_1(sK1)) = sK0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_5429,c_34,c_37,c_495,c_2277]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1,plain,
% 3.33/1.00      ( ~ v1_relat_1(X0)
% 3.33/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.33/1.00      | k1_xboole_0 = X0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2006,plain,
% 3.33/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.33/1.00      | k1_xboole_0 = X0
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5953,plain,
% 3.33/1.00      ( k2_funct_1(sK1) = k1_xboole_0
% 3.33/1.00      | sK0 != k1_xboole_0
% 3.33/1.00      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_5950,c_2006]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6,plain,
% 3.33/1.00      ( ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v2_funct_1(X0)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2263,plain,
% 3.33/1.00      ( ~ v1_funct_1(sK1)
% 3.33/1.00      | ~ v2_funct_1(sK1)
% 3.33/1.00      | v1_relat_1(k2_funct_1(sK1))
% 3.33/1.00      | ~ v1_relat_1(sK1) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2264,plain,
% 3.33/1.00      ( v1_funct_1(sK1) != iProver_top
% 3.33/1.00      | v2_funct_1(sK1) != iProver_top
% 3.33/1.00      | v1_relat_1(k2_funct_1(sK1)) = iProver_top
% 3.33/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2263]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7444,plain,
% 3.33/1.00      ( sK0 != k1_xboole_0 | k2_funct_1(sK1) = k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_5953,c_34,c_37,c_495,c_2264,c_2277]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7445,plain,
% 3.33/1.00      ( k2_funct_1(sK1) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_7444]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8255,plain,
% 3.33/1.00      ( k2_funct_1(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_8247,c_7445]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8370,plain,
% 3.33/1.00      ( k2_funct_1(sK1) = k1_xboole_0 ),
% 3.33/1.00      inference(equality_resolution_simp,[status(thm)],[c_8255]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_0,plain,
% 3.33/1.00      ( ~ v1_relat_1(X0)
% 3.33/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.33/1.00      | k1_xboole_0 = X0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2007,plain,
% 3.33/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.33/1.00      | k1_xboole_0 = X0
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5194,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0
% 3.33/1.00      | sK0 != k1_xboole_0
% 3.33/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_5190,c_2007]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5226,plain,
% 3.33/1.00      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_5194,c_37,c_2277]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5227,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_5226]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8264,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_8247,c_5227]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8335,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(equality_resolution_simp,[status(thm)],[c_8264]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8371,plain,
% 3.33/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_8370,c_8335]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1991,plain,
% 3.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4408,plain,
% 3.33/1.00      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1991,c_1984]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_27,negated_conjecture,
% 3.33/1.00      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_482,plain,
% 3.33/1.00      ( v2_funct_2(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | sK2 != X0
% 3.33/1.00      | sK0 != X1
% 3.33/1.00      | sK0 != X2 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_483,plain,
% 3.33/1.00      ( v2_funct_2(sK2,sK0)
% 3.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.00      | ~ v1_funct_1(sK2) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_482]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_485,plain,
% 3.33/1.00      ( v2_funct_2(sK2,sK0) ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_483,c_29,c_26]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_574,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k2_relat_1(X0) = X2
% 3.33/1.00      | sK2 != X0
% 3.33/1.00      | sK0 != X2 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_370,c_485]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_575,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.33/1.00      | k2_relat_1(sK2) = sK0 ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_574]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_577,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.00      | k2_relat_1(sK2) = sK0 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_575]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5121,plain,
% 3.33/1.00      ( k2_relat_1(sK2) = sK0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_4408,c_26,c_577]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5125,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0
% 3.33/1.00      | sK0 != k1_xboole_0
% 3.33/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_5121,c_2007]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2273,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.00      | v1_relat_1(sK2) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5136,plain,
% 3.33/1.00      ( ~ v1_relat_1(sK2) | sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5125]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5221,plain,
% 3.33/1.00      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_5125,c_26,c_2273,c_5136]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5222,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_5221]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8265,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_8247,c_5222]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8315,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0 ),
% 3.33/1.00      inference(equality_resolution_simp,[status(thm)],[c_8265]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8272,plain,
% 3.33/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_8247,c_2038]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8320,plain,
% 3.33/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_8315,c_8272]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8337,plain,
% 3.33/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_8335,c_8320]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8374,plain,
% 3.33/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_8371,c_8337]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3,plain,
% 3.33/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3413,plain,
% 3.33/1.00      ( k6_partfun1(X0) = k1_xboole_0
% 3.33/1.00      | k1_xboole_0 != X0
% 3.33/1.00      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3,c_2006]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_14,plain,
% 3.33/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_69,plain,
% 3.33/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2268,plain,
% 3.33/1.00      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.33/1.00      | v1_relat_1(k6_partfun1(X0)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2269,plain,
% 3.33/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.33/1.00      | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2268]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3534,plain,
% 3.33/1.00      ( k1_xboole_0 != X0 | k6_partfun1(X0) = k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_3413,c_69,c_2269]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3535,plain,
% 3.33/1.00      ( k6_partfun1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_3534]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3539,plain,
% 3.33/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.33/1.00      inference(equality_resolution,[status(thm)],[c_3535]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1996,plain,
% 3.33/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3837,plain,
% 3.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3539,c_1996]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1998,plain,
% 3.33/1.00      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3994,plain,
% 3.33/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3837,c_1998]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(contradiction,plain,
% 3.33/1.00      ( $false ),
% 3.33/1.00      inference(minisat,[status(thm)],[c_8374,c_3994]) ).
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  ------                               Statistics
% 3.33/1.00  
% 3.33/1.00  ------ General
% 3.33/1.00  
% 3.33/1.00  abstr_ref_over_cycles:                  0
% 3.33/1.00  abstr_ref_under_cycles:                 0
% 3.33/1.00  gc_basic_clause_elim:                   0
% 3.33/1.00  forced_gc_time:                         0
% 3.33/1.00  parsing_time:                           0.015
% 3.33/1.00  unif_index_cands_time:                  0.
% 3.33/1.00  unif_index_add_time:                    0.
% 3.33/1.00  orderings_time:                         0.
% 3.33/1.00  out_proof_time:                         0.014
% 3.33/1.00  total_time:                             0.278
% 3.33/1.00  num_of_symbols:                         53
% 3.33/1.00  num_of_terms:                           8912
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing
% 3.33/1.00  
% 3.33/1.00  num_of_splits:                          0
% 3.33/1.00  num_of_split_atoms:                     0
% 3.33/1.00  num_of_reused_defs:                     0
% 3.33/1.00  num_eq_ax_congr_red:                    12
% 3.33/1.00  num_of_sem_filtered_clauses:            1
% 3.33/1.00  num_of_subtypes:                        0
% 3.33/1.00  monotx_restored_types:                  0
% 3.33/1.00  sat_num_of_epr_types:                   0
% 3.33/1.00  sat_num_of_non_cyclic_types:            0
% 3.33/1.00  sat_guarded_non_collapsed_types:        0
% 3.33/1.00  num_pure_diseq_elim:                    0
% 3.33/1.00  simp_replaced_by:                       0
% 3.33/1.00  res_preprocessed:                       167
% 3.33/1.00  prep_upred:                             0
% 3.33/1.00  prep_unflattend:                        86
% 3.33/1.00  smt_new_axioms:                         0
% 3.33/1.00  pred_elim_cands:                        7
% 3.33/1.00  pred_elim:                              2
% 3.33/1.00  pred_elim_cl:                           0
% 3.33/1.00  pred_elim_cycles:                       7
% 3.33/1.00  merged_defs:                            0
% 3.33/1.00  merged_defs_ncl:                        0
% 3.33/1.00  bin_hyper_res:                          0
% 3.33/1.00  prep_cycles:                            4
% 3.33/1.00  pred_elim_time:                         0.02
% 3.33/1.00  splitting_time:                         0.
% 3.33/1.00  sem_filter_time:                        0.
% 3.33/1.00  monotx_time:                            0.001
% 3.33/1.00  subtype_inf_time:                       0.
% 3.33/1.00  
% 3.33/1.00  ------ Problem properties
% 3.33/1.00  
% 3.33/1.00  clauses:                                33
% 3.33/1.00  conjectures:                            8
% 3.33/1.00  epr:                                    8
% 3.33/1.00  horn:                                   32
% 3.33/1.00  ground:                                 14
% 3.33/1.00  unary:                                  17
% 3.33/1.00  binary:                                 4
% 3.33/1.00  lits:                                   85
% 3.33/1.00  lits_eq:                                17
% 3.33/1.00  fd_pure:                                0
% 3.33/1.00  fd_pseudo:                              0
% 3.33/1.00  fd_cond:                                2
% 3.33/1.00  fd_pseudo_cond:                         3
% 3.33/1.00  ac_symbols:                             0
% 3.33/1.00  
% 3.33/1.00  ------ Propositional Solver
% 3.33/1.00  
% 3.33/1.00  prop_solver_calls:                      26
% 3.33/1.00  prop_fast_solver_calls:                 1388
% 3.33/1.00  smt_solver_calls:                       0
% 3.33/1.00  smt_fast_solver_calls:                  0
% 3.33/1.00  prop_num_of_clauses:                    3516
% 3.33/1.00  prop_preprocess_simplified:             10002
% 3.33/1.00  prop_fo_subsumed:                       48
% 3.33/1.00  prop_solver_time:                       0.
% 3.33/1.00  smt_solver_time:                        0.
% 3.33/1.00  smt_fast_solver_time:                   0.
% 3.33/1.00  prop_fast_solver_time:                  0.
% 3.33/1.00  prop_unsat_core_time:                   0.
% 3.33/1.00  
% 3.33/1.00  ------ QBF
% 3.33/1.00  
% 3.33/1.00  qbf_q_res:                              0
% 3.33/1.00  qbf_num_tautologies:                    0
% 3.33/1.00  qbf_prep_cycles:                        0
% 3.33/1.00  
% 3.33/1.00  ------ BMC1
% 3.33/1.00  
% 3.33/1.00  bmc1_current_bound:                     -1
% 3.33/1.00  bmc1_last_solved_bound:                 -1
% 3.33/1.00  bmc1_unsat_core_size:                   -1
% 3.33/1.00  bmc1_unsat_core_parents_size:           -1
% 3.33/1.00  bmc1_merge_next_fun:                    0
% 3.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation
% 3.33/1.00  
% 3.33/1.00  inst_num_of_clauses:                    1085
% 3.33/1.00  inst_num_in_passive:                    480
% 3.33/1.00  inst_num_in_active:                     403
% 3.33/1.00  inst_num_in_unprocessed:                202
% 3.33/1.00  inst_num_of_loops:                      410
% 3.33/1.00  inst_num_of_learning_restarts:          0
% 3.33/1.00  inst_num_moves_active_passive:          6
% 3.33/1.00  inst_lit_activity:                      0
% 3.33/1.00  inst_lit_activity_moves:                0
% 3.33/1.00  inst_num_tautologies:                   0
% 3.33/1.00  inst_num_prop_implied:                  0
% 3.33/1.00  inst_num_existing_simplified:           0
% 3.33/1.00  inst_num_eq_res_simplified:             0
% 3.33/1.00  inst_num_child_elim:                    0
% 3.33/1.00  inst_num_of_dismatching_blockings:      52
% 3.33/1.00  inst_num_of_non_proper_insts:           547
% 3.33/1.00  inst_num_of_duplicates:                 0
% 3.33/1.00  inst_inst_num_from_inst_to_res:         0
% 3.33/1.00  inst_dismatching_checking_time:         0.
% 3.33/1.00  
% 3.33/1.00  ------ Resolution
% 3.33/1.00  
% 3.33/1.00  res_num_of_clauses:                     0
% 3.33/1.00  res_num_in_passive:                     0
% 3.33/1.00  res_num_in_active:                      0
% 3.33/1.00  res_num_of_loops:                       171
% 3.33/1.00  res_forward_subset_subsumed:            18
% 3.33/1.00  res_backward_subset_subsumed:           0
% 3.33/1.00  res_forward_subsumed:                   0
% 3.33/1.00  res_backward_subsumed:                  0
% 3.33/1.00  res_forward_subsumption_resolution:     2
% 3.33/1.00  res_backward_subsumption_resolution:    0
% 3.33/1.00  res_clause_to_clause_subsumption:       200
% 3.33/1.00  res_orphan_elimination:                 0
% 3.33/1.00  res_tautology_del:                      50
% 3.33/1.00  res_num_eq_res_simplified:              0
% 3.33/1.00  res_num_sel_changes:                    0
% 3.33/1.00  res_moves_from_active_to_pass:          0
% 3.33/1.00  
% 3.33/1.00  ------ Superposition
% 3.33/1.00  
% 3.33/1.00  sup_time_total:                         0.
% 3.33/1.00  sup_time_generating:                    0.
% 3.33/1.00  sup_time_sim_full:                      0.
% 3.33/1.00  sup_time_sim_immed:                     0.
% 3.33/1.00  
% 3.33/1.00  sup_num_of_clauses:                     62
% 3.33/1.00  sup_num_in_active:                      46
% 3.33/1.00  sup_num_in_passive:                     16
% 3.33/1.00  sup_num_of_loops:                       81
% 3.33/1.00  sup_fw_superposition:                   53
% 3.33/1.00  sup_bw_superposition:                   27
% 3.33/1.00  sup_immediate_simplified:               59
% 3.33/1.00  sup_given_eliminated:                   0
% 3.33/1.00  comparisons_done:                       0
% 3.33/1.00  comparisons_avoided:                    3
% 3.33/1.00  
% 3.33/1.00  ------ Simplifications
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  sim_fw_subset_subsumed:                 9
% 3.33/1.00  sim_bw_subset_subsumed:                 4
% 3.33/1.00  sim_fw_subsumed:                        3
% 3.33/1.00  sim_bw_subsumed:                        0
% 3.33/1.00  sim_fw_subsumption_res:                 0
% 3.33/1.00  sim_bw_subsumption_res:                 0
% 3.33/1.00  sim_tautology_del:                      0
% 3.33/1.00  sim_eq_tautology_del:                   14
% 3.33/1.00  sim_eq_res_simp:                        4
% 3.33/1.00  sim_fw_demodulated:                     4
% 3.33/1.00  sim_bw_demodulated:                     55
% 3.33/1.00  sim_light_normalised:                   29
% 3.33/1.00  sim_joinable_taut:                      0
% 3.33/1.00  sim_joinable_simp:                      0
% 3.33/1.00  sim_ac_normalised:                      0
% 3.33/1.00  sim_smt_subsumption:                    0
% 3.33/1.00  
%------------------------------------------------------------------------------
