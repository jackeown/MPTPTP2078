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
% DateTime   : Thu Dec  3 12:07:12 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_37)

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
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46,f45])).

fof(f80,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f78,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_24,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1451,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2041,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1447,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2045,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1447])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1458,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2034,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_3234,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2045,c_2034])).

cnf(c_22,plain,
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

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_182,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_21])).

cnf(c_183,plain,
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
    inference(renaming,[status(thm)],[c_182])).

cnf(c_1444,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
    | ~ v1_funct_2(X3_50,X1_50,X0_50)
    | ~ v1_funct_2(X2_50,X0_50,X1_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ v1_funct_1(X2_50)
    | ~ v1_funct_1(X3_50)
    | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | k2_funct_1(X2_50) = X3_50
    | k1_xboole_0 = X0_50
    | k1_xboole_0 = X1_50 ),
    inference(subtyping,[status(esa)],[c_183])).

cnf(c_2048,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_5026,plain,
    ( k2_funct_1(sK1) = X0_50
    | k2_relat_1(sK1) != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3234,c_2048])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_501,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_502,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_355,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_9,c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_367,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_355,c_8])).

cnf(c_1443,plain,
    ( ~ v2_funct_2(X0_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
    | k2_relat_1(X0_50) = X1_50 ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_2351,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_2353,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(c_6460,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0_50
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5026,c_32,c_33,c_34,c_29,c_36,c_502,c_2353])).

cnf(c_6461,plain,
    ( k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_6460])).

cnf(c_6472,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2041,c_6461])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6473,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6472])).

cnf(c_6695,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6472,c_37,c_38,c_40])).

cnf(c_6696,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6695])).

cnf(c_23,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1452,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2040,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1452])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_520,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_521,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_523,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_32,c_31,c_29])).

cnf(c_1436,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_523])).

cnf(c_2083,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2040,c_1436])).

cnf(c_6703,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6696,c_2083])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1457,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2356,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_2357,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2356])).

cnf(c_6734,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6703,c_40,c_2357])).

cnf(c_1450,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2042,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_2049,plain,
    ( k2_relat_1(X0_50) = X1_50
    | v2_funct_2(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1443])).

cnf(c_5102,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2042,c_2049])).

cnf(c_26,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_479,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_480,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_2346,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_2348,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_5267,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5102,c_28,c_25,c_480,c_2348])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1467,plain,
    ( ~ v1_relat_1(X0_50)
    | k2_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2026,plain,
    ( k2_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1467])).

cnf(c_5282,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5267,c_2026])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2293,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_2294,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2293])).

cnf(c_5743,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5282,c_40,c_2294])).

cnf(c_5744,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5743])).

cnf(c_6744,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6734,c_5744])).

cnf(c_6857,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6744])).

cnf(c_5103,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2045,c_2049])).

cnf(c_5294,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5103,c_32,c_29,c_502,c_2353])).

cnf(c_1445,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2047,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1445])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1460,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k1_relat_1(k2_funct_1(X0_50)) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2032,plain,
    ( k1_relat_1(k2_funct_1(X0_50)) = k2_relat_1(X0_50)
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_4025,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2047,c_2032])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_491,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_2296,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_2337,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_4289,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4025,c_32,c_29,c_491,c_2296,c_2337])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1466,plain,
    ( ~ v1_relat_1(X0_50)
    | k1_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2027,plain,
    ( k1_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_4292,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4289,c_2027])).

cnf(c_492,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_2297,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2296])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1462,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | v1_relat_1(k2_funct_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2307,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_2308,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2307])).

cnf(c_4965,plain,
    ( k2_relat_1(sK1) != k1_xboole_0
    | k2_funct_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4292,c_33,c_36,c_492,c_2297,c_2308])).

cnf(c_4966,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4965])).

cnf(c_5297,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5294,c_4966])).

cnf(c_6745,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6734,c_5297])).

cnf(c_6847,plain,
    ( k2_funct_1(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6745])).

cnf(c_6761,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6734,c_2083])).

cnf(c_6850,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6847,c_6761])).

cnf(c_6859,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6857,c_6850])).

cnf(c_2,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1465,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1455,plain,
    ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2037,plain,
    ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_2451,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_2037])).

cnf(c_2035,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_3252,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2451,c_2035])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6859,c_3252])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:50:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.00  
% 3.00/1.00  ------  iProver source info
% 3.00/1.00  
% 3.00/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.00  git: non_committed_changes: false
% 3.00/1.00  git: last_make_outside_of_git: false
% 3.00/1.00  
% 3.00/1.00  ------ 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options
% 3.00/1.00  
% 3.00/1.00  --out_options                           all
% 3.00/1.00  --tptp_safe_out                         true
% 3.00/1.00  --problem_path                          ""
% 3.00/1.00  --include_path                          ""
% 3.00/1.00  --clausifier                            res/vclausify_rel
% 3.00/1.00  --clausifier_options                    --mode clausify
% 3.00/1.00  --stdin                                 false
% 3.00/1.00  --stats_out                             all
% 3.00/1.00  
% 3.00/1.00  ------ General Options
% 3.00/1.00  
% 3.00/1.00  --fof                                   false
% 3.00/1.00  --time_out_real                         305.
% 3.00/1.00  --time_out_virtual                      -1.
% 3.00/1.00  --symbol_type_check                     false
% 3.00/1.00  --clausify_out                          false
% 3.00/1.00  --sig_cnt_out                           false
% 3.00/1.00  --trig_cnt_out                          false
% 3.00/1.00  --trig_cnt_out_tolerance                1.
% 3.00/1.00  --trig_cnt_out_sk_spl                   false
% 3.00/1.00  --abstr_cl_out                          false
% 3.00/1.00  
% 3.00/1.00  ------ Global Options
% 3.00/1.00  
% 3.00/1.00  --schedule                              default
% 3.00/1.00  --add_important_lit                     false
% 3.00/1.00  --prop_solver_per_cl                    1000
% 3.00/1.00  --min_unsat_core                        false
% 3.00/1.00  --soft_assumptions                      false
% 3.00/1.00  --soft_lemma_size                       3
% 3.00/1.00  --prop_impl_unit_size                   0
% 3.00/1.00  --prop_impl_unit                        []
% 3.00/1.00  --share_sel_clauses                     true
% 3.00/1.00  --reset_solvers                         false
% 3.00/1.00  --bc_imp_inh                            [conj_cone]
% 3.00/1.00  --conj_cone_tolerance                   3.
% 3.00/1.00  --extra_neg_conj                        none
% 3.00/1.00  --large_theory_mode                     true
% 3.00/1.00  --prolific_symb_bound                   200
% 3.00/1.00  --lt_threshold                          2000
% 3.00/1.00  --clause_weak_htbl                      true
% 3.00/1.00  --gc_record_bc_elim                     false
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing Options
% 3.00/1.00  
% 3.00/1.00  --preprocessing_flag                    true
% 3.00/1.00  --time_out_prep_mult                    0.1
% 3.00/1.00  --splitting_mode                        input
% 3.00/1.00  --splitting_grd                         true
% 3.00/1.00  --splitting_cvd                         false
% 3.00/1.00  --splitting_cvd_svl                     false
% 3.00/1.00  --splitting_nvd                         32
% 3.00/1.00  --sub_typing                            true
% 3.00/1.00  --prep_gs_sim                           true
% 3.00/1.00  --prep_unflatten                        true
% 3.00/1.00  --prep_res_sim                          true
% 3.00/1.00  --prep_upred                            true
% 3.00/1.00  --prep_sem_filter                       exhaustive
% 3.00/1.00  --prep_sem_filter_out                   false
% 3.00/1.00  --pred_elim                             true
% 3.00/1.00  --res_sim_input                         true
% 3.00/1.00  --eq_ax_congr_red                       true
% 3.00/1.00  --pure_diseq_elim                       true
% 3.00/1.00  --brand_transform                       false
% 3.00/1.00  --non_eq_to_eq                          false
% 3.00/1.00  --prep_def_merge                        true
% 3.00/1.00  --prep_def_merge_prop_impl              false
% 3.00/1.00  --prep_def_merge_mbd                    true
% 3.00/1.00  --prep_def_merge_tr_red                 false
% 3.00/1.00  --prep_def_merge_tr_cl                  false
% 3.00/1.00  --smt_preprocessing                     true
% 3.00/1.00  --smt_ac_axioms                         fast
% 3.00/1.00  --preprocessed_out                      false
% 3.00/1.00  --preprocessed_stats                    false
% 3.00/1.00  
% 3.00/1.00  ------ Abstraction refinement Options
% 3.00/1.00  
% 3.00/1.00  --abstr_ref                             []
% 3.00/1.00  --abstr_ref_prep                        false
% 3.00/1.00  --abstr_ref_until_sat                   false
% 3.00/1.00  --abstr_ref_sig_restrict                funpre
% 3.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.00  --abstr_ref_under                       []
% 3.00/1.00  
% 3.00/1.00  ------ SAT Options
% 3.00/1.00  
% 3.00/1.00  --sat_mode                              false
% 3.00/1.00  --sat_fm_restart_options                ""
% 3.00/1.00  --sat_gr_def                            false
% 3.00/1.00  --sat_epr_types                         true
% 3.00/1.00  --sat_non_cyclic_types                  false
% 3.00/1.00  --sat_finite_models                     false
% 3.00/1.00  --sat_fm_lemmas                         false
% 3.00/1.00  --sat_fm_prep                           false
% 3.00/1.00  --sat_fm_uc_incr                        true
% 3.00/1.00  --sat_out_model                         small
% 3.00/1.00  --sat_out_clauses                       false
% 3.00/1.00  
% 3.00/1.00  ------ QBF Options
% 3.00/1.00  
% 3.00/1.00  --qbf_mode                              false
% 3.00/1.00  --qbf_elim_univ                         false
% 3.00/1.00  --qbf_dom_inst                          none
% 3.00/1.00  --qbf_dom_pre_inst                      false
% 3.00/1.00  --qbf_sk_in                             false
% 3.00/1.00  --qbf_pred_elim                         true
% 3.00/1.00  --qbf_split                             512
% 3.00/1.00  
% 3.00/1.00  ------ BMC1 Options
% 3.00/1.00  
% 3.00/1.00  --bmc1_incremental                      false
% 3.00/1.00  --bmc1_axioms                           reachable_all
% 3.00/1.00  --bmc1_min_bound                        0
% 3.00/1.00  --bmc1_max_bound                        -1
% 3.00/1.00  --bmc1_max_bound_default                -1
% 3.00/1.00  --bmc1_symbol_reachability              true
% 3.00/1.00  --bmc1_property_lemmas                  false
% 3.00/1.00  --bmc1_k_induction                      false
% 3.00/1.00  --bmc1_non_equiv_states                 false
% 3.00/1.00  --bmc1_deadlock                         false
% 3.00/1.00  --bmc1_ucm                              false
% 3.00/1.00  --bmc1_add_unsat_core                   none
% 3.00/1.00  --bmc1_unsat_core_children              false
% 3.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.00  --bmc1_out_stat                         full
% 3.00/1.00  --bmc1_ground_init                      false
% 3.00/1.00  --bmc1_pre_inst_next_state              false
% 3.00/1.00  --bmc1_pre_inst_state                   false
% 3.00/1.00  --bmc1_pre_inst_reach_state             false
% 3.00/1.00  --bmc1_out_unsat_core                   false
% 3.00/1.00  --bmc1_aig_witness_out                  false
% 3.00/1.00  --bmc1_verbose                          false
% 3.00/1.00  --bmc1_dump_clauses_tptp                false
% 3.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.00  --bmc1_dump_file                        -
% 3.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.00  --bmc1_ucm_extend_mode                  1
% 3.00/1.00  --bmc1_ucm_init_mode                    2
% 3.00/1.00  --bmc1_ucm_cone_mode                    none
% 3.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.00  --bmc1_ucm_relax_model                  4
% 3.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.00  --bmc1_ucm_layered_model                none
% 3.00/1.00  --bmc1_ucm_max_lemma_size               10
% 3.00/1.00  
% 3.00/1.00  ------ AIG Options
% 3.00/1.00  
% 3.00/1.00  --aig_mode                              false
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation Options
% 3.00/1.00  
% 3.00/1.00  --instantiation_flag                    true
% 3.00/1.00  --inst_sos_flag                         false
% 3.00/1.00  --inst_sos_phase                        true
% 3.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel_side                     num_symb
% 3.00/1.00  --inst_solver_per_active                1400
% 3.00/1.00  --inst_solver_calls_frac                1.
% 3.00/1.00  --inst_passive_queue_type               priority_queues
% 3.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.00  --inst_passive_queues_freq              [25;2]
% 3.00/1.00  --inst_dismatching                      true
% 3.00/1.00  --inst_eager_unprocessed_to_passive     true
% 3.00/1.00  --inst_prop_sim_given                   true
% 3.00/1.00  --inst_prop_sim_new                     false
% 3.00/1.00  --inst_subs_new                         false
% 3.00/1.00  --inst_eq_res_simp                      false
% 3.00/1.00  --inst_subs_given                       false
% 3.00/1.00  --inst_orphan_elimination               true
% 3.00/1.00  --inst_learning_loop_flag               true
% 3.00/1.00  --inst_learning_start                   3000
% 3.00/1.00  --inst_learning_factor                  2
% 3.00/1.00  --inst_start_prop_sim_after_learn       3
% 3.00/1.00  --inst_sel_renew                        solver
% 3.00/1.00  --inst_lit_activity_flag                true
% 3.00/1.00  --inst_restr_to_given                   false
% 3.00/1.00  --inst_activity_threshold               500
% 3.00/1.00  --inst_out_proof                        true
% 3.00/1.00  
% 3.00/1.00  ------ Resolution Options
% 3.00/1.00  
% 3.00/1.00  --resolution_flag                       true
% 3.00/1.00  --res_lit_sel                           adaptive
% 3.00/1.00  --res_lit_sel_side                      none
% 3.00/1.00  --res_ordering                          kbo
% 3.00/1.00  --res_to_prop_solver                    active
% 3.00/1.00  --res_prop_simpl_new                    false
% 3.00/1.00  --res_prop_simpl_given                  true
% 3.00/1.00  --res_passive_queue_type                priority_queues
% 3.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.00  --res_passive_queues_freq               [15;5]
% 3.00/1.00  --res_forward_subs                      full
% 3.00/1.00  --res_backward_subs                     full
% 3.00/1.00  --res_forward_subs_resolution           true
% 3.00/1.00  --res_backward_subs_resolution          true
% 3.00/1.00  --res_orphan_elimination                true
% 3.00/1.00  --res_time_limit                        2.
% 3.00/1.00  --res_out_proof                         true
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Options
% 3.00/1.00  
% 3.00/1.00  --superposition_flag                    true
% 3.00/1.00  --sup_passive_queue_type                priority_queues
% 3.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.00  --demod_completeness_check              fast
% 3.00/1.00  --demod_use_ground                      true
% 3.00/1.00  --sup_to_prop_solver                    passive
% 3.00/1.00  --sup_prop_simpl_new                    true
% 3.00/1.00  --sup_prop_simpl_given                  true
% 3.00/1.00  --sup_fun_splitting                     false
% 3.00/1.00  --sup_smt_interval                      50000
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Simplification Setup
% 3.00/1.00  
% 3.00/1.00  --sup_indices_passive                   []
% 3.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_full_bw                           [BwDemod]
% 3.00/1.00  --sup_immed_triv                        [TrivRules]
% 3.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_immed_bw_main                     []
% 3.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  
% 3.00/1.00  ------ Combination Options
% 3.00/1.00  
% 3.00/1.00  --comb_res_mult                         3
% 3.00/1.00  --comb_sup_mult                         2
% 3.00/1.00  --comb_inst_mult                        10
% 3.00/1.00  
% 3.00/1.00  ------ Debug Options
% 3.00/1.00  
% 3.00/1.00  --dbg_backtrace                         false
% 3.00/1.00  --dbg_dump_prop_clauses                 false
% 3.00/1.00  --dbg_dump_prop_clauses_file            -
% 3.00/1.00  --dbg_out_stat                          false
% 3.00/1.00  ------ Parsing...
% 3.00/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.00  ------ Proving...
% 3.00/1.00  ------ Problem Properties 
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  clauses                                 32
% 3.00/1.00  conjectures                             8
% 3.00/1.00  EPR                                     8
% 3.00/1.00  Horn                                    31
% 3.00/1.00  unary                                   16
% 3.00/1.00  binary                                  4
% 3.00/1.00  lits                                    84
% 3.00/1.00  lits eq                                 16
% 3.00/1.00  fd_pure                                 0
% 3.00/1.00  fd_pseudo                               0
% 3.00/1.00  fd_cond                                 2
% 3.00/1.00  fd_pseudo_cond                          3
% 3.00/1.00  AC symbols                              0
% 3.00/1.00  
% 3.00/1.00  ------ Schedule dynamic 5 is on 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  ------ 
% 3.00/1.00  Current options:
% 3.00/1.00  ------ 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options
% 3.00/1.00  
% 3.00/1.00  --out_options                           all
% 3.00/1.00  --tptp_safe_out                         true
% 3.00/1.00  --problem_path                          ""
% 3.00/1.00  --include_path                          ""
% 3.00/1.00  --clausifier                            res/vclausify_rel
% 3.00/1.00  --clausifier_options                    --mode clausify
% 3.00/1.00  --stdin                                 false
% 3.00/1.00  --stats_out                             all
% 3.00/1.00  
% 3.00/1.00  ------ General Options
% 3.00/1.00  
% 3.00/1.00  --fof                                   false
% 3.00/1.00  --time_out_real                         305.
% 3.00/1.00  --time_out_virtual                      -1.
% 3.00/1.00  --symbol_type_check                     false
% 3.00/1.00  --clausify_out                          false
% 3.00/1.00  --sig_cnt_out                           false
% 3.00/1.00  --trig_cnt_out                          false
% 3.00/1.00  --trig_cnt_out_tolerance                1.
% 3.00/1.00  --trig_cnt_out_sk_spl                   false
% 3.00/1.00  --abstr_cl_out                          false
% 3.00/1.00  
% 3.00/1.00  ------ Global Options
% 3.00/1.00  
% 3.00/1.00  --schedule                              default
% 3.00/1.00  --add_important_lit                     false
% 3.00/1.00  --prop_solver_per_cl                    1000
% 3.00/1.00  --min_unsat_core                        false
% 3.00/1.00  --soft_assumptions                      false
% 3.00/1.00  --soft_lemma_size                       3
% 3.00/1.00  --prop_impl_unit_size                   0
% 3.00/1.00  --prop_impl_unit                        []
% 3.00/1.00  --share_sel_clauses                     true
% 3.00/1.00  --reset_solvers                         false
% 3.00/1.00  --bc_imp_inh                            [conj_cone]
% 3.00/1.00  --conj_cone_tolerance                   3.
% 3.00/1.00  --extra_neg_conj                        none
% 3.00/1.00  --large_theory_mode                     true
% 3.00/1.00  --prolific_symb_bound                   200
% 3.00/1.00  --lt_threshold                          2000
% 3.00/1.00  --clause_weak_htbl                      true
% 3.00/1.00  --gc_record_bc_elim                     false
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing Options
% 3.00/1.00  
% 3.00/1.00  --preprocessing_flag                    true
% 3.00/1.00  --time_out_prep_mult                    0.1
% 3.00/1.00  --splitting_mode                        input
% 3.00/1.00  --splitting_grd                         true
% 3.00/1.00  --splitting_cvd                         false
% 3.00/1.00  --splitting_cvd_svl                     false
% 3.00/1.00  --splitting_nvd                         32
% 3.00/1.00  --sub_typing                            true
% 3.00/1.00  --prep_gs_sim                           true
% 3.00/1.00  --prep_unflatten                        true
% 3.00/1.00  --prep_res_sim                          true
% 3.00/1.00  --prep_upred                            true
% 3.00/1.00  --prep_sem_filter                       exhaustive
% 3.00/1.00  --prep_sem_filter_out                   false
% 3.00/1.00  --pred_elim                             true
% 3.00/1.00  --res_sim_input                         true
% 3.00/1.00  --eq_ax_congr_red                       true
% 3.00/1.00  --pure_diseq_elim                       true
% 3.00/1.00  --brand_transform                       false
% 3.00/1.00  --non_eq_to_eq                          false
% 3.00/1.00  --prep_def_merge                        true
% 3.00/1.00  --prep_def_merge_prop_impl              false
% 3.00/1.00  --prep_def_merge_mbd                    true
% 3.00/1.00  --prep_def_merge_tr_red                 false
% 3.00/1.00  --prep_def_merge_tr_cl                  false
% 3.00/1.00  --smt_preprocessing                     true
% 3.00/1.00  --smt_ac_axioms                         fast
% 3.00/1.00  --preprocessed_out                      false
% 3.00/1.00  --preprocessed_stats                    false
% 3.00/1.00  
% 3.00/1.00  ------ Abstraction refinement Options
% 3.00/1.00  
% 3.00/1.00  --abstr_ref                             []
% 3.00/1.00  --abstr_ref_prep                        false
% 3.00/1.00  --abstr_ref_until_sat                   false
% 3.00/1.00  --abstr_ref_sig_restrict                funpre
% 3.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.00  --abstr_ref_under                       []
% 3.00/1.00  
% 3.00/1.00  ------ SAT Options
% 3.00/1.00  
% 3.00/1.00  --sat_mode                              false
% 3.00/1.00  --sat_fm_restart_options                ""
% 3.00/1.00  --sat_gr_def                            false
% 3.00/1.00  --sat_epr_types                         true
% 3.00/1.00  --sat_non_cyclic_types                  false
% 3.00/1.00  --sat_finite_models                     false
% 3.00/1.00  --sat_fm_lemmas                         false
% 3.00/1.00  --sat_fm_prep                           false
% 3.00/1.00  --sat_fm_uc_incr                        true
% 3.00/1.00  --sat_out_model                         small
% 3.00/1.00  --sat_out_clauses                       false
% 3.00/1.00  
% 3.00/1.00  ------ QBF Options
% 3.00/1.00  
% 3.00/1.00  --qbf_mode                              false
% 3.00/1.00  --qbf_elim_univ                         false
% 3.00/1.00  --qbf_dom_inst                          none
% 3.00/1.00  --qbf_dom_pre_inst                      false
% 3.00/1.00  --qbf_sk_in                             false
% 3.00/1.00  --qbf_pred_elim                         true
% 3.00/1.00  --qbf_split                             512
% 3.00/1.00  
% 3.00/1.00  ------ BMC1 Options
% 3.00/1.00  
% 3.00/1.00  --bmc1_incremental                      false
% 3.00/1.00  --bmc1_axioms                           reachable_all
% 3.00/1.00  --bmc1_min_bound                        0
% 3.00/1.00  --bmc1_max_bound                        -1
% 3.00/1.00  --bmc1_max_bound_default                -1
% 3.00/1.00  --bmc1_symbol_reachability              true
% 3.00/1.00  --bmc1_property_lemmas                  false
% 3.00/1.00  --bmc1_k_induction                      false
% 3.00/1.00  --bmc1_non_equiv_states                 false
% 3.00/1.00  --bmc1_deadlock                         false
% 3.00/1.00  --bmc1_ucm                              false
% 3.00/1.00  --bmc1_add_unsat_core                   none
% 3.00/1.00  --bmc1_unsat_core_children              false
% 3.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.00  --bmc1_out_stat                         full
% 3.00/1.00  --bmc1_ground_init                      false
% 3.00/1.00  --bmc1_pre_inst_next_state              false
% 3.00/1.00  --bmc1_pre_inst_state                   false
% 3.00/1.00  --bmc1_pre_inst_reach_state             false
% 3.00/1.00  --bmc1_out_unsat_core                   false
% 3.00/1.00  --bmc1_aig_witness_out                  false
% 3.00/1.00  --bmc1_verbose                          false
% 3.00/1.00  --bmc1_dump_clauses_tptp                false
% 3.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.00  --bmc1_dump_file                        -
% 3.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.00  --bmc1_ucm_extend_mode                  1
% 3.00/1.00  --bmc1_ucm_init_mode                    2
% 3.00/1.00  --bmc1_ucm_cone_mode                    none
% 3.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.00  --bmc1_ucm_relax_model                  4
% 3.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.00  --bmc1_ucm_layered_model                none
% 3.00/1.00  --bmc1_ucm_max_lemma_size               10
% 3.00/1.00  
% 3.00/1.00  ------ AIG Options
% 3.00/1.00  
% 3.00/1.00  --aig_mode                              false
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation Options
% 3.00/1.00  
% 3.00/1.00  --instantiation_flag                    true
% 3.00/1.00  --inst_sos_flag                         false
% 3.00/1.00  --inst_sos_phase                        true
% 3.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel_side                     none
% 3.00/1.00  --inst_solver_per_active                1400
% 3.00/1.00  --inst_solver_calls_frac                1.
% 3.00/1.00  --inst_passive_queue_type               priority_queues
% 3.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.00  --inst_passive_queues_freq              [25;2]
% 3.00/1.00  --inst_dismatching                      true
% 3.00/1.00  --inst_eager_unprocessed_to_passive     true
% 3.00/1.00  --inst_prop_sim_given                   true
% 3.00/1.00  --inst_prop_sim_new                     false
% 3.00/1.00  --inst_subs_new                         false
% 3.00/1.00  --inst_eq_res_simp                      false
% 3.00/1.00  --inst_subs_given                       false
% 3.00/1.00  --inst_orphan_elimination               true
% 3.00/1.00  --inst_learning_loop_flag               true
% 3.00/1.00  --inst_learning_start                   3000
% 3.00/1.00  --inst_learning_factor                  2
% 3.00/1.00  --inst_start_prop_sim_after_learn       3
% 3.00/1.00  --inst_sel_renew                        solver
% 3.00/1.00  --inst_lit_activity_flag                true
% 3.00/1.00  --inst_restr_to_given                   false
% 3.00/1.00  --inst_activity_threshold               500
% 3.00/1.00  --inst_out_proof                        true
% 3.00/1.00  
% 3.00/1.00  ------ Resolution Options
% 3.00/1.00  
% 3.00/1.00  --resolution_flag                       false
% 3.00/1.00  --res_lit_sel                           adaptive
% 3.00/1.00  --res_lit_sel_side                      none
% 3.00/1.00  --res_ordering                          kbo
% 3.00/1.00  --res_to_prop_solver                    active
% 3.00/1.00  --res_prop_simpl_new                    false
% 3.00/1.00  --res_prop_simpl_given                  true
% 3.00/1.00  --res_passive_queue_type                priority_queues
% 3.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.00  --res_passive_queues_freq               [15;5]
% 3.00/1.00  --res_forward_subs                      full
% 3.00/1.00  --res_backward_subs                     full
% 3.00/1.00  --res_forward_subs_resolution           true
% 3.00/1.00  --res_backward_subs_resolution          true
% 3.00/1.00  --res_orphan_elimination                true
% 3.00/1.00  --res_time_limit                        2.
% 3.00/1.00  --res_out_proof                         true
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Options
% 3.00/1.00  
% 3.00/1.00  --superposition_flag                    true
% 3.00/1.00  --sup_passive_queue_type                priority_queues
% 3.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.00  --demod_completeness_check              fast
% 3.00/1.00  --demod_use_ground                      true
% 3.00/1.00  --sup_to_prop_solver                    passive
% 3.00/1.00  --sup_prop_simpl_new                    true
% 3.00/1.00  --sup_prop_simpl_given                  true
% 3.00/1.00  --sup_fun_splitting                     false
% 3.00/1.00  --sup_smt_interval                      50000
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Simplification Setup
% 3.00/1.00  
% 3.00/1.00  --sup_indices_passive                   []
% 3.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_full_bw                           [BwDemod]
% 3.00/1.00  --sup_immed_triv                        [TrivRules]
% 3.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_immed_bw_main                     []
% 3.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  
% 3.00/1.00  ------ Combination Options
% 3.00/1.00  
% 3.00/1.00  --comb_res_mult                         3
% 3.00/1.00  --comb_sup_mult                         2
% 3.00/1.00  --comb_inst_mult                        10
% 3.00/1.00  
% 3.00/1.00  ------ Debug Options
% 3.00/1.00  
% 3.00/1.00  --dbg_backtrace                         false
% 3.00/1.00  --dbg_dump_prop_clauses                 false
% 3.00/1.00  --dbg_dump_prop_clauses_file            -
% 3.00/1.00  --dbg_out_stat                          false
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  ------ Proving...
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  % SZS status Theorem for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  fof(f16,conjecture,(
% 3.00/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f17,negated_conjecture,(
% 3.00/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.00/1.00    inference(negated_conjecture,[],[f16])).
% 3.00/1.00  
% 3.00/1.00  fof(f41,plain,(
% 3.00/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.00/1.00    inference(ennf_transformation,[],[f17])).
% 3.00/1.00  
% 3.00/1.00  fof(f42,plain,(
% 3.00/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.00/1.00    inference(flattening,[],[f41])).
% 3.00/1.00  
% 3.00/1.00  fof(f46,plain,(
% 3.00/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f45,plain,(
% 3.00/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f47,plain,(
% 3.00/1.00    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46,f45])).
% 3.00/1.00  
% 3.00/1.00  fof(f80,plain,(
% 3.00/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f75,plain,(
% 3.00/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f7,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f28,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.00    inference(ennf_transformation,[],[f7])).
% 3.00/1.00  
% 3.00/1.00  fof(f58,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f28])).
% 3.00/1.00  
% 3.00/1.00  fof(f15,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f39,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.00/1.00    inference(ennf_transformation,[],[f15])).
% 3.00/1.00  
% 3.00/1.00  fof(f40,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.00/1.00    inference(flattening,[],[f39])).
% 3.00/1.00  
% 3.00/1.00  fof(f71,plain,(
% 3.00/1.00    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f40])).
% 3.00/1.00  
% 3.00/1.00  fof(f14,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f37,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.00/1.00    inference(ennf_transformation,[],[f14])).
% 3.00/1.00  
% 3.00/1.00  fof(f38,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.00/1.00    inference(flattening,[],[f37])).
% 3.00/1.00  
% 3.00/1.00  fof(f69,plain,(
% 3.00/1.00    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f38])).
% 3.00/1.00  
% 3.00/1.00  fof(f72,plain,(
% 3.00/1.00    v1_funct_1(sK1)),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f73,plain,(
% 3.00/1.00    v1_funct_2(sK1,sK0,sK0)),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f9,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f31,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.00    inference(ennf_transformation,[],[f9])).
% 3.00/1.00  
% 3.00/1.00  fof(f32,plain,(
% 3.00/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.00    inference(flattening,[],[f31])).
% 3.00/1.00  
% 3.00/1.00  fof(f63,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f32])).
% 3.00/1.00  
% 3.00/1.00  fof(f74,plain,(
% 3.00/1.00    v3_funct_2(sK1,sK0,sK0)),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f6,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f19,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.00/1.00    inference(pure_predicate_removal,[],[f6])).
% 3.00/1.00  
% 3.00/1.00  fof(f27,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.00    inference(ennf_transformation,[],[f19])).
% 3.00/1.00  
% 3.00/1.00  fof(f57,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f27])).
% 3.00/1.00  
% 3.00/1.00  fof(f10,axiom,(
% 3.00/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f33,plain,(
% 3.00/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.00/1.00    inference(ennf_transformation,[],[f10])).
% 3.00/1.00  
% 3.00/1.00  fof(f34,plain,(
% 3.00/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.00/1.00    inference(flattening,[],[f33])).
% 3.00/1.00  
% 3.00/1.00  fof(f44,plain,(
% 3.00/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.00/1.00    inference(nnf_transformation,[],[f34])).
% 3.00/1.00  
% 3.00/1.00  fof(f64,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f44])).
% 3.00/1.00  
% 3.00/1.00  fof(f5,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f26,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.00    inference(ennf_transformation,[],[f5])).
% 3.00/1.00  
% 3.00/1.00  fof(f56,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f26])).
% 3.00/1.00  
% 3.00/1.00  fof(f76,plain,(
% 3.00/1.00    v1_funct_1(sK2)),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f77,plain,(
% 3.00/1.00    v1_funct_2(sK2,sK0,sK0)),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f79,plain,(
% 3.00/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f81,plain,(
% 3.00/1.00    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f12,axiom,(
% 3.00/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f35,plain,(
% 3.00/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.00/1.00    inference(ennf_transformation,[],[f12])).
% 3.00/1.00  
% 3.00/1.00  fof(f36,plain,(
% 3.00/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.00/1.00    inference(flattening,[],[f35])).
% 3.00/1.00  
% 3.00/1.00  fof(f67,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f36])).
% 3.00/1.00  
% 3.00/1.00  fof(f8,axiom,(
% 3.00/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f29,plain,(
% 3.00/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.00/1.00    inference(ennf_transformation,[],[f8])).
% 3.00/1.00  
% 3.00/1.00  fof(f30,plain,(
% 3.00/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.00    inference(flattening,[],[f29])).
% 3.00/1.00  
% 3.00/1.00  fof(f43,plain,(
% 3.00/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.00    inference(nnf_transformation,[],[f30])).
% 3.00/1.00  
% 3.00/1.00  fof(f60,plain,(
% 3.00/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f43])).
% 3.00/1.00  
% 3.00/1.00  fof(f83,plain,(
% 3.00/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.00    inference(equality_resolution,[],[f60])).
% 3.00/1.00  
% 3.00/1.00  fof(f78,plain,(
% 3.00/1.00    v3_funct_2(sK2,sK0,sK0)),
% 3.00/1.00    inference(cnf_transformation,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f1,axiom,(
% 3.00/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f20,plain,(
% 3.00/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.00/1.00    inference(ennf_transformation,[],[f1])).
% 3.00/1.00  
% 3.00/1.00  fof(f21,plain,(
% 3.00/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.00/1.00    inference(flattening,[],[f20])).
% 3.00/1.00  
% 3.00/1.00  fof(f49,plain,(
% 3.00/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f21])).
% 3.00/1.00  
% 3.00/1.00  fof(f4,axiom,(
% 3.00/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f24,plain,(
% 3.00/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/1.00    inference(ennf_transformation,[],[f4])).
% 3.00/1.00  
% 3.00/1.00  fof(f25,plain,(
% 3.00/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/1.00    inference(flattening,[],[f24])).
% 3.00/1.00  
% 3.00/1.00  fof(f54,plain,(
% 3.00/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f25])).
% 3.00/1.00  
% 3.00/1.00  fof(f62,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f32])).
% 3.00/1.00  
% 3.00/1.00  fof(f48,plain,(
% 3.00/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f21])).
% 3.00/1.00  
% 3.00/1.00  fof(f3,axiom,(
% 3.00/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f22,plain,(
% 3.00/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/1.00    inference(ennf_transformation,[],[f3])).
% 3.00/1.00  
% 3.00/1.00  fof(f23,plain,(
% 3.00/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/1.00    inference(flattening,[],[f22])).
% 3.00/1.00  
% 3.00/1.00  fof(f51,plain,(
% 3.00/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f23])).
% 3.00/1.00  
% 3.00/1.00  fof(f2,axiom,(
% 3.00/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f50,plain,(
% 3.00/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.00/1.00    inference(cnf_transformation,[],[f2])).
% 3.00/1.00  
% 3.00/1.00  fof(f13,axiom,(
% 3.00/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f68,plain,(
% 3.00/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f13])).
% 3.00/1.00  
% 3.00/1.00  fof(f82,plain,(
% 3.00/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.00/1.00    inference(definition_unfolding,[],[f50,f68])).
% 3.00/1.00  
% 3.00/1.00  fof(f11,axiom,(
% 3.00/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f18,plain,(
% 3.00/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.00/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.00/1.00  
% 3.00/1.00  fof(f66,plain,(
% 3.00/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f18])).
% 3.00/1.00  
% 3.00/1.00  cnf(c_24,negated_conjecture,
% 3.00/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1451,negated_conjecture,
% 3.00/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.00/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2041,plain,
% 3.00/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_29,negated_conjecture,
% 3.00/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.00/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1447,negated_conjecture,
% 3.00/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.00/1.00      inference(subtyping,[status(esa)],[c_29]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2045,plain,
% 3.00/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1447]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_10,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1458,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 3.00/1.00      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 3.00/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2034,plain,
% 3.00/1.00      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 3.00/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3234,plain,
% 3.00/1.00      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_2045,c_2034]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_22,plain,
% 3.00/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.00/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.00/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.00/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.00/1.00      | ~ v1_funct_1(X2)
% 3.00/1.00      | ~ v1_funct_1(X3)
% 3.00/1.00      | ~ v2_funct_1(X2)
% 3.00/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.00/1.00      | k2_funct_1(X2) = X3
% 3.00/1.00      | k1_xboole_0 = X0
% 3.00/1.00      | k1_xboole_0 = X1 ),
% 3.00/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_21,plain,
% 3.00/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.00/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.00/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.00/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.00/1.00      | ~ v1_funct_1(X2)
% 3.00/1.00      | ~ v1_funct_1(X3)
% 3.00/1.00      | v2_funct_1(X2) ),
% 3.00/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_182,plain,
% 3.00/1.00      ( ~ v1_funct_1(X3)
% 3.00/1.00      | ~ v1_funct_1(X2)
% 3.00/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.00/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.00/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.00/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.00/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.00/1.00      | k2_funct_1(X2) = X3
% 3.00/1.00      | k1_xboole_0 = X0
% 3.00/1.00      | k1_xboole_0 = X1 ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_22,c_21]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_183,plain,
% 3.00/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.00/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.00/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.00/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.00/1.00      | ~ v1_funct_1(X2)
% 3.00/1.00      | ~ v1_funct_1(X3)
% 3.00/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.00/1.00      | k2_funct_1(X2) = X3
% 3.00/1.00      | k1_xboole_0 = X0
% 3.00/1.00      | k1_xboole_0 = X1 ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_182]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1444,plain,
% 3.00/1.00      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
% 3.00/1.00      | ~ v1_funct_2(X3_50,X1_50,X0_50)
% 3.00/1.00      | ~ v1_funct_2(X2_50,X0_50,X1_50)
% 3.00/1.00      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 3.00/1.00      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 3.00/1.00      | ~ v1_funct_1(X2_50)
% 3.00/1.00      | ~ v1_funct_1(X3_50)
% 3.00/1.00      | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 3.00/1.00      | k2_funct_1(X2_50) = X3_50
% 3.00/1.00      | k1_xboole_0 = X0_50
% 3.00/1.00      | k1_xboole_0 = X1_50 ),
% 3.00/1.00      inference(subtyping,[status(esa)],[c_183]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2048,plain,
% 3.00/1.00      ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 3.00/1.00      | k2_funct_1(X2_50) = X3_50
% 3.00/1.00      | k1_xboole_0 = X0_50
% 3.00/1.00      | k1_xboole_0 = X1_50
% 3.00/1.00      | r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50)) != iProver_top
% 3.00/1.00      | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
% 3.00/1.00      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 3.00/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 3.00/1.00      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 3.00/1.00      | v1_funct_1(X2_50) != iProver_top
% 3.00/1.00      | v1_funct_1(X3_50) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1444]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_5026,plain,
% 3.00/1.00      ( k2_funct_1(sK1) = X0_50
% 3.00/1.00      | k2_relat_1(sK1) != sK0
% 3.00/1.00      | sK0 = k1_xboole_0
% 3.00/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.00/1.00      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.00/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.00/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.00/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.00/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.00/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_3234,c_2048]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_32,negated_conjecture,
% 3.00/1.00      ( v1_funct_1(sK1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_33,plain,
% 3.00/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_31,negated_conjecture,
% 3.00/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_34,plain,
% 3.00/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_36,plain,
% 3.00/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_13,plain,
% 3.00/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.00/1.00      | v2_funct_2(X0,X2)
% 3.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.00      | ~ v1_funct_1(X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_30,negated_conjecture,
% 3.00/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_501,plain,
% 3.00/1.00      ( v2_funct_2(X0,X1)
% 3.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.00/1.00      | ~ v1_funct_1(X0)
% 3.00/1.00      | sK1 != X0
% 3.00/1.00      | sK0 != X1
% 3.00/1.00      | sK0 != X2 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_502,plain,
% 3.00/1.00      ( v2_funct_2(sK1,sK0)
% 3.00/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/1.00      | ~ v1_funct_1(sK1) ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_501]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_9,plain,
% 3.00/1.00      ( v5_relat_1(X0,X1)
% 3.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.00/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_17,plain,
% 3.00/1.00      ( ~ v2_funct_2(X0,X1)
% 3.00/1.00      | ~ v5_relat_1(X0,X1)
% 3.00/1.00      | ~ v1_relat_1(X0)
% 3.00/1.00      | k2_relat_1(X0) = X1 ),
% 3.00/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_355,plain,
% 3.00/1.00      ( ~ v2_funct_2(X0,X1)
% 3.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.00/1.00      | ~ v1_relat_1(X0)
% 3.00/1.00      | k2_relat_1(X0) = X1 ),
% 3.00/1.01      inference(resolution,[status(thm)],[c_9,c_17]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_8,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | v1_relat_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_367,plain,
% 3.00/1.01      ( ~ v2_funct_2(X0,X1)
% 3.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.00/1.01      | k2_relat_1(X0) = X1 ),
% 3.00/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_355,c_8]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1443,plain,
% 3.00/1.01      ( ~ v2_funct_2(X0_50,X1_50)
% 3.00/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
% 3.00/1.01      | k2_relat_1(X0_50) = X1_50 ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_367]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2351,plain,
% 3.00/1.01      ( ~ v2_funct_2(sK1,sK0)
% 3.00/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
% 3.00/1.01      | k2_relat_1(sK1) = sK0 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1443]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2353,plain,
% 3.00/1.01      ( ~ v2_funct_2(sK1,sK0)
% 3.00/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/1.01      | k2_relat_1(sK1) = sK0 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_2351]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6460,plain,
% 3.00/1.01      ( v1_funct_1(X0_50) != iProver_top
% 3.00/1.01      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.00/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.00/1.01      | sK0 = k1_xboole_0
% 3.00/1.01      | k2_funct_1(sK1) = X0_50
% 3.00/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_5026,c_32,c_33,c_34,c_29,c_36,c_502,c_2353]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6461,plain,
% 3.00/1.01      ( k2_funct_1(sK1) = X0_50
% 3.00/1.01      | sK0 = k1_xboole_0
% 3.00/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.00/1.01      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.00/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.00/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 3.00/1.01      inference(renaming,[status(thm)],[c_6460]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6472,plain,
% 3.00/1.01      ( k2_funct_1(sK1) = sK2
% 3.00/1.01      | sK0 = k1_xboole_0
% 3.00/1.01      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.00/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.00/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_2041,c_6461]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_28,negated_conjecture,
% 3.00/1.01      ( v1_funct_1(sK2) ),
% 3.00/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_27,negated_conjecture,
% 3.00/1.01      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_25,negated_conjecture,
% 3.00/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6473,plain,
% 3.00/1.01      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.00/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/1.01      | ~ v1_funct_1(sK2)
% 3.00/1.01      | k2_funct_1(sK1) = sK2
% 3.00/1.01      | sK0 = k1_xboole_0 ),
% 3.00/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6472]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6695,plain,
% 3.00/1.01      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_6472,c_37,c_38,c_40]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6696,plain,
% 3.00/1.01      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.00/1.01      inference(renaming,[status(thm)],[c_6695]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_23,negated_conjecture,
% 3.00/1.01      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.00/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1452,negated_conjecture,
% 3.00/1.01      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2040,plain,
% 3.00/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1452]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_19,plain,
% 3.00/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.00/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.00/1.01      | ~ v1_funct_1(X0)
% 3.00/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_520,plain,
% 3.00/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.00/1.01      | ~ v1_funct_1(X0)
% 3.00/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.00/1.01      | sK1 != X0
% 3.00/1.01      | sK0 != X1 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_521,plain,
% 3.00/1.01      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.00/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/1.01      | ~ v1_funct_1(sK1)
% 3.00/1.01      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_520]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_523,plain,
% 3.00/1.01      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_521,c_32,c_31,c_29]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1436,plain,
% 3.00/1.01      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_523]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2083,plain,
% 3.00/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.00/1.01      inference(light_normalisation,[status(thm)],[c_2040,c_1436]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6703,plain,
% 3.00/1.01      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_6696,c_2083]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_40,plain,
% 3.00/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_11,plain,
% 3.00/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1457,plain,
% 3.00/1.01      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
% 3.00/1.01      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2356,plain,
% 3.00/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.00/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1457]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2357,plain,
% 3.00/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.00/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_2356]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6734,plain,
% 3.00/1.01      ( sK0 = k1_xboole_0 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_6703,c_40,c_2357]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1450,negated_conjecture,
% 3.00/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_25]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2042,plain,
% 3.00/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1450]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2049,plain,
% 3.00/1.01      ( k2_relat_1(X0_50) = X1_50
% 3.00/1.01      | v2_funct_2(X0_50,X1_50) != iProver_top
% 3.00/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1443]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5102,plain,
% 3.00/1.01      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_2042,c_2049]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_26,negated_conjecture,
% 3.00/1.01      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_479,plain,
% 3.00/1.01      ( v2_funct_2(X0,X1)
% 3.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.00/1.01      | ~ v1_funct_1(X0)
% 3.00/1.01      | sK2 != X0
% 3.00/1.01      | sK0 != X1
% 3.00/1.01      | sK0 != X2 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_480,plain,
% 3.00/1.01      ( v2_funct_2(sK2,sK0)
% 3.00/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/1.01      | ~ v1_funct_1(sK2) ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_479]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2346,plain,
% 3.00/1.01      ( ~ v2_funct_2(sK2,sK0)
% 3.00/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
% 3.00/1.01      | k2_relat_1(sK2) = sK0 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1443]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2348,plain,
% 3.00/1.01      ( ~ v2_funct_2(sK2,sK0)
% 3.00/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/1.01      | k2_relat_1(sK2) = sK0 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_2346]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5267,plain,
% 3.00/1.01      ( k2_relat_1(sK2) = sK0 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_5102,c_28,c_25,c_480,c_2348]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_0,plain,
% 3.00/1.01      ( ~ v1_relat_1(X0)
% 3.00/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.00/1.01      | k1_xboole_0 = X0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1467,plain,
% 3.00/1.01      ( ~ v1_relat_1(X0_50)
% 3.00/1.01      | k2_relat_1(X0_50) != k1_xboole_0
% 3.00/1.01      | k1_xboole_0 = X0_50 ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2026,plain,
% 3.00/1.01      ( k2_relat_1(X0_50) != k1_xboole_0
% 3.00/1.01      | k1_xboole_0 = X0_50
% 3.00/1.01      | v1_relat_1(X0_50) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1467]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5282,plain,
% 3.00/1.01      ( sK2 = k1_xboole_0
% 3.00/1.01      | sK0 != k1_xboole_0
% 3.00/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_5267,c_2026]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1459,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 3.00/1.01      | v1_relat_1(X0_50) ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2293,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/1.01      | v1_relat_1(sK2) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1459]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2294,plain,
% 3.00/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.00/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_2293]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5743,plain,
% 3.00/1.01      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_5282,c_40,c_2294]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5744,plain,
% 3.00/1.01      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.00/1.01      inference(renaming,[status(thm)],[c_5743]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6744,plain,
% 3.00/1.01      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_6734,c_5744]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6857,plain,
% 3.00/1.01      ( sK2 = k1_xboole_0 ),
% 3.00/1.01      inference(equality_resolution_simp,[status(thm)],[c_6744]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5103,plain,
% 3.00/1.01      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_2045,c_2049]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5294,plain,
% 3.00/1.01      ( k2_relat_1(sK1) = sK0 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_5103,c_32,c_29,c_502,c_2353]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1445,negated_conjecture,
% 3.00/1.01      ( v1_funct_1(sK1) ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_32]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2047,plain,
% 3.00/1.01      ( v1_funct_1(sK1) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1445]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_7,plain,
% 3.00/1.01      ( ~ v1_funct_1(X0)
% 3.00/1.01      | ~ v2_funct_1(X0)
% 3.00/1.01      | ~ v1_relat_1(X0)
% 3.00/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1460,plain,
% 3.00/1.01      ( ~ v1_funct_1(X0_50)
% 3.00/1.01      | ~ v2_funct_1(X0_50)
% 3.00/1.01      | ~ v1_relat_1(X0_50)
% 3.00/1.01      | k1_relat_1(k2_funct_1(X0_50)) = k2_relat_1(X0_50) ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2032,plain,
% 3.00/1.01      ( k1_relat_1(k2_funct_1(X0_50)) = k2_relat_1(X0_50)
% 3.00/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.00/1.01      | v2_funct_1(X0_50) != iProver_top
% 3.00/1.01      | v1_relat_1(X0_50) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4025,plain,
% 3.00/1.01      ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
% 3.00/1.01      | v2_funct_1(sK1) != iProver_top
% 3.00/1.01      | v1_relat_1(sK1) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_2047,c_2032]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_14,plain,
% 3.00/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | ~ v1_funct_1(X0)
% 3.00/1.01      | v2_funct_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_490,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | ~ v1_funct_1(X0)
% 3.00/1.01      | v2_funct_1(X0)
% 3.00/1.01      | sK1 != X0
% 3.00/1.01      | sK0 != X2
% 3.00/1.01      | sK0 != X1 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_491,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/1.01      | ~ v1_funct_1(sK1)
% 3.00/1.01      | v2_funct_1(sK1) ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_490]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2296,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/1.01      | v1_relat_1(sK1) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1459]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2337,plain,
% 3.00/1.01      ( ~ v1_funct_1(sK1)
% 3.00/1.01      | ~ v2_funct_1(sK1)
% 3.00/1.01      | ~ v1_relat_1(sK1)
% 3.00/1.01      | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1460]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4289,plain,
% 3.00/1.01      ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_4025,c_32,c_29,c_491,c_2296,c_2337]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1,plain,
% 3.00/1.01      ( ~ v1_relat_1(X0)
% 3.00/1.01      | k1_relat_1(X0) != k1_xboole_0
% 3.00/1.01      | k1_xboole_0 = X0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1466,plain,
% 3.00/1.01      ( ~ v1_relat_1(X0_50)
% 3.00/1.01      | k1_relat_1(X0_50) != k1_xboole_0
% 3.00/1.01      | k1_xboole_0 = X0_50 ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2027,plain,
% 3.00/1.01      ( k1_relat_1(X0_50) != k1_xboole_0
% 3.00/1.01      | k1_xboole_0 = X0_50
% 3.00/1.01      | v1_relat_1(X0_50) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4292,plain,
% 3.00/1.01      ( k2_funct_1(sK1) = k1_xboole_0
% 3.00/1.01      | k2_relat_1(sK1) != k1_xboole_0
% 3.00/1.01      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_4289,c_2027]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_492,plain,
% 3.00/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.00/1.01      | v1_funct_1(sK1) != iProver_top
% 3.00/1.01      | v2_funct_1(sK1) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2297,plain,
% 3.00/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.00/1.01      | v1_relat_1(sK1) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_2296]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5,plain,
% 3.00/1.01      ( ~ v1_funct_1(X0)
% 3.00/1.01      | ~ v2_funct_1(X0)
% 3.00/1.01      | ~ v1_relat_1(X0)
% 3.00/1.01      | v1_relat_1(k2_funct_1(X0)) ),
% 3.00/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1462,plain,
% 3.00/1.01      ( ~ v1_funct_1(X0_50)
% 3.00/1.01      | ~ v2_funct_1(X0_50)
% 3.00/1.01      | ~ v1_relat_1(X0_50)
% 3.00/1.01      | v1_relat_1(k2_funct_1(X0_50)) ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2307,plain,
% 3.00/1.01      ( ~ v1_funct_1(sK1)
% 3.00/1.01      | ~ v2_funct_1(sK1)
% 3.00/1.01      | v1_relat_1(k2_funct_1(sK1))
% 3.00/1.01      | ~ v1_relat_1(sK1) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1462]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2308,plain,
% 3.00/1.01      ( v1_funct_1(sK1) != iProver_top
% 3.00/1.01      | v2_funct_1(sK1) != iProver_top
% 3.00/1.01      | v1_relat_1(k2_funct_1(sK1)) = iProver_top
% 3.00/1.01      | v1_relat_1(sK1) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_2307]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4965,plain,
% 3.00/1.01      ( k2_relat_1(sK1) != k1_xboole_0 | k2_funct_1(sK1) = k1_xboole_0 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_4292,c_33,c_36,c_492,c_2297,c_2308]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4966,plain,
% 3.00/1.01      ( k2_funct_1(sK1) = k1_xboole_0 | k2_relat_1(sK1) != k1_xboole_0 ),
% 3.00/1.01      inference(renaming,[status(thm)],[c_4965]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5297,plain,
% 3.00/1.01      ( k2_funct_1(sK1) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_5294,c_4966]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6745,plain,
% 3.00/1.01      ( k2_funct_1(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_6734,c_5297]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6847,plain,
% 3.00/1.01      ( k2_funct_1(sK1) = k1_xboole_0 ),
% 3.00/1.01      inference(equality_resolution_simp,[status(thm)],[c_6745]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6761,plain,
% 3.00/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_6734,c_2083]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6850,plain,
% 3.00/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_6847,c_6761]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6859,plain,
% 3.00/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_6857,c_6850]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2,plain,
% 3.00/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1465,plain,
% 3.00/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_18,plain,
% 3.00/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1455,plain,
% 3.00/1.01      ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
% 3.00/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2037,plain,
% 3.00/1.01      ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2451,plain,
% 3.00/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1465,c_2037]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2035,plain,
% 3.00/1.01      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
% 3.00/1.01      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3252,plain,
% 3.00/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_2451,c_2035]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(contradiction,plain,
% 3.00/1.01      ( $false ),
% 3.00/1.01      inference(minisat,[status(thm)],[c_6859,c_3252]) ).
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  ------                               Statistics
% 3.00/1.01  
% 3.00/1.01  ------ General
% 3.00/1.01  
% 3.00/1.01  abstr_ref_over_cycles:                  0
% 3.00/1.01  abstr_ref_under_cycles:                 0
% 3.00/1.01  gc_basic_clause_elim:                   0
% 3.00/1.01  forced_gc_time:                         0
% 3.00/1.01  parsing_time:                           0.013
% 3.00/1.01  unif_index_cands_time:                  0.
% 3.00/1.01  unif_index_add_time:                    0.
% 3.00/1.01  orderings_time:                         0.
% 3.00/1.01  out_proof_time:                         0.012
% 3.00/1.01  total_time:                             0.27
% 3.00/1.01  num_of_symbols:                         56
% 3.00/1.01  num_of_terms:                           7893
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing
% 3.00/1.01  
% 3.00/1.01  num_of_splits:                          0
% 3.00/1.01  num_of_split_atoms:                     0
% 3.00/1.01  num_of_reused_defs:                     0
% 3.00/1.01  num_eq_ax_congr_red:                    12
% 3.00/1.01  num_of_sem_filtered_clauses:            1
% 3.00/1.01  num_of_subtypes:                        3
% 3.00/1.01  monotx_restored_types:                  1
% 3.00/1.01  sat_num_of_epr_types:                   0
% 3.00/1.01  sat_num_of_non_cyclic_types:            0
% 3.00/1.01  sat_guarded_non_collapsed_types:        1
% 3.00/1.01  num_pure_diseq_elim:                    0
% 3.00/1.01  simp_replaced_by:                       0
% 3.00/1.01  res_preprocessed:                       167
% 3.00/1.01  prep_upred:                             0
% 3.00/1.01  prep_unflattend:                        86
% 3.00/1.01  smt_new_axioms:                         0
% 3.00/1.01  pred_elim_cands:                        7
% 3.00/1.01  pred_elim:                              2
% 3.00/1.01  pred_elim_cl:                           0
% 3.00/1.01  pred_elim_cycles:                       7
% 3.00/1.01  merged_defs:                            0
% 3.00/1.01  merged_defs_ncl:                        0
% 3.00/1.01  bin_hyper_res:                          0
% 3.00/1.01  prep_cycles:                            4
% 3.00/1.01  pred_elim_time:                         0.019
% 3.00/1.01  splitting_time:                         0.
% 3.00/1.01  sem_filter_time:                        0.
% 3.00/1.01  monotx_time:                            0.001
% 3.00/1.01  subtype_inf_time:                       0.001
% 3.00/1.01  
% 3.00/1.01  ------ Problem properties
% 3.00/1.01  
% 3.00/1.01  clauses:                                32
% 3.00/1.01  conjectures:                            8
% 3.00/1.01  epr:                                    8
% 3.00/1.01  horn:                                   31
% 3.00/1.01  ground:                                 15
% 3.00/1.01  unary:                                  16
% 3.00/1.01  binary:                                 4
% 3.00/1.01  lits:                                   84
% 3.00/1.01  lits_eq:                                16
% 3.00/1.01  fd_pure:                                0
% 3.00/1.01  fd_pseudo:                              0
% 3.00/1.01  fd_cond:                                2
% 3.00/1.01  fd_pseudo_cond:                         3
% 3.00/1.01  ac_symbols:                             0
% 3.00/1.01  
% 3.00/1.01  ------ Propositional Solver
% 3.00/1.01  
% 3.00/1.01  prop_solver_calls:                      26
% 3.00/1.01  prop_fast_solver_calls:                 1422
% 3.00/1.01  smt_solver_calls:                       0
% 3.00/1.01  smt_fast_solver_calls:                  0
% 3.00/1.01  prop_num_of_clauses:                    2791
% 3.00/1.01  prop_preprocess_simplified:             6818
% 3.00/1.01  prop_fo_subsumed:                       55
% 3.00/1.01  prop_solver_time:                       0.
% 3.00/1.01  smt_solver_time:                        0.
% 3.00/1.01  smt_fast_solver_time:                   0.
% 3.00/1.01  prop_fast_solver_time:                  0.
% 3.00/1.01  prop_unsat_core_time:                   0.
% 3.00/1.01  
% 3.00/1.01  ------ QBF
% 3.00/1.01  
% 3.00/1.01  qbf_q_res:                              0
% 3.00/1.01  qbf_num_tautologies:                    0
% 3.00/1.01  qbf_prep_cycles:                        0
% 3.00/1.01  
% 3.00/1.01  ------ BMC1
% 3.00/1.01  
% 3.00/1.01  bmc1_current_bound:                     -1
% 3.00/1.01  bmc1_last_solved_bound:                 -1
% 3.00/1.01  bmc1_unsat_core_size:                   -1
% 3.00/1.01  bmc1_unsat_core_parents_size:           -1
% 3.00/1.01  bmc1_merge_next_fun:                    0
% 3.00/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation
% 3.00/1.01  
% 3.00/1.01  inst_num_of_clauses:                    795
% 3.00/1.01  inst_num_in_passive:                    32
% 3.00/1.01  inst_num_in_active:                     424
% 3.00/1.01  inst_num_in_unprocessed:                339
% 3.00/1.01  inst_num_of_loops:                      430
% 3.00/1.01  inst_num_of_learning_restarts:          0
% 3.00/1.01  inst_num_moves_active_passive:          3
% 3.00/1.01  inst_lit_activity:                      0
% 3.00/1.01  inst_lit_activity_moves:                0
% 3.00/1.01  inst_num_tautologies:                   0
% 3.00/1.01  inst_num_prop_implied:                  0
% 3.00/1.01  inst_num_existing_simplified:           0
% 3.00/1.01  inst_num_eq_res_simplified:             0
% 3.00/1.01  inst_num_child_elim:                    0
% 3.00/1.01  inst_num_of_dismatching_blockings:      133
% 3.00/1.01  inst_num_of_non_proper_insts:           678
% 3.00/1.01  inst_num_of_duplicates:                 0
% 3.00/1.01  inst_inst_num_from_inst_to_res:         0
% 3.00/1.01  inst_dismatching_checking_time:         0.
% 3.00/1.01  
% 3.00/1.01  ------ Resolution
% 3.00/1.01  
% 3.00/1.01  res_num_of_clauses:                     0
% 3.00/1.01  res_num_in_passive:                     0
% 3.00/1.01  res_num_in_active:                      0
% 3.00/1.01  res_num_of_loops:                       171
% 3.00/1.01  res_forward_subset_subsumed:            30
% 3.00/1.01  res_backward_subset_subsumed:           0
% 3.00/1.01  res_forward_subsumed:                   0
% 3.00/1.01  res_backward_subsumed:                  0
% 3.00/1.01  res_forward_subsumption_resolution:     2
% 3.00/1.01  res_backward_subsumption_resolution:    0
% 3.00/1.01  res_clause_to_clause_subsumption:       255
% 3.00/1.01  res_orphan_elimination:                 0
% 3.00/1.01  res_tautology_del:                      68
% 3.00/1.01  res_num_eq_res_simplified:              0
% 3.00/1.01  res_num_sel_changes:                    0
% 3.00/1.01  res_moves_from_active_to_pass:          0
% 3.00/1.01  
% 3.00/1.01  ------ Superposition
% 3.00/1.01  
% 3.00/1.01  sup_time_total:                         0.
% 3.00/1.01  sup_time_generating:                    0.
% 3.00/1.01  sup_time_sim_full:                      0.
% 3.00/1.01  sup_time_sim_immed:                     0.
% 3.00/1.01  
% 3.00/1.01  sup_num_of_clauses:                     60
% 3.00/1.01  sup_num_in_active:                      45
% 3.00/1.01  sup_num_in_passive:                     15
% 3.00/1.01  sup_num_of_loops:                       85
% 3.00/1.01  sup_fw_superposition:                   58
% 3.00/1.01  sup_bw_superposition:                   24
% 3.00/1.01  sup_immediate_simplified:               58
% 3.00/1.01  sup_given_eliminated:                   0
% 3.00/1.01  comparisons_done:                       0
% 3.00/1.01  comparisons_avoided:                    3
% 3.00/1.01  
% 3.00/1.01  ------ Simplifications
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  sim_fw_subset_subsumed:                 9
% 3.00/1.01  sim_bw_subset_subsumed:                 3
% 3.00/1.01  sim_fw_subsumed:                        2
% 3.00/1.01  sim_bw_subsumed:                        1
% 3.00/1.01  sim_fw_subsumption_res:                 0
% 3.00/1.01  sim_bw_subsumption_res:                 0
% 3.00/1.01  sim_tautology_del:                      0
% 3.00/1.01  sim_eq_tautology_del:                   11
% 3.00/1.01  sim_eq_res_simp:                        4
% 3.00/1.01  sim_fw_demodulated:                     2
% 3.00/1.01  sim_bw_demodulated:                     68
% 3.00/1.01  sim_light_normalised:                   20
% 3.00/1.01  sim_joinable_taut:                      0
% 3.00/1.01  sim_joinable_simp:                      0
% 3.00/1.01  sim_ac_normalised:                      0
% 3.00/1.01  sim_smt_subsumption:                    0
% 3.00/1.01  
%------------------------------------------------------------------------------
