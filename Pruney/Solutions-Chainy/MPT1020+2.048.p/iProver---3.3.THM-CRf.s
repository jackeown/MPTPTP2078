%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:14 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_45)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f51,f50])).

fof(f92,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f83,plain,(
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

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f81,plain,(
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

fof(f84,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2053,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2048,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2065,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4187,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2048,c_2065])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_219,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_29])).

cnf(c_220,plain,
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
    inference(renaming,[status(thm)],[c_219])).

cnf(c_2044,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_5079,plain,
    ( k2_funct_1(sK1) = X0
    | k2_relat_1(sK1) != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4187,c_2044])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_41,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_42,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_110,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2067,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3125,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_2067])).

cnf(c_3131,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3125])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_19,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_528,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_529,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_545,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_529,c_11])).

cnf(c_2042,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_4054,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_2042])).

cnf(c_38,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_43,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4502,plain,
    ( k2_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4054,c_41,c_43])).

cnf(c_4504,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4502])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_294,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_295,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_365,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_295])).

cnf(c_3336,plain,
    ( ~ r1_tarski(sK1,X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_5322,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(X0,X1))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_3336])).

cnf(c_5324,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5322])).

cnf(c_6906,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5079,c_41,c_42,c_44,c_110,c_3131,c_4504,c_5324])).

cnf(c_6907,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6906])).

cnf(c_6912,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_6907])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6913,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6912])).

cnf(c_6915,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6912,c_45,c_46,c_48])).

cnf(c_6916,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6915])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2055,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5761,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_2055])).

cnf(c_4556,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_5986,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5761,c_40,c_39,c_38,c_37,c_4556])).

cnf(c_31,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2054,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5989,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5986,c_2054])).

cnf(c_6920,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6916,c_5989])).

cnf(c_48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2137,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2138,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2137])).

cnf(c_7287,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6920,c_48,c_2138])).

cnf(c_2052,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3124,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2052,c_2067])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2071,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5195,plain,
    ( k2_zfmisc_1(sK0,sK0) = sK2
    | r1_tarski(k2_zfmisc_1(sK0,sK0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_2071])).

cnf(c_7303,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK2
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7287,c_5195])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_7329,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7303,c_5])).

cnf(c_2851,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2852,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2851])).

cnf(c_2437,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2879,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_2880,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2879])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4009,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4010,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4009])).

cnf(c_7317,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7287,c_2052])).

cnf(c_7324,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7317,c_5])).

cnf(c_9742,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7329,c_2852,c_2880,c_4010,c_7324])).

cnf(c_7297,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7287,c_5989])).

cnf(c_9746,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9742,c_7297])).

cnf(c_5196,plain,
    ( k2_zfmisc_1(sK0,sK0) = sK1
    | r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3125,c_2071])).

cnf(c_7302,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK1
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7287,c_5196])).

cnf(c_7330,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7302,c_5])).

cnf(c_3620,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3621,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3620])).

cnf(c_2738,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3669,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2738])).

cnf(c_3670,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3669])).

cnf(c_5831,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5832,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5831])).

cnf(c_7318,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7287,c_2048])).

cnf(c_7323,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7318,c_5])).

cnf(c_10046,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7330,c_3621,c_3670,c_5832,c_7323])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2060,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6969,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5986,c_2060])).

cnf(c_10913,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6969,c_41,c_42,c_43,c_44])).

cnf(c_10917,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10913,c_7287,c_10046])).

cnf(c_10918,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10917,c_5])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2063,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5210,plain,
    ( sK2 = X0
    | r2_relset_1(sK0,sK0,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2052,c_2063])).

cnf(c_7307,plain,
    ( sK2 = X0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7287,c_5210])).

cnf(c_7327,plain,
    ( sK2 = X0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7307,c_5])).

cnf(c_11007,plain,
    ( sK2 = X0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7327,c_9742])).

cnf(c_11008,plain,
    ( k1_xboole_0 = X0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11007,c_9742])).

cnf(c_4030,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4031,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4030])).

cnf(c_2069,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5193,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2069,c_2071])).

cnf(c_11012,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11008,c_4031,c_5193])).

cnf(c_11022,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10918,c_11012])).

cnf(c_11978,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9746,c_10046,c_11022])).

cnf(c_2064,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3484,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2052,c_2064])).

cnf(c_7313,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7287,c_3484])).

cnf(c_9747,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9742,c_7313])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11978,c_9747])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.80/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/0.99  
% 3.80/0.99  ------  iProver source info
% 3.80/0.99  
% 3.80/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.80/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/0.99  git: non_committed_changes: false
% 3.80/0.99  git: last_make_outside_of_git: false
% 3.80/0.99  
% 3.80/0.99  ------ 
% 3.80/0.99  
% 3.80/0.99  ------ Input Options
% 3.80/0.99  
% 3.80/0.99  --out_options                           all
% 3.80/0.99  --tptp_safe_out                         true
% 3.80/0.99  --problem_path                          ""
% 3.80/0.99  --include_path                          ""
% 3.80/0.99  --clausifier                            res/vclausify_rel
% 3.80/0.99  --clausifier_options                    ""
% 3.80/0.99  --stdin                                 false
% 3.80/0.99  --stats_out                             all
% 3.80/0.99  
% 3.80/0.99  ------ General Options
% 3.80/0.99  
% 3.80/0.99  --fof                                   false
% 3.80/0.99  --time_out_real                         305.
% 3.80/0.99  --time_out_virtual                      -1.
% 3.80/0.99  --symbol_type_check                     false
% 3.80/0.99  --clausify_out                          false
% 3.80/0.99  --sig_cnt_out                           false
% 3.80/0.99  --trig_cnt_out                          false
% 3.80/0.99  --trig_cnt_out_tolerance                1.
% 3.80/0.99  --trig_cnt_out_sk_spl                   false
% 3.80/0.99  --abstr_cl_out                          false
% 3.80/0.99  
% 3.80/0.99  ------ Global Options
% 3.80/0.99  
% 3.80/0.99  --schedule                              default
% 3.80/0.99  --add_important_lit                     false
% 3.80/0.99  --prop_solver_per_cl                    1000
% 3.80/0.99  --min_unsat_core                        false
% 3.80/0.99  --soft_assumptions                      false
% 3.80/0.99  --soft_lemma_size                       3
% 3.80/0.99  --prop_impl_unit_size                   0
% 3.80/0.99  --prop_impl_unit                        []
% 3.80/0.99  --share_sel_clauses                     true
% 3.80/0.99  --reset_solvers                         false
% 3.80/0.99  --bc_imp_inh                            [conj_cone]
% 3.80/0.99  --conj_cone_tolerance                   3.
% 3.80/0.99  --extra_neg_conj                        none
% 3.80/0.99  --large_theory_mode                     true
% 3.80/0.99  --prolific_symb_bound                   200
% 3.80/0.99  --lt_threshold                          2000
% 3.80/0.99  --clause_weak_htbl                      true
% 3.80/0.99  --gc_record_bc_elim                     false
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing Options
% 3.80/0.99  
% 3.80/0.99  --preprocessing_flag                    true
% 3.80/0.99  --time_out_prep_mult                    0.1
% 3.80/0.99  --splitting_mode                        input
% 3.80/0.99  --splitting_grd                         true
% 3.80/0.99  --splitting_cvd                         false
% 3.80/0.99  --splitting_cvd_svl                     false
% 3.80/0.99  --splitting_nvd                         32
% 3.80/0.99  --sub_typing                            true
% 3.80/0.99  --prep_gs_sim                           true
% 3.80/0.99  --prep_unflatten                        true
% 3.80/0.99  --prep_res_sim                          true
% 3.80/0.99  --prep_upred                            true
% 3.80/0.99  --prep_sem_filter                       exhaustive
% 3.80/0.99  --prep_sem_filter_out                   false
% 3.80/0.99  --pred_elim                             true
% 3.80/0.99  --res_sim_input                         true
% 3.80/0.99  --eq_ax_congr_red                       true
% 3.80/0.99  --pure_diseq_elim                       true
% 3.80/0.99  --brand_transform                       false
% 3.80/0.99  --non_eq_to_eq                          false
% 3.80/0.99  --prep_def_merge                        true
% 3.80/0.99  --prep_def_merge_prop_impl              false
% 3.80/0.99  --prep_def_merge_mbd                    true
% 3.80/0.99  --prep_def_merge_tr_red                 false
% 3.80/0.99  --prep_def_merge_tr_cl                  false
% 3.80/0.99  --smt_preprocessing                     true
% 3.80/0.99  --smt_ac_axioms                         fast
% 3.80/0.99  --preprocessed_out                      false
% 3.80/0.99  --preprocessed_stats                    false
% 3.80/0.99  
% 3.80/0.99  ------ Abstraction refinement Options
% 3.80/0.99  
% 3.80/0.99  --abstr_ref                             []
% 3.80/0.99  --abstr_ref_prep                        false
% 3.80/0.99  --abstr_ref_until_sat                   false
% 3.80/0.99  --abstr_ref_sig_restrict                funpre
% 3.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.99  --abstr_ref_under                       []
% 3.80/0.99  
% 3.80/0.99  ------ SAT Options
% 3.80/0.99  
% 3.80/0.99  --sat_mode                              false
% 3.80/0.99  --sat_fm_restart_options                ""
% 3.80/0.99  --sat_gr_def                            false
% 3.80/0.99  --sat_epr_types                         true
% 3.80/0.99  --sat_non_cyclic_types                  false
% 3.80/0.99  --sat_finite_models                     false
% 3.80/0.99  --sat_fm_lemmas                         false
% 3.80/0.99  --sat_fm_prep                           false
% 3.80/0.99  --sat_fm_uc_incr                        true
% 3.80/0.99  --sat_out_model                         small
% 3.80/0.99  --sat_out_clauses                       false
% 3.80/0.99  
% 3.80/0.99  ------ QBF Options
% 3.80/0.99  
% 3.80/0.99  --qbf_mode                              false
% 3.80/0.99  --qbf_elim_univ                         false
% 3.80/0.99  --qbf_dom_inst                          none
% 3.80/0.99  --qbf_dom_pre_inst                      false
% 3.80/0.99  --qbf_sk_in                             false
% 3.80/0.99  --qbf_pred_elim                         true
% 3.80/0.99  --qbf_split                             512
% 3.80/0.99  
% 3.80/0.99  ------ BMC1 Options
% 3.80/0.99  
% 3.80/0.99  --bmc1_incremental                      false
% 3.80/0.99  --bmc1_axioms                           reachable_all
% 3.80/0.99  --bmc1_min_bound                        0
% 3.80/0.99  --bmc1_max_bound                        -1
% 3.80/0.99  --bmc1_max_bound_default                -1
% 3.80/0.99  --bmc1_symbol_reachability              true
% 3.80/0.99  --bmc1_property_lemmas                  false
% 3.80/0.99  --bmc1_k_induction                      false
% 3.80/0.99  --bmc1_non_equiv_states                 false
% 3.80/0.99  --bmc1_deadlock                         false
% 3.80/0.99  --bmc1_ucm                              false
% 3.80/0.99  --bmc1_add_unsat_core                   none
% 3.80/0.99  --bmc1_unsat_core_children              false
% 3.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.99  --bmc1_out_stat                         full
% 3.80/0.99  --bmc1_ground_init                      false
% 3.80/0.99  --bmc1_pre_inst_next_state              false
% 3.80/0.99  --bmc1_pre_inst_state                   false
% 3.80/0.99  --bmc1_pre_inst_reach_state             false
% 3.80/0.99  --bmc1_out_unsat_core                   false
% 3.80/0.99  --bmc1_aig_witness_out                  false
% 3.80/0.99  --bmc1_verbose                          false
% 3.80/0.99  --bmc1_dump_clauses_tptp                false
% 3.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.99  --bmc1_dump_file                        -
% 3.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.99  --bmc1_ucm_extend_mode                  1
% 3.80/0.99  --bmc1_ucm_init_mode                    2
% 3.80/0.99  --bmc1_ucm_cone_mode                    none
% 3.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.99  --bmc1_ucm_relax_model                  4
% 3.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.99  --bmc1_ucm_layered_model                none
% 3.80/0.99  --bmc1_ucm_max_lemma_size               10
% 3.80/0.99  
% 3.80/0.99  ------ AIG Options
% 3.80/0.99  
% 3.80/0.99  --aig_mode                              false
% 3.80/0.99  
% 3.80/0.99  ------ Instantiation Options
% 3.80/0.99  
% 3.80/0.99  --instantiation_flag                    true
% 3.80/0.99  --inst_sos_flag                         true
% 3.80/0.99  --inst_sos_phase                        true
% 3.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel_side                     num_symb
% 3.80/0.99  --inst_solver_per_active                1400
% 3.80/0.99  --inst_solver_calls_frac                1.
% 3.80/0.99  --inst_passive_queue_type               priority_queues
% 3.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.99  --inst_passive_queues_freq              [25;2]
% 3.80/0.99  --inst_dismatching                      true
% 3.80/0.99  --inst_eager_unprocessed_to_passive     true
% 3.80/0.99  --inst_prop_sim_given                   true
% 3.80/0.99  --inst_prop_sim_new                     false
% 3.80/0.99  --inst_subs_new                         false
% 3.80/0.99  --inst_eq_res_simp                      false
% 3.80/0.99  --inst_subs_given                       false
% 3.80/0.99  --inst_orphan_elimination               true
% 3.80/0.99  --inst_learning_loop_flag               true
% 3.80/0.99  --inst_learning_start                   3000
% 3.80/0.99  --inst_learning_factor                  2
% 3.80/0.99  --inst_start_prop_sim_after_learn       3
% 3.80/0.99  --inst_sel_renew                        solver
% 3.80/0.99  --inst_lit_activity_flag                true
% 3.80/0.99  --inst_restr_to_given                   false
% 3.80/0.99  --inst_activity_threshold               500
% 3.80/0.99  --inst_out_proof                        true
% 3.80/0.99  
% 3.80/0.99  ------ Resolution Options
% 3.80/0.99  
% 3.80/0.99  --resolution_flag                       true
% 3.80/0.99  --res_lit_sel                           adaptive
% 3.80/0.99  --res_lit_sel_side                      none
% 3.80/0.99  --res_ordering                          kbo
% 3.80/0.99  --res_to_prop_solver                    active
% 3.80/0.99  --res_prop_simpl_new                    false
% 3.80/0.99  --res_prop_simpl_given                  true
% 3.80/0.99  --res_passive_queue_type                priority_queues
% 3.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.99  --res_passive_queues_freq               [15;5]
% 3.80/0.99  --res_forward_subs                      full
% 3.80/0.99  --res_backward_subs                     full
% 3.80/0.99  --res_forward_subs_resolution           true
% 3.80/0.99  --res_backward_subs_resolution          true
% 3.80/0.99  --res_orphan_elimination                true
% 3.80/0.99  --res_time_limit                        2.
% 3.80/0.99  --res_out_proof                         true
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Options
% 3.80/0.99  
% 3.80/0.99  --superposition_flag                    true
% 3.80/0.99  --sup_passive_queue_type                priority_queues
% 3.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.99  --demod_completeness_check              fast
% 3.80/0.99  --demod_use_ground                      true
% 3.80/0.99  --sup_to_prop_solver                    passive
% 3.80/0.99  --sup_prop_simpl_new                    true
% 3.80/0.99  --sup_prop_simpl_given                  true
% 3.80/0.99  --sup_fun_splitting                     true
% 3.80/0.99  --sup_smt_interval                      50000
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Simplification Setup
% 3.80/0.99  
% 3.80/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/0.99  --sup_immed_triv                        [TrivRules]
% 3.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_bw_main                     []
% 3.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_input_bw                          []
% 3.80/0.99  
% 3.80/0.99  ------ Combination Options
% 3.80/0.99  
% 3.80/0.99  --comb_res_mult                         3
% 3.80/0.99  --comb_sup_mult                         2
% 3.80/0.99  --comb_inst_mult                        10
% 3.80/0.99  
% 3.80/0.99  ------ Debug Options
% 3.80/0.99  
% 3.80/0.99  --dbg_backtrace                         false
% 3.80/0.99  --dbg_dump_prop_clauses                 false
% 3.80/0.99  --dbg_dump_prop_clauses_file            -
% 3.80/0.99  --dbg_out_stat                          false
% 3.80/0.99  ------ Parsing...
% 3.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.80/0.99  ------ Proving...
% 3.80/0.99  ------ Problem Properties 
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  clauses                                 34
% 3.80/0.99  conjectures                             10
% 3.80/0.99  EPR                                     10
% 3.80/0.99  Horn                                    32
% 3.80/0.99  unary                                   16
% 3.80/0.99  binary                                  4
% 3.80/0.99  lits                                    97
% 3.80/0.99  lits eq                                 15
% 3.80/0.99  fd_pure                                 0
% 3.80/0.99  fd_pseudo                               0
% 3.80/0.99  fd_cond                                 1
% 3.80/0.99  fd_pseudo_cond                          5
% 3.80/0.99  AC symbols                              0
% 3.80/0.99  
% 3.80/0.99  ------ Schedule dynamic 5 is on 
% 3.80/0.99  
% 3.80/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  ------ 
% 3.80/0.99  Current options:
% 3.80/0.99  ------ 
% 3.80/0.99  
% 3.80/0.99  ------ Input Options
% 3.80/0.99  
% 3.80/0.99  --out_options                           all
% 3.80/0.99  --tptp_safe_out                         true
% 3.80/0.99  --problem_path                          ""
% 3.80/0.99  --include_path                          ""
% 3.80/0.99  --clausifier                            res/vclausify_rel
% 3.80/0.99  --clausifier_options                    ""
% 3.80/0.99  --stdin                                 false
% 3.80/0.99  --stats_out                             all
% 3.80/0.99  
% 3.80/0.99  ------ General Options
% 3.80/0.99  
% 3.80/0.99  --fof                                   false
% 3.80/0.99  --time_out_real                         305.
% 3.80/0.99  --time_out_virtual                      -1.
% 3.80/0.99  --symbol_type_check                     false
% 3.80/0.99  --clausify_out                          false
% 3.80/0.99  --sig_cnt_out                           false
% 3.80/0.99  --trig_cnt_out                          false
% 3.80/0.99  --trig_cnt_out_tolerance                1.
% 3.80/0.99  --trig_cnt_out_sk_spl                   false
% 3.80/0.99  --abstr_cl_out                          false
% 3.80/0.99  
% 3.80/0.99  ------ Global Options
% 3.80/0.99  
% 3.80/0.99  --schedule                              default
% 3.80/0.99  --add_important_lit                     false
% 3.80/0.99  --prop_solver_per_cl                    1000
% 3.80/0.99  --min_unsat_core                        false
% 3.80/0.99  --soft_assumptions                      false
% 3.80/0.99  --soft_lemma_size                       3
% 3.80/0.99  --prop_impl_unit_size                   0
% 3.80/0.99  --prop_impl_unit                        []
% 3.80/0.99  --share_sel_clauses                     true
% 3.80/0.99  --reset_solvers                         false
% 3.80/0.99  --bc_imp_inh                            [conj_cone]
% 3.80/0.99  --conj_cone_tolerance                   3.
% 3.80/0.99  --extra_neg_conj                        none
% 3.80/0.99  --large_theory_mode                     true
% 3.80/0.99  --prolific_symb_bound                   200
% 3.80/0.99  --lt_threshold                          2000
% 3.80/0.99  --clause_weak_htbl                      true
% 3.80/0.99  --gc_record_bc_elim                     false
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing Options
% 3.80/0.99  
% 3.80/0.99  --preprocessing_flag                    true
% 3.80/0.99  --time_out_prep_mult                    0.1
% 3.80/0.99  --splitting_mode                        input
% 3.80/0.99  --splitting_grd                         true
% 3.80/0.99  --splitting_cvd                         false
% 3.80/0.99  --splitting_cvd_svl                     false
% 3.80/0.99  --splitting_nvd                         32
% 3.80/0.99  --sub_typing                            true
% 3.80/0.99  --prep_gs_sim                           true
% 3.80/0.99  --prep_unflatten                        true
% 3.80/0.99  --prep_res_sim                          true
% 3.80/0.99  --prep_upred                            true
% 3.80/0.99  --prep_sem_filter                       exhaustive
% 3.80/0.99  --prep_sem_filter_out                   false
% 3.80/0.99  --pred_elim                             true
% 3.80/0.99  --res_sim_input                         true
% 3.80/0.99  --eq_ax_congr_red                       true
% 3.80/0.99  --pure_diseq_elim                       true
% 3.80/0.99  --brand_transform                       false
% 3.80/0.99  --non_eq_to_eq                          false
% 3.80/0.99  --prep_def_merge                        true
% 3.80/0.99  --prep_def_merge_prop_impl              false
% 3.80/0.99  --prep_def_merge_mbd                    true
% 3.80/0.99  --prep_def_merge_tr_red                 false
% 3.80/0.99  --prep_def_merge_tr_cl                  false
% 3.80/0.99  --smt_preprocessing                     true
% 3.80/0.99  --smt_ac_axioms                         fast
% 3.80/0.99  --preprocessed_out                      false
% 3.80/0.99  --preprocessed_stats                    false
% 3.80/0.99  
% 3.80/0.99  ------ Abstraction refinement Options
% 3.80/0.99  
% 3.80/0.99  --abstr_ref                             []
% 3.80/0.99  --abstr_ref_prep                        false
% 3.80/0.99  --abstr_ref_until_sat                   false
% 3.80/0.99  --abstr_ref_sig_restrict                funpre
% 3.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.99  --abstr_ref_under                       []
% 3.80/0.99  
% 3.80/0.99  ------ SAT Options
% 3.80/0.99  
% 3.80/0.99  --sat_mode                              false
% 3.80/0.99  --sat_fm_restart_options                ""
% 3.80/0.99  --sat_gr_def                            false
% 3.80/0.99  --sat_epr_types                         true
% 3.80/0.99  --sat_non_cyclic_types                  false
% 3.80/0.99  --sat_finite_models                     false
% 3.80/0.99  --sat_fm_lemmas                         false
% 3.80/0.99  --sat_fm_prep                           false
% 3.80/0.99  --sat_fm_uc_incr                        true
% 3.80/0.99  --sat_out_model                         small
% 3.80/0.99  --sat_out_clauses                       false
% 3.80/0.99  
% 3.80/0.99  ------ QBF Options
% 3.80/0.99  
% 3.80/0.99  --qbf_mode                              false
% 3.80/0.99  --qbf_elim_univ                         false
% 3.80/0.99  --qbf_dom_inst                          none
% 3.80/0.99  --qbf_dom_pre_inst                      false
% 3.80/0.99  --qbf_sk_in                             false
% 3.80/0.99  --qbf_pred_elim                         true
% 3.80/0.99  --qbf_split                             512
% 3.80/0.99  
% 3.80/0.99  ------ BMC1 Options
% 3.80/0.99  
% 3.80/0.99  --bmc1_incremental                      false
% 3.80/0.99  --bmc1_axioms                           reachable_all
% 3.80/0.99  --bmc1_min_bound                        0
% 3.80/0.99  --bmc1_max_bound                        -1
% 3.80/0.99  --bmc1_max_bound_default                -1
% 3.80/0.99  --bmc1_symbol_reachability              true
% 3.80/0.99  --bmc1_property_lemmas                  false
% 3.80/0.99  --bmc1_k_induction                      false
% 3.80/0.99  --bmc1_non_equiv_states                 false
% 3.80/0.99  --bmc1_deadlock                         false
% 3.80/0.99  --bmc1_ucm                              false
% 3.80/0.99  --bmc1_add_unsat_core                   none
% 3.80/0.99  --bmc1_unsat_core_children              false
% 3.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.99  --bmc1_out_stat                         full
% 3.80/0.99  --bmc1_ground_init                      false
% 3.80/0.99  --bmc1_pre_inst_next_state              false
% 3.80/0.99  --bmc1_pre_inst_state                   false
% 3.80/0.99  --bmc1_pre_inst_reach_state             false
% 3.80/0.99  --bmc1_out_unsat_core                   false
% 3.80/0.99  --bmc1_aig_witness_out                  false
% 3.80/0.99  --bmc1_verbose                          false
% 3.80/0.99  --bmc1_dump_clauses_tptp                false
% 3.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.99  --bmc1_dump_file                        -
% 3.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.99  --bmc1_ucm_extend_mode                  1
% 3.80/0.99  --bmc1_ucm_init_mode                    2
% 3.80/0.99  --bmc1_ucm_cone_mode                    none
% 3.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.99  --bmc1_ucm_relax_model                  4
% 3.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.99  --bmc1_ucm_layered_model                none
% 3.80/0.99  --bmc1_ucm_max_lemma_size               10
% 3.80/0.99  
% 3.80/0.99  ------ AIG Options
% 3.80/0.99  
% 3.80/0.99  --aig_mode                              false
% 3.80/0.99  
% 3.80/0.99  ------ Instantiation Options
% 3.80/0.99  
% 3.80/0.99  --instantiation_flag                    true
% 3.80/0.99  --inst_sos_flag                         true
% 3.80/0.99  --inst_sos_phase                        true
% 3.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel_side                     none
% 3.80/0.99  --inst_solver_per_active                1400
% 3.80/0.99  --inst_solver_calls_frac                1.
% 3.80/0.99  --inst_passive_queue_type               priority_queues
% 3.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.99  --inst_passive_queues_freq              [25;2]
% 3.80/0.99  --inst_dismatching                      true
% 3.80/0.99  --inst_eager_unprocessed_to_passive     true
% 3.80/0.99  --inst_prop_sim_given                   true
% 3.80/0.99  --inst_prop_sim_new                     false
% 3.80/0.99  --inst_subs_new                         false
% 3.80/0.99  --inst_eq_res_simp                      false
% 3.80/0.99  --inst_subs_given                       false
% 3.80/0.99  --inst_orphan_elimination               true
% 3.80/0.99  --inst_learning_loop_flag               true
% 3.80/0.99  --inst_learning_start                   3000
% 3.80/0.99  --inst_learning_factor                  2
% 3.80/0.99  --inst_start_prop_sim_after_learn       3
% 3.80/0.99  --inst_sel_renew                        solver
% 3.80/0.99  --inst_lit_activity_flag                true
% 3.80/0.99  --inst_restr_to_given                   false
% 3.80/0.99  --inst_activity_threshold               500
% 3.80/0.99  --inst_out_proof                        true
% 3.80/0.99  
% 3.80/0.99  ------ Resolution Options
% 3.80/0.99  
% 3.80/0.99  --resolution_flag                       false
% 3.80/0.99  --res_lit_sel                           adaptive
% 3.80/0.99  --res_lit_sel_side                      none
% 3.80/0.99  --res_ordering                          kbo
% 3.80/0.99  --res_to_prop_solver                    active
% 3.80/0.99  --res_prop_simpl_new                    false
% 3.80/0.99  --res_prop_simpl_given                  true
% 3.80/0.99  --res_passive_queue_type                priority_queues
% 3.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.99  --res_passive_queues_freq               [15;5]
% 3.80/0.99  --res_forward_subs                      full
% 3.80/0.99  --res_backward_subs                     full
% 3.80/0.99  --res_forward_subs_resolution           true
% 3.80/0.99  --res_backward_subs_resolution          true
% 3.80/0.99  --res_orphan_elimination                true
% 3.80/0.99  --res_time_limit                        2.
% 3.80/0.99  --res_out_proof                         true
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Options
% 3.80/0.99  
% 3.80/0.99  --superposition_flag                    true
% 3.80/0.99  --sup_passive_queue_type                priority_queues
% 3.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.99  --demod_completeness_check              fast
% 3.80/0.99  --demod_use_ground                      true
% 3.80/0.99  --sup_to_prop_solver                    passive
% 3.80/0.99  --sup_prop_simpl_new                    true
% 3.80/0.99  --sup_prop_simpl_given                  true
% 3.80/0.99  --sup_fun_splitting                     true
% 3.80/0.99  --sup_smt_interval                      50000
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Simplification Setup
% 3.80/0.99  
% 3.80/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/0.99  --sup_immed_triv                        [TrivRules]
% 3.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_bw_main                     []
% 3.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_input_bw                          []
% 3.80/0.99  
% 3.80/0.99  ------ Combination Options
% 3.80/0.99  
% 3.80/0.99  --comb_res_mult                         3
% 3.80/0.99  --comb_sup_mult                         2
% 3.80/0.99  --comb_inst_mult                        10
% 3.80/0.99  
% 3.80/0.99  ------ Debug Options
% 3.80/0.99  
% 3.80/0.99  --dbg_backtrace                         false
% 3.80/0.99  --dbg_dump_prop_clauses                 false
% 3.80/0.99  --dbg_dump_prop_clauses_file            -
% 3.80/0.99  --dbg_out_stat                          false
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  ------ Proving...
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  % SZS status Theorem for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  fof(f18,conjecture,(
% 3.80/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f19,negated_conjecture,(
% 3.80/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.80/0.99    inference(negated_conjecture,[],[f18])).
% 3.80/0.99  
% 3.80/0.99  fof(f41,plain,(
% 3.80/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.80/0.99    inference(ennf_transformation,[],[f19])).
% 3.80/0.99  
% 3.80/0.99  fof(f42,plain,(
% 3.80/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.80/0.99    inference(flattening,[],[f41])).
% 3.80/0.99  
% 3.80/0.99  fof(f51,plain,(
% 3.80/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f50,plain,(
% 3.80/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f52,plain,(
% 3.80/0.99    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f51,f50])).
% 3.80/0.99  
% 3.80/0.99  fof(f92,plain,(
% 3.80/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f87,plain,(
% 3.80/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f8,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f24,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.99    inference(ennf_transformation,[],[f8])).
% 3.80/0.99  
% 3.80/0.99  fof(f65,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f24])).
% 3.80/0.99  
% 3.80/0.99  fof(f17,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f39,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.80/0.99    inference(ennf_transformation,[],[f17])).
% 3.80/0.99  
% 3.80/0.99  fof(f40,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.80/0.99    inference(flattening,[],[f39])).
% 3.80/0.99  
% 3.80/0.99  fof(f83,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f40])).
% 3.80/0.99  
% 3.80/0.99  fof(f16,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f37,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.80/0.99    inference(ennf_transformation,[],[f16])).
% 3.80/0.99  
% 3.80/0.99  fof(f38,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.80/0.99    inference(flattening,[],[f37])).
% 3.80/0.99  
% 3.80/0.99  fof(f81,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f84,plain,(
% 3.80/0.99    v1_funct_1(sK1)),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f85,plain,(
% 3.80/0.99    v1_funct_2(sK1,sK0,sK0)),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f6,axiom,(
% 3.80/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f63,plain,(
% 3.80/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f6])).
% 3.80/0.99  
% 3.80/0.99  fof(f4,axiom,(
% 3.80/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f47,plain,(
% 3.80/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.80/0.99    inference(nnf_transformation,[],[f4])).
% 3.80/0.99  
% 3.80/0.99  fof(f60,plain,(
% 3.80/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f47])).
% 3.80/0.99  
% 3.80/0.99  fof(f10,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f27,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.99    inference(ennf_transformation,[],[f10])).
% 3.80/0.99  
% 3.80/0.99  fof(f28,plain,(
% 3.80/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.99    inference(flattening,[],[f27])).
% 3.80/0.99  
% 3.80/0.99  fof(f70,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f28])).
% 3.80/0.99  
% 3.80/0.99  fof(f11,axiom,(
% 3.80/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f29,plain,(
% 3.80/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.80/0.99    inference(ennf_transformation,[],[f11])).
% 3.80/0.99  
% 3.80/0.99  fof(f30,plain,(
% 3.80/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(flattening,[],[f29])).
% 3.80/0.99  
% 3.80/0.99  fof(f49,plain,(
% 3.80/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(nnf_transformation,[],[f30])).
% 3.80/0.99  
% 3.80/0.99  fof(f71,plain,(
% 3.80/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f49])).
% 3.80/0.99  
% 3.80/0.99  fof(f7,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f21,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.80/0.99    inference(pure_predicate_removal,[],[f7])).
% 3.80/0.99  
% 3.80/0.99  fof(f23,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.99    inference(ennf_transformation,[],[f21])).
% 3.80/0.99  
% 3.80/0.99  fof(f64,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f23])).
% 3.80/0.99  
% 3.80/0.99  fof(f86,plain,(
% 3.80/0.99    v3_funct_2(sK1,sK0,sK0)),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f5,axiom,(
% 3.80/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f22,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f5])).
% 3.80/0.99  
% 3.80/0.99  fof(f62,plain,(
% 3.80/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f22])).
% 3.80/0.99  
% 3.80/0.99  fof(f61,plain,(
% 3.80/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f47])).
% 3.80/0.99  
% 3.80/0.99  fof(f88,plain,(
% 3.80/0.99    v1_funct_1(sK2)),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f89,plain,(
% 3.80/0.99    v1_funct_2(sK2,sK0,sK0)),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f91,plain,(
% 3.80/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f15,axiom,(
% 3.80/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f35,plain,(
% 3.80/0.99    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.80/0.99    inference(ennf_transformation,[],[f15])).
% 3.80/0.99  
% 3.80/0.99  fof(f36,plain,(
% 3.80/0.99    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.80/0.99    inference(flattening,[],[f35])).
% 3.80/0.99  
% 3.80/0.99  fof(f80,plain,(
% 3.80/0.99    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f36])).
% 3.80/0.99  
% 3.80/0.99  fof(f93,plain,(
% 3.80/0.99    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f9,axiom,(
% 3.80/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f25,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.80/0.99    inference(ennf_transformation,[],[f9])).
% 3.80/0.99  
% 3.80/0.99  fof(f26,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.99    inference(flattening,[],[f25])).
% 3.80/0.99  
% 3.80/0.99  fof(f48,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.99    inference(nnf_transformation,[],[f26])).
% 3.80/0.99  
% 3.80/0.99  fof(f67,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f48])).
% 3.80/0.99  
% 3.80/0.99  fof(f98,plain,(
% 3.80/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.99    inference(equality_resolution,[],[f67])).
% 3.80/0.99  
% 3.80/0.99  fof(f1,axiom,(
% 3.80/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f43,plain,(
% 3.80/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.99    inference(nnf_transformation,[],[f1])).
% 3.80/0.99  
% 3.80/0.99  fof(f44,plain,(
% 3.80/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.99    inference(flattening,[],[f43])).
% 3.80/0.99  
% 3.80/0.99  fof(f55,plain,(
% 3.80/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f44])).
% 3.80/0.99  
% 3.80/0.99  fof(f3,axiom,(
% 3.80/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f45,plain,(
% 3.80/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.80/0.99    inference(nnf_transformation,[],[f3])).
% 3.80/0.99  
% 3.80/0.99  fof(f46,plain,(
% 3.80/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.80/0.99    inference(flattening,[],[f45])).
% 3.80/0.99  
% 3.80/0.99  fof(f58,plain,(
% 3.80/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.80/0.99    inference(cnf_transformation,[],[f46])).
% 3.80/0.99  
% 3.80/0.99  fof(f97,plain,(
% 3.80/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.80/0.99    inference(equality_resolution,[],[f58])).
% 3.80/0.99  
% 3.80/0.99  fof(f2,axiom,(
% 3.80/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f56,plain,(
% 3.80/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f2])).
% 3.80/0.99  
% 3.80/0.99  fof(f13,axiom,(
% 3.80/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f33,plain,(
% 3.80/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.80/0.99    inference(ennf_transformation,[],[f13])).
% 3.80/0.99  
% 3.80/0.99  fof(f34,plain,(
% 3.80/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.80/0.99    inference(flattening,[],[f33])).
% 3.80/0.99  
% 3.80/0.99  fof(f78,plain,(
% 3.80/0.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f34])).
% 3.80/0.99  
% 3.80/0.99  fof(f66,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f48])).
% 3.80/0.99  
% 3.80/0.99  cnf(c_32,negated_conjecture,
% 3.80/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2053,plain,
% 3.80/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_37,negated_conjecture,
% 3.80/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2048,plain,
% 3.80/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_12,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2065,plain,
% 3.80/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4187,plain,
% 3.80/0.99      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2048,c_2065]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_30,plain,
% 3.80/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.80/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.80/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.80/0.99      | ~ v2_funct_1(X2)
% 3.80/0.99      | ~ v1_funct_1(X2)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.80/0.99      | k2_funct_1(X2) = X3
% 3.80/0.99      | k1_xboole_0 = X1
% 3.80/0.99      | k1_xboole_0 = X0 ),
% 3.80/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_29,plain,
% 3.80/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.80/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.80/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.80/0.99      | v2_funct_1(X2)
% 3.80/0.99      | ~ v1_funct_1(X2)
% 3.80/0.99      | ~ v1_funct_1(X3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_219,plain,
% 3.80/0.99      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.80/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.80/0.99      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.80/0.99      | ~ v1_funct_1(X2)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.80/0.99      | k2_funct_1(X2) = X3
% 3.80/0.99      | k1_xboole_0 = X1
% 3.80/0.99      | k1_xboole_0 = X0 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_30,c_29]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_220,plain,
% 3.80/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.80/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.80/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.80/0.99      | ~ v1_funct_1(X2)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.80/0.99      | k2_funct_1(X2) = X3
% 3.80/0.99      | k1_xboole_0 = X1
% 3.80/0.99      | k1_xboole_0 = X0 ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_219]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2044,plain,
% 3.80/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.80/0.99      | k2_funct_1(X2) = X3
% 3.80/0.99      | k1_xboole_0 = X1
% 3.80/0.99      | k1_xboole_0 = X0
% 3.80/0.99      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.80/0.99      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.80/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.80/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.80/0.99      | v1_funct_1(X2) != iProver_top
% 3.80/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5079,plain,
% 3.80/0.99      ( k2_funct_1(sK1) = X0
% 3.80/0.99      | k2_relat_1(sK1) != sK0
% 3.80/0.99      | sK0 = k1_xboole_0
% 3.80/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.80/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.80/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.80/0.99      | v1_funct_1(X0) != iProver_top
% 3.80/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_4187,c_2044]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_40,negated_conjecture,
% 3.80/0.99      ( v1_funct_1(sK1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_41,plain,
% 3.80/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_39,negated_conjecture,
% 3.80/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_42,plain,
% 3.80/0.99      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_44,plain,
% 3.80/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10,plain,
% 3.80/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_110,plain,
% 3.80/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_8,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2067,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.80/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3125,plain,
% 3.80/0.99      ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2048,c_2067]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3131,plain,
% 3.80/0.99      ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
% 3.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3125]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_15,plain,
% 3.80/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.80/0.99      | v2_funct_2(X0,X2)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_19,plain,
% 3.80/0.99      ( ~ v2_funct_2(X0,X1)
% 3.80/0.99      | ~ v5_relat_1(X0,X1)
% 3.80/0.99      | ~ v1_relat_1(X0)
% 3.80/0.99      | k2_relat_1(X0) = X1 ),
% 3.80/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_528,plain,
% 3.80/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v5_relat_1(X3,X4)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_relat_1(X3)
% 3.80/0.99      | X3 != X0
% 3.80/0.99      | X4 != X2
% 3.80/0.99      | k2_relat_1(X3) = X4 ),
% 3.80/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_529,plain,
% 3.80/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v5_relat_1(X0,X2)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_relat_1(X0)
% 3.80/0.99      | k2_relat_1(X0) = X2 ),
% 3.80/0.99      inference(unflattening,[status(thm)],[c_528]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11,plain,
% 3.80/0.99      ( v5_relat_1(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_545,plain,
% 3.80/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_relat_1(X0)
% 3.80/0.99      | k2_relat_1(X0) = X2 ),
% 3.80/0.99      inference(forward_subsumption_resolution,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_529,c_11]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2042,plain,
% 3.80/0.99      ( k2_relat_1(X0) = X1
% 3.80/0.99      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.80/0.99      | v1_funct_1(X0) != iProver_top
% 3.80/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4054,plain,
% 3.80/0.99      ( k2_relat_1(sK1) = sK0
% 3.80/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.80/0.99      | v1_funct_1(sK1) != iProver_top
% 3.80/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2048,c_2042]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_38,negated_conjecture,
% 3.80/0.99      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_43,plain,
% 3.80/0.99      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4502,plain,
% 3.80/0.99      ( k2_relat_1(sK1) = sK0 | v1_relat_1(sK1) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_4054,c_41,c_43]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4504,plain,
% 3.80/0.99      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 3.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4502]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.80/0.99      | ~ v1_relat_1(X1)
% 3.80/0.99      | v1_relat_1(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_294,plain,
% 3.80/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.80/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_295,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_294]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_365,plain,
% 3.80/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.80/0.99      inference(bin_hyper_res,[status(thm)],[c_9,c_295]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3336,plain,
% 3.80/0.99      ( ~ r1_tarski(sK1,X0) | ~ v1_relat_1(X0) | v1_relat_1(sK1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_365]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5322,plain,
% 3.80/0.99      ( ~ r1_tarski(sK1,k2_zfmisc_1(X0,X1))
% 3.80/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.80/0.99      | v1_relat_1(sK1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_3336]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5324,plain,
% 3.80/0.99      ( ~ r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
% 3.80/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.80/0.99      | v1_relat_1(sK1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_5322]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6906,plain,
% 3.80/0.99      ( v1_funct_1(X0) != iProver_top
% 3.80/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.80/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.80/0.99      | sK0 = k1_xboole_0
% 3.80/0.99      | k2_funct_1(sK1) = X0
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_5079,c_41,c_42,c_44,c_110,c_3131,c_4504,c_5324]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6907,plain,
% 3.80/0.99      ( k2_funct_1(sK1) = X0
% 3.80/0.99      | sK0 = k1_xboole_0
% 3.80/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.80/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.80/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_6906]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6912,plain,
% 3.80/0.99      ( k2_funct_1(sK1) = sK2
% 3.80/0.99      | sK0 = k1_xboole_0
% 3.80/0.99      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.80/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2053,c_6907]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_36,negated_conjecture,
% 3.80/0.99      ( v1_funct_1(sK2) ),
% 3.80/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_35,negated_conjecture,
% 3.80/0.99      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_33,negated_conjecture,
% 3.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6913,plain,
% 3.80/0.99      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.80/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.80/0.99      | ~ v1_funct_1(sK2)
% 3.80/0.99      | k2_funct_1(sK1) = sK2
% 3.80/0.99      | sK0 = k1_xboole_0 ),
% 3.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6912]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6915,plain,
% 3.80/0.99      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_6912,c_45,c_46,c_48]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6916,plain,
% 3.80/0.99      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_6915]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_27,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.80/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2055,plain,
% 3.80/0.99      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.80/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.80/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.80/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5761,plain,
% 3.80/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.80/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.80/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.80/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2048,c_2055]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4556,plain,
% 3.80/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.80/0.99      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.80/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.80/0.99      | ~ v1_funct_1(sK1)
% 3.80/0.99      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5986,plain,
% 3.80/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_5761,c_40,c_39,c_38,c_37,c_4556]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_31,negated_conjecture,
% 3.80/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2054,plain,
% 3.80/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5989,plain,
% 3.80/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_5986,c_2054]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6920,plain,
% 3.80/0.99      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_6916,c_5989]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_48,plain,
% 3.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_13,plain,
% 3.80/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2137,plain,
% 3.80/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.80/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2138,plain,
% 3.80/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_2137]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7287,plain,
% 3.80/0.99      ( sK0 = k1_xboole_0 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_6920,c_48,c_2138]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2052,plain,
% 3.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3124,plain,
% 3.80/0.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2052,c_2067]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_0,plain,
% 3.80/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.80/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2071,plain,
% 3.80/0.99      ( X0 = X1
% 3.80/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.80/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5195,plain,
% 3.80/0.99      ( k2_zfmisc_1(sK0,sK0) = sK2
% 3.80/0.99      | r1_tarski(k2_zfmisc_1(sK0,sK0),sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3124,c_2071]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7303,plain,
% 3.80/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK2
% 3.80/0.99      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7287,c_5195]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5,plain,
% 3.80/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.80/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7329,plain,
% 3.80/0.99      ( sK2 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7303,c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2851,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
% 3.80/0.99      | r1_tarski(sK2,k1_xboole_0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2852,plain,
% 3.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.80/0.99      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_2851]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2437,plain,
% 3.80/0.99      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2879,plain,
% 3.80/0.99      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.80/0.99      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.80/0.99      | sK2 = k1_xboole_0 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_2437]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2880,plain,
% 3.80/0.99      ( sK2 = k1_xboole_0
% 3.80/0.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.80/0.99      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_2879]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3,plain,
% 3.80/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4009,plain,
% 3.80/0.99      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4010,plain,
% 3.80/0.99      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_4009]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7317,plain,
% 3.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7287,c_2052]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7324,plain,
% 3.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7317,c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9742,plain,
% 3.80/0.99      ( sK2 = k1_xboole_0 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_7329,c_2852,c_2880,c_4010,c_7324]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7297,plain,
% 3.80/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7287,c_5989]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9746,plain,
% 3.80/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_9742,c_7297]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5196,plain,
% 3.80/0.99      ( k2_zfmisc_1(sK0,sK0) = sK1
% 3.80/0.99      | r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3125,c_2071]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7302,plain,
% 3.80/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK1
% 3.80/0.99      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7287,c_5196]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7330,plain,
% 3.80/0.99      ( sK1 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7302,c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3620,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
% 3.80/0.99      | r1_tarski(sK1,k1_xboole_0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3621,plain,
% 3.80/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.80/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_3620]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2738,plain,
% 3.80/0.99      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3669,plain,
% 3.80/0.99      ( ~ r1_tarski(sK1,k1_xboole_0)
% 3.80/0.99      | ~ r1_tarski(k1_xboole_0,sK1)
% 3.80/0.99      | sK1 = k1_xboole_0 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_2738]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3670,plain,
% 3.80/0.99      ( sK1 = k1_xboole_0
% 3.80/0.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.80/0.99      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_3669]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5831,plain,
% 3.80/0.99      ( r1_tarski(k1_xboole_0,sK1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5832,plain,
% 3.80/0.99      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_5831]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7318,plain,
% 3.80/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7287,c_2048]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7323,plain,
% 3.80/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7318,c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10046,plain,
% 3.80/0.99      ( sK1 = k1_xboole_0 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_7330,c_3621,c_3670,c_5832,c_7323]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_22,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.80/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.80/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.80/0.99      | ~ v1_funct_1(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2060,plain,
% 3.80/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.80/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.80/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.80/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6969,plain,
% 3.80/0.99      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.80/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.80/0.99      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.80/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.80/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_5986,c_2060]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10913,plain,
% 3.80/0.99      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_6969,c_41,c_42,c_43,c_44]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10917,plain,
% 3.80/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.80/0.99      inference(light_normalisation,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_10913,c_7287,c_10046]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10918,plain,
% 3.80/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_10917,c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14,plain,
% 3.80/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | X3 = X2 ),
% 3.80/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2063,plain,
% 3.80/0.99      ( X0 = X1
% 3.80/0.99      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5210,plain,
% 3.80/0.99      ( sK2 = X0
% 3.80/0.99      | r2_relset_1(sK0,sK0,sK2,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2052,c_2063]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7307,plain,
% 3.80/0.99      ( sK2 = X0
% 3.80/0.99      | r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7287,c_5210]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7327,plain,
% 3.80/0.99      ( sK2 = X0
% 3.80/0.99      | r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7307,c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11007,plain,
% 3.80/0.99      ( sK2 = X0
% 3.80/0.99      | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_7327,c_9742]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11008,plain,
% 3.80/0.99      ( k1_xboole_0 = X0
% 3.80/0.99      | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_11007,c_9742]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4030,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 3.80/0.99      | r1_tarski(X0,k1_xboole_0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4031,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.80/0.99      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_4030]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2069,plain,
% 3.80/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5193,plain,
% 3.80/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2069,c_2071]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11012,plain,
% 3.80/0.99      ( k1_xboole_0 = X0
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_11008,c_4031,c_5193]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11022,plain,
% 3.80/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_10918,c_11012]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11978,plain,
% 3.80/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.80/0.99      inference(light_normalisation,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_9746,c_10046,c_11022]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2064,plain,
% 3.80/0.99      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3484,plain,
% 3.80/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2052,c_2064]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7313,plain,
% 3.80/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7287,c_3484]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9747,plain,
% 3.80/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_9742,c_7313]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(contradiction,plain,
% 3.80/0.99      ( $false ),
% 3.80/0.99      inference(minisat,[status(thm)],[c_11978,c_9747]) ).
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  ------                               Statistics
% 3.80/0.99  
% 3.80/0.99  ------ General
% 3.80/0.99  
% 3.80/0.99  abstr_ref_over_cycles:                  0
% 3.80/0.99  abstr_ref_under_cycles:                 0
% 3.80/0.99  gc_basic_clause_elim:                   0
% 3.80/0.99  forced_gc_time:                         0
% 3.80/0.99  parsing_time:                           0.012
% 3.80/0.99  unif_index_cands_time:                  0.
% 3.80/0.99  unif_index_add_time:                    0.
% 3.80/0.99  orderings_time:                         0.
% 3.80/0.99  out_proof_time:                         0.013
% 3.80/0.99  total_time:                             0.438
% 3.80/0.99  num_of_symbols:                         53
% 3.80/0.99  num_of_terms:                           20276
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing
% 3.80/0.99  
% 3.80/0.99  num_of_splits:                          0
% 3.80/0.99  num_of_split_atoms:                     0
% 3.80/0.99  num_of_reused_defs:                     0
% 3.80/0.99  num_eq_ax_congr_red:                    21
% 3.80/0.99  num_of_sem_filtered_clauses:            3
% 3.80/0.99  num_of_subtypes:                        0
% 3.80/0.99  monotx_restored_types:                  0
% 3.80/0.99  sat_num_of_epr_types:                   0
% 3.80/0.99  sat_num_of_non_cyclic_types:            0
% 3.80/0.99  sat_guarded_non_collapsed_types:        0
% 3.80/0.99  num_pure_diseq_elim:                    0
% 3.80/0.99  simp_replaced_by:                       0
% 3.80/0.99  res_preprocessed:                       170
% 3.80/0.99  prep_upred:                             0
% 3.80/0.99  prep_unflattend:                        46
% 3.80/0.99  smt_new_axioms:                         0
% 3.80/0.99  pred_elim_cands:                        7
% 3.80/0.99  pred_elim:                              2
% 3.80/0.99  pred_elim_cl:                           3
% 3.80/0.99  pred_elim_cycles:                       5
% 3.80/0.99  merged_defs:                            8
% 3.80/0.99  merged_defs_ncl:                        0
% 3.80/0.99  bin_hyper_res:                          9
% 3.80/0.99  prep_cycles:                            4
% 3.80/0.99  pred_elim_time:                         0.009
% 3.80/0.99  splitting_time:                         0.
% 3.80/0.99  sem_filter_time:                        0.
% 3.80/0.99  monotx_time:                            0.
% 3.80/0.99  subtype_inf_time:                       0.
% 3.80/0.99  
% 3.80/0.99  ------ Problem properties
% 3.80/0.99  
% 3.80/0.99  clauses:                                34
% 3.80/0.99  conjectures:                            10
% 3.80/0.99  epr:                                    10
% 3.80/0.99  horn:                                   32
% 3.80/0.99  ground:                                 10
% 3.80/0.99  unary:                                  16
% 3.80/0.99  binary:                                 4
% 3.80/0.99  lits:                                   97
% 3.80/0.99  lits_eq:                                15
% 3.80/0.99  fd_pure:                                0
% 3.80/0.99  fd_pseudo:                              0
% 3.80/0.99  fd_cond:                                1
% 3.80/0.99  fd_pseudo_cond:                         5
% 3.80/0.99  ac_symbols:                             0
% 3.80/0.99  
% 3.80/0.99  ------ Propositional Solver
% 3.80/0.99  
% 3.80/0.99  prop_solver_calls:                      30
% 3.80/0.99  prop_fast_solver_calls:                 1682
% 3.80/0.99  smt_solver_calls:                       0
% 3.80/0.99  smt_fast_solver_calls:                  0
% 3.80/0.99  prop_num_of_clauses:                    5067
% 3.80/0.99  prop_preprocess_simplified:             11185
% 3.80/0.99  prop_fo_subsumed:                       74
% 3.80/0.99  prop_solver_time:                       0.
% 3.80/0.99  smt_solver_time:                        0.
% 3.80/0.99  smt_fast_solver_time:                   0.
% 3.80/0.99  prop_fast_solver_time:                  0.
% 3.80/0.99  prop_unsat_core_time:                   0.
% 3.80/0.99  
% 3.80/0.99  ------ QBF
% 3.80/0.99  
% 3.80/0.99  qbf_q_res:                              0
% 3.80/0.99  qbf_num_tautologies:                    0
% 3.80/0.99  qbf_prep_cycles:                        0
% 3.80/0.99  
% 3.80/0.99  ------ BMC1
% 3.80/0.99  
% 3.80/0.99  bmc1_current_bound:                     -1
% 3.80/0.99  bmc1_last_solved_bound:                 -1
% 3.80/0.99  bmc1_unsat_core_size:                   -1
% 3.80/0.99  bmc1_unsat_core_parents_size:           -1
% 3.80/0.99  bmc1_merge_next_fun:                    0
% 3.80/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.80/0.99  
% 3.80/0.99  ------ Instantiation
% 3.80/0.99  
% 3.80/0.99  inst_num_of_clauses:                    1279
% 3.80/0.99  inst_num_in_passive:                    314
% 3.80/0.99  inst_num_in_active:                     615
% 3.80/0.99  inst_num_in_unprocessed:                350
% 3.80/0.99  inst_num_of_loops:                      690
% 3.80/0.99  inst_num_of_learning_restarts:          0
% 3.80/0.99  inst_num_moves_active_passive:          71
% 3.80/0.99  inst_lit_activity:                      0
% 3.80/0.99  inst_lit_activity_moves:                0
% 3.80/0.99  inst_num_tautologies:                   0
% 3.80/0.99  inst_num_prop_implied:                  0
% 3.80/0.99  inst_num_existing_simplified:           0
% 3.80/0.99  inst_num_eq_res_simplified:             0
% 3.80/0.99  inst_num_child_elim:                    0
% 3.80/0.99  inst_num_of_dismatching_blockings:      462
% 3.80/0.99  inst_num_of_non_proper_insts:           1798
% 3.80/0.99  inst_num_of_duplicates:                 0
% 3.80/0.99  inst_inst_num_from_inst_to_res:         0
% 3.80/0.99  inst_dismatching_checking_time:         0.
% 3.80/0.99  
% 3.80/0.99  ------ Resolution
% 3.80/0.99  
% 3.80/0.99  res_num_of_clauses:                     0
% 3.80/0.99  res_num_in_passive:                     0
% 3.80/0.99  res_num_in_active:                      0
% 3.80/0.99  res_num_of_loops:                       174
% 3.80/0.99  res_forward_subset_subsumed:            233
% 3.80/0.99  res_backward_subset_subsumed:           0
% 3.80/0.99  res_forward_subsumed:                   0
% 3.80/0.99  res_backward_subsumed:                  0
% 3.80/0.99  res_forward_subsumption_resolution:     4
% 3.80/0.99  res_backward_subsumption_resolution:    0
% 3.80/0.99  res_clause_to_clause_subsumption:       574
% 3.80/0.99  res_orphan_elimination:                 0
% 3.80/0.99  res_tautology_del:                      80
% 3.80/0.99  res_num_eq_res_simplified:              0
% 3.80/0.99  res_num_sel_changes:                    0
% 3.80/0.99  res_moves_from_active_to_pass:          0
% 3.80/0.99  
% 3.80/0.99  ------ Superposition
% 3.80/0.99  
% 3.80/0.99  sup_time_total:                         0.
% 3.80/0.99  sup_time_generating:                    0.
% 3.80/0.99  sup_time_sim_full:                      0.
% 3.80/0.99  sup_time_sim_immed:                     0.
% 3.80/0.99  
% 3.80/0.99  sup_num_of_clauses:                     170
% 3.80/0.99  sup_num_in_active:                      68
% 3.80/0.99  sup_num_in_passive:                     102
% 3.80/0.99  sup_num_of_loops:                       137
% 3.80/0.99  sup_fw_superposition:                   144
% 3.80/0.99  sup_bw_superposition:                   122
% 3.80/0.99  sup_immediate_simplified:               61
% 3.80/0.99  sup_given_eliminated:                   0
% 3.80/0.99  comparisons_done:                       0
% 3.80/0.99  comparisons_avoided:                    3
% 3.80/0.99  
% 3.80/0.99  ------ Simplifications
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  sim_fw_subset_subsumed:                 16
% 3.80/0.99  sim_bw_subset_subsumed:                 9
% 3.80/0.99  sim_fw_subsumed:                        7
% 3.80/0.99  sim_bw_subsumed:                        1
% 3.80/0.99  sim_fw_subsumption_res:                 0
% 3.80/0.99  sim_bw_subsumption_res:                 0
% 3.80/0.99  sim_tautology_del:                      11
% 3.80/0.99  sim_eq_tautology_del:                   26
% 3.80/0.99  sim_eq_res_simp:                        0
% 3.80/0.99  sim_fw_demodulated:                     40
% 3.80/0.99  sim_bw_demodulated:                     68
% 3.80/0.99  sim_light_normalised:                   37
% 3.80/0.99  sim_joinable_taut:                      0
% 3.80/0.99  sim_joinable_simp:                      0
% 3.80/0.99  sim_ac_normalised:                      0
% 3.80/0.99  sim_smt_subsumption:                    0
% 3.80/0.99  
%------------------------------------------------------------------------------
